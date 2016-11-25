module Solve (
  findRun, showRun
) where
import System.Clock

import Data.Ratio
import Data.Maybe
import Data.List (sortOn, intercalate, transpose)
import qualified Data.Map as M
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Text as T

import Z3.Monad
import Control.Monad
import Control.Monad.IO.Class (liftIO)

import qualified Text.PrettyPrint.Boxes as B

import Types

-- make finite ID domain
mkEnum :: Show a => String -> String -> [a] -> Z3 Sort
mkEnum sname spref is = join $ mkDatatype <$> mkStringSymbol sname <*> forM is makeconst
  where makeconst i = join $ mkConstructor <$> mkStringSymbol (spref++(show i)) <*> mkStringSymbol (spref++(show i)) <*> pure []

-- custom enumeration type for node ids (NOTE: seems slower than using ints? benchmark more!)
-- getNidSort is = do
  -- node <- mkEnum "NodeId" "n" is
  -- nodeConst <- V.fromList <$> getDatatypeSortConstructors node
  -- let mkFreshNodeVar = flip mkFreshVar node
  -- nid <- mapM (flip mkApp []) nodeConst
  -- -- evaluate resulting id back to an integer
  -- let evalNid m sym = do
  --       ret <- modelEval m sym True
  --       case ret of
  --         Nothing -> return Nothing
  --         Just v -> astToString v >>= return . Just . read . tail
  -- return (mkFreshNodeVar, evalNid, nid)

-- use ints as node ids
getNidSort is = do
  nid <- V.fromList <$> mapM (mkInteger . fromIntegral) is
  return (mkFreshIntVar, evalInt, nid)

-- given valid edges and two variable syms, enumerate all valid assignments
isValidEdge :: [(Int,Int)] -> Vector AST -> (AST,AST) -> Z3 AST
isValidEdge validEdges constNid (fromVar,toVar) = mkOr =<< forM validEdges (\(i,j) ->
  mkAnd =<< sequence [mkEq fromVar (constNid V.! i), mkEq toVar (constNid V.! j)])

-- helper: generate a variable name from prefix and a list of indices
varname pref ind = intercalate "_" $ pref:(map show ind)

-- helper: a /= b
mkNeq a b = mkNot =<< mkEq a b

-- sugar, expand quantifiers over variables
mkForallI [] _ = mkTrue
mkForallI ind f = mkAnd =<< forM ind f
mkExistsI [] _ = mkFalse
mkExistsI ind f = mkOr =<< forM ind f

-- helper: allocate a vector of variable symbols with given prefix, indexed over is
mkVarVec mkf name is = V.fromList <$> forM is (\i -> mkf $ varname name [i])
-- helper: allocate a matrix of variable symbols with given prefix, indexed over is and js
mkVarMat mkf name is js = V.fromList <$> forM is (\i -> mkVarVec mkf (varname name [i]) js)

ifT False _ = mkTrue
ifT True f = f
ifF False _ = mkFalse
ifF True f = f

-- vector of run in a path schema
data PosVars = PosVars {
                 posId :: Integer
               , posLType :: LoopType
               , posLCount :: Integer
               , posLStart :: Integer
               , posLCtr :: Integer
               , posLLen :: Integer
               , posLbls :: Vector Bool
               , posUCtrs :: Vector Integer
               , posUpd :: Vector Bool
               , posGrd :: Vector (Bool,Bool)
               } deriving (Show, Eq)
type Run = [PosVars]

-- loop type enum, represented in formulae as 2 booleans per value
data LoopType = Out | Start | End | In deriving (Show,Eq)
isLtype :: LoopType -> (AST,AST) -> Z3 AST
isLtype lt (b1,b2) | lt==Out = comb mkFalse mkFalse
                   | lt==In  = comb mkTrue  mkTrue
                   | lt==Start = comb mkTrue  mkFalse
                   | lt==End   = comb mkFalse mkTrue
                   | otherwise = mkFalse --impossible...
  where comb v1 v2 = mkAnd =<< sequence [join $ mkEq b1 <$> v1, join $ mkEq b2 <$> v2]

toLtype (False,False) = Out
toLtype (True,True) = In
toLtype (True,False) = Start
toLtype (False,True) = End

-- is one of given loop types
isOneOfLT ls p = mkOr =<< mapM (flip isLtype p) ls

-- input: graph structure, ltl formula, path schema length
-- output: valid run if possible
findRun :: Graph Char -> Formula Char -> Int -> Bool -> IO (Maybe Run)
findRun g f n v = evalZ3 $ do
  when (n<=0) $ error "path schema must have positive size!"


  log "Enumerating simple cycle lengths..."
  start0 <- currTime
  let lens = calcValidCycleLengths g     -- valid loop lens (use johnson on g!)
  end0 <- currTime
  log $ "Found lengths " ++ show lens ++ " in: " ++ showTime start0 end0

  log "Building constraints..."
  start1 <- currTime

  -- create a few constant elements
  _T <- mkTrue
  _F <- mkFalse
  _N1 <- mkInteger (-1)
  _0 <- mkInteger 0
  _1 <- mkInteger 1
  _n <- mkInteger $ fromIntegral n  -- constant n = number of states in path schema
  let indices = [0..n-1]            -- helper to quantify over indices of variables
  let ge = edges g                  -- get directed edges of graph

  (mkFreshNodeVar, evalNid, nid) <- getNidSort (nodes g)

  -- variables to store node ids of path schema
  ids <- mkVarVec mkFreshNodeVar "nid" indices

  -- variables to indicate loop structure: both 0 <-> out, both 1 <-> in, lt1=1,lt2=0 <-> start, lt2=1,lt1=0 <-> end
  -- no self loops, only "simple" loops (no internal id equal to left or right border)
  lt1 <- mkVarVec mkFreshBoolVar "lt1" indices
  lt2 <- mkVarVec mkFreshBoolVar "lt2" indices
  let lt = V.zip lt1 lt2
  -- variables to act as loop counters for the run, decorating nodes that are part of aloop
  lcnt <- mkVarVec mkFreshIntVar "lct" indices
  -- loop start propagation
  lst  <- mkVarVec mkFreshNodeVar "lst" indices
  -- loop length counter
  lctr <- mkVarVec mkFreshIntVar "lctr" indices
  -- loop length indicator (derived from lctr)
  llen <- mkVarVec mkFreshIntVar "llen" indices

  -- get all subformulas with assigned id
  let sfs = enumerateSubformulas f
  -- variable sets to store labels (list of lists, each node has vars with flags of all subf)
  labels <- mkVarMat mkFreshBoolVar "lbl" indices [1..length sfs]

  -- to correctly label the rational untils, we need to employ the counters
  -- each state of the path has an own counter per ratio-U subformula which is firstly updated there
  -- there are 2 guards per counter: <0, >=0. both can be on the incoming edge of a node
  let untils = getEvilUntils sfs
  let numUntils = length untils
  -- per state and U-formula: one counter flag, two incoming guard flags
  -- dimensions: i=current schema state, j=number U-formula counter, guards: 1: >=0, 2: <0
  uctrs   <- mkVarMat mkFreshIntVar  "uctr" indices [1..numUntils]
  updates <- mkVarMat mkFreshBoolVar "upd"  indices [1..numUntils]
  guards1 <- mkVarMat mkFreshBoolVar "grd1" indices [1..numUntils]
  guards2 <- mkVarMat mkFreshBoolVar "grd2" indices [1..numUntils]

  -------------------------------------------------------------------------------------------------------------------------------
  -- always start path at node 0...
  assert =<< mkEq (nid V.! 0) (ids V.! 0)
  -- ... and neighboring ids must have valid edge (non looping path is valid)
  assert =<< mkForallI [(i,j) | i<-init indices,let j=i+1] (\(i,j) -> isValidEdge ge nid ((ids V.! i),(ids V.! j)))

  -- path ends with ending of a loop (we consider only infinite paths!)
  assert =<< isLtype End (lt V.! (n-1))

  -- force loop count = 0 in last loop
  assert =<< mkEq (lcnt V.! (n-1)) _0

  -- we want the complete formula to be satisfied, i.e. total formula labeled at first node (the node with id 0)
  assert =<< mkEq (V.last $ labels V.! 0) _T

  -- all until phi freq. counters start at 0
  assert =<< mkForallI (M.toList untils) (\(_,j) -> mkEq ((uctrs V.! 0) V.! j) _0)

  -- helper: f shall hold with one of the valid loop lengths
  let withLoopLen i f = mkExistsI lens (\l -> mkAnd =<< sequence [join $ mkEq (llen V.! i) <$> (mkInteger $ fromIntegral l), f l])

  let at var i j = (var V.! i) V.! j -- helper: access 2-indexed variable
  let isInc n f g = join $ mkEq g <$> (mkAdd =<< sequence [mkInteger $ fromIntegral n, pure f]) -- helper: f + n = g
  let lbl = at labels
  assert =<< mkForallI indices (\i-> mkAnd =<< sequence [
      -- enforce looptype structure (Out | Start (In*) End)*(Start (In*) End)
      ifT (i>0 && i<n-1) $ mkAnd =<< sequence (map join [
                                                mkImplies <$> (isLtype Start (lt V.! i)) <*> (isOneOfLT [In,End]  (lt V.! (i+1)))
                                              , mkImplies <$> (isLtype Start (lt V.! i)) <*> (isLtype Out (lt V.! (i-1)))
                                              , mkImplies <$> (isLtype End   (lt V.! i)) <*> (isLtype Out (lt V.! (i+1)))
                                              , mkImplies <$> (isLtype End   (lt V.! i)) <*> (isOneOfLT [In,Start]  (lt V.! (i-1)))
                                              , mkImplies <$> (isLtype In   (lt V.! i)) <*> (isOneOfLT [In,End]    (lt V.! (i+1)))
                                              , mkImplies <$> (isLtype In   (lt V.! i)) <*> (isOneOfLT [In,Start]  (lt V.! (i-1)))
                                              , mkImplies <$> (isLtype Out  (lt V.! i)) <*> (isOneOfLT [Out,Start] (lt V.! (i+1)))
                                              , mkImplies <$> (isLtype Out  (lt V.! i)) <*> (isOneOfLT [Out,End]   (lt V.! (i-1)))
                                              ])

      -- loop count >= 0 in general
    , mkLe _0 (lcnt V.! i)
      -- loop count > 1 in all loops but last
    , ifT (i<n-1) $ join $ mkImplies <$> isLtype End (lt V.! i) <*> mkLt _1 (lcnt V.! i)
      -- loop count = 1 <-> outside of loop
    , join $ mkIff <$> isLtype Out (lt V.! i) <*> mkEq (lcnt V.! i) _1
      -- consistent loopcount in loops
    , ifT (i>0 && i<n-1) $ mkAnd =<< sequence [
        join $ mkImplies <$> isLtype Start (lt V.! i) <*> (mkEq (lcnt V.! i) (lcnt V.! (i+1)))
      , join $ mkImplies <$> isLtype End   (lt V.! i) <*> (mkEq (lcnt V.! i) (lcnt V.! (i-1)))
      , join $ mkImplies <$> isLtype In    (lt V.! i) <*> (mkAnd =<< sequence [ mkEq (lcnt V.! i) (lcnt V.! (i+1)), mkEq (lcnt V.! i) (lcnt V.! (i-1))])
      ]

      -- propagate start id
    , mkAnd =<< sequence [ join $ mkImplies <$> (isLtype Start (lt V.! i)) <*> (mkEq (lst V.! i) (ids V.! i)) --take loop start id at start from curr id
                         , join $ mkImplies <$> (isLtype Out (lt V.! i)) <*> (mkEq (lst V.! i) (nid V.! 0)) --outside loops start id is always node 0 (as dummy)
                         , ifT (i<n-1) $ join $ mkImplies <$> (isOneOfLT [Start,In] (lt V.! i)) <*> mkEq (lst V.! i) (lst V.! (i+1)) ] --propagate forward

    -- loop length counter outside of loops is zero
    , join $ mkImplies <$> isLtype Out (lt V.! i) <*> mkEq (lctr V.! i) _0
    -- loop length counter init at loop start
    , join $ mkImplies <$> isLtype Start (lt V.! i) <*> mkEq (lctr V.! i) _1
    -- loop length counter propagate
    , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> (isInc 1 (lctr V.! (i-1)) (lctr V.! i))

    -- loop length outside of loops is zero
    , join $ mkImplies <$> isLtype Out (lt V.! i) <*> mkEq (llen V.! i) _0
    -- loop length init at loop end
    , join $ mkImplies <$> isLtype End (lt V.! i) <*> mkEq (lctr V.! i) (llen V.! i)
    -- loop length counter propagate
    , ifT (i<n-1) $ join $ mkImplies <$> (isOneOfLT [Start,In] (lt V.! i)) <*> mkEq (llen V.! i) (llen V.! (i+1))

    -- valid backloop and also loop length (restrict to possible lengths of simple loops in orig. graph)
    , join $ mkImplies <$> isLtype End (lt V.! i) <*> (mkAnd =<< sequence [
          isValidEdge ge nid (ids V.! i, lst V.! i)
        , mkExistsI lens (\l -> join $ mkEq (llen V.! i) <$> (mkInteger $ fromIntegral l))
        ])

    -- enforce 2x unrolled left (same ids and labels, but outside of loop)
    , join $ mkImplies <$> (mkNot =<< isLtype Out (lt V.! i)) <*> (withLoopLen i (\l -> ifF (i-2*l>=0) (mkAnd =<< sequence
        [ isLtype Out (lt V.! (i-l))
        , isLtype Out (lt V.! (i-2*l))
        , mkEq (ids V.! i) (ids V.! (i-l))
        , mkEq (ids V.! i) (ids V.! (i-2*l))
        , mkForallI (M.toList sfs) (\(_,j) -> mkEq (lbl i j) (lbl (i-l) j))
        , mkForallI (M.toList sfs) (\(_,j) -> mkEq (lbl i j) (lbl (i-2*l) j))
        ])))

    -- enforce 1x unrolled right (unless last loop)
    , join $ mkImplies <$> (mkAnd =<< sequence [mkNot =<< isLtype Out (lt V.! i), mkNot =<< (mkEq (lcnt V.! i) _0)])
                       <*> (withLoopLen i (\l -> ifF (i+l<=n-1) (mkAnd =<< sequence
        [ isLtype Out (lt V.! (i+l))
        , mkEq (ids V.! i) (ids V.! (i+l))
        , mkForallI (M.toList sfs) (\(_,j) -> mkEq (lbl i j) (lbl (i+l) j))
        ])))

    -- enforce correct updates, corresponding counter states and interaction with guards for the evil untils
    , mkForallI (M.toList untils) (\((Until r f g), j) -> do
      let (phi, psi) = (fromJust $ M.lookup f sfs, fromJust $ M.lookup g sfs)
          (m, n) = (numerator r, denominator r)
          isMulAdd f n v g = join $ mkEq g <$> (mkAdd =<< sequence [mkMul =<< sequence [mkInteger $ fromIntegral n, pure v], pure f]) -- helper: f + n*v = g
      mkAnd =<< sequence [
          -- set corresponding updates. 0 = negative (-m) if phi does not hold, 1 = positive (n-m) if phi does hold
          mkIff (at updates i j) (at labels i phi)

          -- guard related constraints:
        , join $ mkImplies (at guards1 i j) <$> (mkLe _0 (at uctrs i j)) -- if guard >= 0 is set, counter must be >= 0 afterwards
        , join $ mkImplies (at guards2 i j) <$> (mkLt (at uctrs i j) _0) -- if guard < 0 is set, counter must be < 0 afterwards
        , join $ mkNot <$> (mkAnd [at guards1 i j, at guards2 i j])      -- both guards for same counter can not be set
          -- no guards in loops (TODO: is this correct?)
        , join $ mkImplies <$> (isOneOfLT [Start,In,End] (lt V.! i)) <*> (mkNot =<< mkOr [at guards1 i j, at guards2 i j])

          -- counter value at i>0 = old value at i-1 + update on edge from i-i
        , ifT (i>0) $ mkAnd =<< sequence [
            -- positive update (proportional to number of node visits, semantically invalid inside loops, just used as accumulator there)
            join $ mkImplies           (at updates (i-1) j) <$> isMulAdd (at uctrs (i-1) j) (n-m) (lcnt V.! (i-1)) (at uctrs i j)
            -- negative update, same idea
          , join $ mkImplies <$> mkNot (at updates (i-1) j) <*> isMulAdd (at uctrs (i-1) j) (-m)  (lcnt V.! (i-1)) (at uctrs i j)
          ]
        ]
      )

    -- enforce correct labelling
    , mkForallI (M.toList sfs) (\(sf,j) -> do --for all the subformulae...
      let subf = subformulas sfs sf
          lbl_ij_equiv_to t = join $ mkIff <$> pure (lbl i j) <*> t
      case sf of
          -- an atomic proposition holds if the chosen node contains the proposition
          Prop p -> lbl_ij_equiv_to $ mkOr =<< forM (filter (flip (hasProp g) p) $ nodes g) (\node -> mkEq (ids V.! i) (nid V.! node))
          -- obvious
          Tru -> lbl_ij_equiv_to mkTrue
          Fls -> lbl_ij_equiv_to mkFalse
          And _ _ -> lbl_ij_equiv_to $ mkAnd (fmap (lbl i) subf)
          Or _ _ ->  lbl_ij_equiv_to $ mkOr (fmap (lbl i) subf)
          Not _ ->   lbl_ij_equiv_to $ mkNot (head $ fmap (lbl i) subf)
          -- for next the subf. must hold on all successors -> next node and backloop if any
          Next _ ->  lbl_ij_equiv_to $ mkAnd =<< sequence
            [ ifT (i<n-1) $ mkAnd (fmap (lbl (i+1)) subf) -- subf. must hold in succ. node
            -- backloop edge -> must check that subformula holds in target
            , join $ mkImplies <$> (isLtype End (lt V.! i)) <*> mkExistsI lens (\l -> ifF (i-l+1>=0) $ mkAnd (fmap (lbl (i-l+1)) subf))
            ]
          -- need to consider subformulas in until separately.. get their subformula index and set constraints
          Until 1 f g -> do -- this is the regular until
            let (phi, psi) = (fromJust $ M.lookup f sfs, fromJust $ M.lookup g sfs)
                -- psi holds at some time in the future and for all positions until then phi holds.
            lbl_ij_equiv_to $ mkAnd =<< sequence [
                join $ mkImplies <$> (isLtype Out (lt V.! i)) <*> (mkOr =<< sequence [
                  -- psi holds -> until holds here
                  pure $ lbl i psi
                  -- phi holds -> until works here if it holds in next position too, which must be outside loop
                , ifF (i<n-1) $ mkAnd =<< sequence [pure $ lbl i phi, isLtype Out (lt V.! (i+1)), pure $ lbl (i+1) j]
                ])
              -- we are inside loop -> check the unrolling value and copy it
              , join $ mkImplies <$> (mkNot =<< isLtype Out (lt V.! i)) <*> (withLoopLen i $ \l -> ifF (i-2*l>=0) $ pure $ lbl (i-2*l) j)
              ]

          --TODO: consistency of evil until
          Until _ _ _ -> mkTrue
      )
    ])

  -------------------------------------------------------------------------------------------------------------------------------
  -- extract satisfying model from Z3 if possible
  end1 <- currTime
  log $ "Build constraints: " ++ showTime start1 end1
  st <- if v then T.pack <$> solverToString else pure T.empty --slow, do only in verbose mode for infos
  let countInts = length $ T.breakOnAll (T.pack "Int") st
  let countBools = length $ T.breakOnAll (T.pack "Bool") st
  log $ "Formula size: " ++ show (T.length st) ++ " Ints: " ++ show countInts ++ " Bools: " ++ show countBools

  start2 <- currTime
  log "Searching..."
  result <- fmap snd $ withModel $ \m -> do
    let getVec :: EvalAst Z3 a -> Vector AST -> Z3 (Vector a)
        getVec evalfunc vec = fromMaybe V.empty <$> mapEval evalfunc m vec

        getCtrMat :: EvalAst Z3 a -> Vector (Vector AST) -> Z3 (Vector (Vector a))
        getCtrMat f mat = fromMaybe V.empty . V.sequence <$> V.forM mat (\row -> mapEval f m row)

    idvals <- getVec evalNid ids
    ltvals <- fmap toLtype <$> (V.zip <$> getVec evalBool lt1 <*> getVec evalBool lt2)
    lcntvals <- getVec evalInt lcnt
    lstvals <- getVec evalNid lst
    lctrvals <- getVec evalInt lctr
    llenvals <- getVec evalInt llen

    ucvals <- getCtrMat evalInt  uctrs
    uvals <-  getCtrMat evalBool updates
    gvals <- fmap (uncurry V.zip) <$> (V.zip <$> getCtrMat evalBool guards1 <*> getCtrMat evalBool guards2)

    lblvals <- getCtrMat evalBool labels

    return $ V.toList $ V.generate (length indices) (\i ->
      PosVars {
        posId = idvals V.! i
      , posLType = ltvals V.! i
      , posLCount = lcntvals V.! i
      , posLStart = lstvals V.! i
      , posLCtr = lctrvals V.! i
      , posLLen = llenvals V.! i
      , posLbls = lblvals V.! i
      , posUCtrs = ucvals V.! i
      , posUpd = uvals V.! i
      , posGrd = gvals V.! i
      })
  end2 <- currTime
  log $ "Finished after: "++showTime start2 end2
  return result

  where currTime = liftIO $ getTime Monotonic
        showTime a b = show ((/1000000) . fromIntegral . abs . toNanoSecs $ b-a)++" ms" -- print time diff. of a and b
        log = when v . liftIO . putStrLn

-- generate pretty-printed run string for output
showRun :: Formula Char -> Run -> String
showRun f r = B.render $ B.hsep 4 B.left [B.hsep 1 B.left [ids,lts,lcs,lst,lln], tri, lbl]
  where mkCol name cells = (B.text name) B.// (B.vcat B.top cells)
        addLT f p = (f p, posLType p)
        showIfLoop (_,Out) = ""
        showIfLoop (a,_) = show a
        sfs = enumerateSubformulas f

        ids = mkCol "ID" $ map (B.text . show . posId) r
        lts = mkCol "LT" $ map (B.text . lsym . posLType) r
        lcs = mkCol "LC" $ map (B.text . lcount . posLCount) r
        lst = mkCol "LS" $ map (B.text . showIfLoop . addLT posLStart) r
        lln = mkCol "LL" $ map (B.text . showIfLoop . addLT posLLen) r

        tri = B.hsep 2 B.left $ map (B.vcat B.top) $ transpose $ iuts:(map (map (B.text . c2str) . (\p -> V.toList $ V.zip3 (posGrd p) (posUCtrs p) (posUpd p))) r)
        iuts = map (B.text . show . fst) $ sortOn snd $ M.toList $ getEvilUntils sfs --to label columns with until formulae

        lbl = mkCol "Labels" $ map (B.text . lbls . posLbls) r
        lblids = map fst . filter ((==True).snd) . zip [0..] . V.toList
        lbls = intercalate ", " . map show . catMaybes . map (flip M.lookup isfs) . lblids
        isfs = M.fromList $ map (\(a,b) -> (b,a)) $ M.toList sfs --to map indices back to subformulas

        -- this representation looks too noisy for big formulae:
        -- lbl = B.hsep 1 B.left $ map (B.vcat B.top) $ transpose $ lblhdr:(map ((B.text "" :) . map (B.text . (\(a,t) -> if t then show a else "")) . zip ssfs . V.toList . posLbls) r)
        -- ssfs = map fst $ sortOn snd $ M.toList sfs
        -- lblhdr = B.text "Labels:" : (ssfs *> pure (B.text ""))

        lsym Start = "<"
        lsym End = "-"
        lsym In = "|"
        lsym Out = " "
        lcount 1 = ""
        lcount n = show n
        -- pretty print counter triples (in-guard, counter value, out-update)
        c2str ((g,l),v,u) = (if g then "[≥0] " else if l then "[<0] " else "[  ] ") ++ show v ++ (if u then " (+)" else " (-)")
