module Solve (
  findRun, showRun
) where
import Prelude hiding (log)
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

import qualified Data.IntSet as IS
import Cycles (getCycleLens)
import Util (currTime, msTimeDiff)
import Types

-- make finite ID domain. TODO: is this the best way?
-- mkEnum :: Show a => String -> String -> [a] -> Z3 Sort
-- mkEnum sname spref is = join $ mkDatatype <$> mkStringSymbol sname <*> forM is makeconst
--   where makeconst i = join $ mkConstructor <$> mkStringSymbol (spref++(show i)) <*> mkStringSymbol (spref++(show i)) <*> pure []

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

-- TODO
-- implement witness condition on rows
-- per until/counter extra guard greedy lane
-- copy labelling from around
-- impose guard conditions for U

-- vector of run in a path schema
data PosVars = PosVars {
                 posId :: Integer
               , posLType :: LoopType
               , posLCount :: Integer
               , posLStart :: Integer
               , posLCtr :: Integer
               , posLLen :: Integer
               , posLDCtrs :: Vector Integer
               , posLDelta :: Vector Integer
               , posLbls :: Vector Bool
               , posUCtrs :: Vector Integer
               , posUpd :: Vector Bool
               , posGrd :: Vector (Bool,Bool,Integer)
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

-- input: graph structure, optional loop lengths, ltl formula, path schema length
-- output: valid run if possible
findRun :: Graph Char -> [Int] -> Formula Char -> Int -> Bool -> IO (Maybe Run)
findRun gr ml f n verbose = evalZ3 $ do
  when (n<=0) $ error "path schema must have positive size!"

  lens <- case ml of
    [] -> do
      log "Enumerating simple cycle lengths..."
      start0 <- currTime
      -- calculate valid loop lens with Johnsons algorithm in (n+e)(c+1)
      -- selfloops must be unrolled to loops of size 2 -> we must always allow 2
      -- apart of self-loops, all guessed loops are simple cycles in graph
      let lens = IS.elems $ IS.insert 2 $ getCycleLens $ kripke2fgl gr
      end0 <- currTime
      log $ "Found lengths " ++ show lens ++ " in: " ++ showTime start0 end0
      return lens
    -- if the provided lengths are incomplete, probably a solution will not be found!
    -- if a superset is provided, the formula will be bigger than neccessary,
    -- but may be a good idea for small, but REALLY dense graphs (provide [1..n])
    ls -> log ("Using provided simple cycle lengths: "++show ls) >> return (2:ls)

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
  let ge = edges gr                 -- get directed edges of graph

  (mkFreshNodeVar, evalNid, nid) <- getNidSort (nodes gr)

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
  let uindices = [0..numUntils-1]
  -- per state and U-formula:
  -- dimensions: i=current schema state, j=number U-formula counter
  -- intermediate counter values
  uctrs    <- mkVarMat mkFreshIntVar  "uctr"  indices uindices
  -- update annotation on outgoing edge
  updates  <- mkVarMat mkFreshBoolVar "upd"   indices uindices
  -- guard for cj >= X, guard for cj < X flags, and X value
  guardsGE <- mkVarMat mkFreshBoolVar "grdf"  indices uindices
  guardsLT <- mkVarMat mkFreshBoolVar "grdt"  indices uindices
  guardsX  <- mkVarMat mkFreshIntVar  "grdx"  indices uindices
  -- loop delta (effect of one loop repetition) for each counter
  ldctrs   <- mkVarMat mkFreshIntVar  "ldctr" indices uindices
  ldeltas  <- mkVarMat mkFreshIntVar  "ldlt"  indices uindices

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
  let withLoopLen i prop = mkExistsI lens (\l -> mkAnd =<< sequence [join $ mkEq (llen V.! i) <$> (mkInteger $ fromIntegral l), prop l])

  let at var i j = (var V.! i) V.! j -- helper: access 2-indexed variable
  let isInc c a b = join $ mkEq b <$> (mkAdd =<< sequence [mkInteger $ fromIntegral c, pure a]) -- helper: a + c = b
  let lbl = at labels
  let allEq i i2 js mat = mkForallI js (\j -> mkEq (at mat i j) (at mat i2 j))
  assert =<< mkForallI indices (\i-> mkAnd =<< sequence [
      -- enforce looptype structure (Out | Start (In*) End)*(Start (In*) End)
      ifT (i>0 && i<n-1) $ mkAnd =<< sequence (map join [
                                                mkImplies <$> (isLtype Start (lt V.! i)) <*> (isOneOfLT [In,End]  (lt V.! (i+1)))
                                              , mkImplies <$> (isLtype Start (lt V.! i)) <*> (isLtype Out (lt V.! (i-1)))
                                              , mkImplies <$> (isLtype End   (lt V.! i)) <*> (isLtype Out (lt V.! (i+1)))
                                              , mkImplies <$> (isLtype End   (lt V.! i)) <*> (isOneOfLT [In,Start]  (lt V.! (i-1)))
                                              , mkImplies <$> (isLtype In    (lt V.! i)) <*> (isOneOfLT [In,End]    (lt V.! (i+1)))
                                              , mkImplies <$> (isLtype In    (lt V.! i)) <*> (isOneOfLT [In,Start]  (lt V.! (i-1)))
                                              , mkImplies <$> (isLtype Out   (lt V.! i)) <*> (isOneOfLT [Out,Start] (lt V.! (i+1)))
                                              , mkImplies <$> (isLtype Out   (lt V.! i)) <*> (isOneOfLT [Out,End]   (lt V.! (i-1)))
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
    , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> (isInc (1::Integer) (lctr V.! (i-1)) (lctr V.! i))

    -- loop length outside of loops is zero
    , join $ mkImplies <$> isLtype Out (lt V.! i) <*> mkEq (llen V.! i) _0
    -- loop length init at loop end
    , join $ mkImplies <$> isLtype End (lt V.! i) <*> mkEq (lctr V.! i) (llen V.! i)
    -- loop length counter propagate
    , ifT (i<n-1) $ join $ mkImplies <$> (isOneOfLT [Start,In] (lt V.! i)) <*> mkEq (llen V.! i) (llen V.! (i+1))

    -- valid backloop and also loop length (restrict to possible lengths of simple loops in orig. graph)
    , join $ mkImplies <$> isLtype End (lt V.! i) <*> (mkAnd =<< sequence [
          isValidEdge ge nid (ids V.! i, lst V.! i) -- valid backloop
        , withLoopLen i $ const mkTrue              -- valid loop length
        ])

    -- enforce 2x unrolled left (same ids, labels, guards and updates, but outside of loop)
    , join $ mkImplies <$> (mkNot =<< isLtype Out (lt V.! i)) <*> (withLoopLen i (\l -> ifF (i-2*l>=0) (mkAnd =<< sequence
        [ isLtype Out (lt V.! (i-l))
        , isLtype Out (lt V.! (i-2*l))
        , mkEq (ids V.! i) (ids V.! (i-l))
        , mkEq (ids V.! i) (ids V.! (i-2*l))
        , allEq i (i-l)   (snd <$> M.toList sfs) labels
        , allEq i (i-2*l) (snd <$> M.toList sfs) labels
        , mkAnd =<< forM [updates, guardsGE, guardsLT, guardsX] (\mat ->
          mkAnd =<< sequence [ allEq i (i-l) uindices mat, allEq i (i-2*l) uindices mat ] )
        ])))

    -- enforce 1x unrolled right (unless last loop)
    , join $ mkImplies <$> (mkAnd =<< sequence [mkNot =<< isLtype Out (lt V.! i), mkNot =<< (mkEq (lcnt V.! i) _0)])
                       <*> (withLoopLen i (\l -> ifF (i+l<=n-1) (mkAnd =<< sequence
        [ isLtype Out (lt V.! (i+l))
        , mkEq (ids V.! i) (ids V.! (i+l))
        , mkForallI (M.toList sfs) (\(_,j) -> mkEq (lbl i j) (lbl (i+l) j))
        , mkAnd =<< forM [updates, guardsGE, guardsLT, guardsX] (allEq i (i+l) uindices)
        ])))

    -- enforce correct updates, corresponding counter states and interaction with guards for the evil untils
    , mkForallI (M.toList untils) (\((Until r a _), j) -> do
      let (phi, x, y) = (fromJust $ M.lookup a sfs, numerator r, denominator r)
          -- helper: p + c*v = q
          isMulAdd p c v q = join $ mkEq q <$> (mkAdd =<< sequence [mkMul =<< sequence [mkInteger $ fromIntegral c, pure v], pure p])
          withUpdateAt k prop = mkAnd =<< sequence [
              join $ mkImplies           (at updates k j) <$> prop (y-x)
            , join $ mkImplies <$> mkNot (at updates k j) <*> prop (-x)
            ]
      mkAnd =<< sequence [
          -- set corresponding updates. 0 = negative (-m) if phi does not hold, 1 = positive (n-m) if phi does hold
          -- the updates-lane is technically not necessary, but very convenient to take phi out of the considerations
          mkIff (at updates i j) (at labels i phi)

          -- guard related constraints:
        , join $ mkNot <$> (mkAnd [at guardsGE i j, at guardsLT i j])                   -- both guards for same counter can not be set
        , join $ mkImplies (at guardsGE i j) <$> (mkGe (at uctrs i j) (at guardsX i j)) -- if guard >= X is set, counter must be >= X afterwards
        , join $ mkImplies (at guardsLT i j) <$> (mkLt (at uctrs i j) (at guardsX i j)) -- if guard < X is set, counter must be < X afterwards
          -- no guards in loops (TODO: look in unrolling)
        , join $ mkImplies <$> (isOneOfLT [Start,In,End] (lt V.! i)) <*> (mkNot =<< mkOr [at guardsGE i j, at guardsLT i j])

          -- counter value at i>0 = old value at i-1 + update on edge from i-1 times the number of visits of i-1
          -- (proportional to number of node visits, semantically invalid inside loops, just used as accumulator there)
          -- notice: counter value in last loop does not change (lcnt==0!) but it does not matter, see at loop delta to decide whether its a good loop
        , ifT (i>0) $ withUpdateAt (i-1) $ \u -> isMulAdd (at uctrs (i-1) j) u (lcnt V.! (i-1)) (at uctrs i j)

          -- accumulate loop deltas as sum of the update effects
        , join $ mkImplies <$> isLtype Out   (lt V.! i) <*> mkEq (at ldctrs i j) _0
        , join $ mkImplies <$> isLtype Start (lt V.! i) <*> withUpdateAt i (\u -> join $ mkEq (at ldctrs i j) <$> (mkInteger $ fromIntegral u))
        , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> withUpdateAt i (\u -> isInc u (at ldctrs (i-1) j) (at ldctrs i j))
        --   -- propagate loop delta back along loop
        , join $ mkImplies <$> isLtype Out (lt V.! i) <*> mkEq (at ldeltas i j) _0
        , join $ mkImplies <$> isLtype End (lt V.! i) <*> mkEq (at ldeltas i j) (at ldctrs i j)
        , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> mkEq (at ldeltas i j) (at ldeltas (i-1) j)
        ]
      )

    -- enforce correct labelling
    , mkForallI (M.toList sfs) (\(sf,j) -> do --for all the subformulae...
      let subf = subformulas sfs sf
          lbl_ij_equiv_to t = join $ mkIff <$> pure (lbl i j) <*> t
      case sf of
          -- an atomic proposition holds if the chosen node contains the proposition
          Prop p -> lbl_ij_equiv_to $ mkExistsI (filter (flip (hasProp gr) p) $ nodes gr) (\node -> mkEq (ids V.! i) (nid V.! node))
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
            , join $ mkImplies <$> (isLtype End (lt V.! i)) <*> withLoopLen i (\l -> ifF (i-l+1>=0) $ mkAnd (fmap (lbl (i-l+1)) subf))
            ]
          -- need to consider subformulas in until separately.. get their subformula index and set constraints
          Until 1 a b -> do -- this is the regular until
            let (phi, psi) = (fromJust $ M.lookup a sfs, fromJust $ M.lookup b sfs)
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
  st <- if verbose then T.pack <$> solverToString else pure T.empty --slow, do only in verbose mode for infos
  let countInts = length $ T.breakOnAll (T.pack "Int") st
  let countBools = length $ T.breakOnAll (T.pack "Bool") st
  log $ "Formula size: " ++ show (T.length st) ++ " Ints: " ++ show countInts ++ " Bools: " ++ show countBools

  start2 <- currTime
  log "Searching..."
  result <- fmap snd $ withModel $ \m -> do
    let getVec :: EvalAst Z3 a -> Vector AST -> Z3 (Vector a)
        getVec evalfunc vec = fromMaybe V.empty <$> mapEval evalfunc m vec

        getMat :: EvalAst Z3 a -> Vector (Vector AST) -> Z3 (Vector (Vector a))
        getMat fun mat = fromMaybe V.empty . V.sequence <$> V.forM mat (\row -> mapEval fun m row)

    idvals <- getVec evalNid ids

    ltvals <- fmap toLtype <$> (V.zip <$> getVec evalBool lt1 <*> getVec evalBool lt2)
    lcntvals <- getVec evalInt lcnt
    lstvals <- getVec evalNid lst
    lctrvals <- getVec evalInt lctr
    llenvals <- getVec evalInt llen

    ldcvals <-  getMat evalInt ldctrs
    ldvals <-  getMat evalInt ldeltas
    ucvals <- getMat evalInt  uctrs
    uvals <-  getMat evalBool updates
    gvals <- fmap (\(g,l,x) -> V.zip3 g l x) <$> (V.zip3 <$> getMat evalBool guardsGE <*> getMat evalBool guardsLT <*> getMat evalInt guardsX)

    lblvals <- getMat evalBool labels

    return $ V.toList $ V.generate (length indices) (\i ->
      PosVars {
        posId = idvals V.! i

      , posLType = ltvals V.! i
      , posLCount = lcntvals V.! i
      , posLStart = lstvals V.! i
      , posLCtr = lctrvals V.! i
      , posLLen = llenvals V.! i

      , posLDCtrs = ldcvals V.! i
      , posLDelta = ldvals V.! i
      , posUCtrs = ucvals V.! i
      , posUpd = uvals V.! i
      , posGrd = gvals V.! i

      , posLbls = lblvals V.! i
      })
  end2 <- currTime
  log $ "Finished after: "++showTime start2 end2
  return result

  where showTime a b = show (msTimeDiff a b :: Double) ++ " ms"
        log = when verbose . liftIO . putStrLn

-- generate pretty-printed run string for output
showRun :: Formula Char -> Run -> String
showRun f r = B.render $ B.hsep 4 B.left [B.hsep 1 B.left [ids,lts,lcs,lst,lln, lds], tri, lbl]
  where mkCol name cells = (B.text name) B.// (B.vcat B.top cells)
        addLT fun p = (fun p, posLType p)
        showIfLoop (_,Out) = ""
        showIfLoop (a,_) = show a
        sfs = enumerateSubformulas f

        ids = mkCol "ID" $ map (B.text . show . posId) r
        lts = mkCol "LT" $ map (B.text . lsym . posLType) r
        lcs = mkCol "LC" $ map (B.text . lcount . posLCount) r
        lst = mkCol "LS" $ map (B.text . showIfLoop . addLT posLStart) r
        lln = mkCol "LL" $ map (B.text . showIfLoop . addLT posLLen) r
        lds = mkCol "LD" $ map (B.text . showIfLoop . addLT posLDelta) r

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
        c2str ((g,l,x),v,u) = (if g then "[≥"++show x++"] " else if l then "[<"++show x++"] " else "[  ] ") ++ show v ++ (if u then " (+)" else " (-)")
