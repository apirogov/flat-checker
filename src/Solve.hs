module Solve (
  SolveConf(..), defaultSolveConf, findRun, showRun
) where
import Prelude hiding (log)
import Data.Bool
import Data.Ratio
import Data.Maybe
import Data.List (intercalate)
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
import Util (currTime, showTime)
import Types
import Z3Util

-- | given valid edges and two variable syms, enumerate all valid assignments
-- isValidEdge :: [(Int,Int)] -> Vector AST -> (AST,AST) -> Z3 AST
isValidEdge validEdges isNid (fromVar,toVar) = mkOr =<< forM validEdges (\(i,j) ->
  mkAnd =<< sequence [isNid i fromVar, isNid j toVar])

-- | helper: access 2-indexed variable
at var i j = (var V.! i) V.! j

-- | configuration structure for the checker
data SolveConf = SolveConf
  { slvFormula    :: Formula Char -- ^ the fLTL formula to check
  , slvSchemaSize :: Int          -- ^ schema size to use
  , slvGraphFile  :: String       -- ^ source file of the graph (not necessary for operation)
  , slvLoopLens   :: [Int]        -- ^ all simple loop lengths in graph (if empty, will be calculated)
  , slvUseIntIds  :: Bool         -- ^ use ints for node ids instead of enum
  , slvUseBoolLT  :: Bool         -- ^ use pairs of bools for loop type instead of enum
  , slvVerbose    :: Bool         -- ^ show additional information
  }
-- | default configuration for the checker
defaultSolveConf f n = SolveConf f n "" [] False False False

data PosVars = PosVars
  { posId     :: Int              -- ^ node id at current position (first node: 0)
  , posLType  :: LoopType         -- ^ are we in or outide/at border of a loop
  , posLCount :: Integer          -- ^ how often is this node visited (outside of loop: 1)
  , posLStart :: Int              -- ^ if in loop, start node, else: 0 as dummy
  , posLCtr   :: Integer          -- ^ counter to calculate loop length
  , posLLen   :: Integer          -- ^ length of current loop (outside: 0)

  , posLbls    :: Vector Bool     -- ^ for each subformula, flag whether it holds at this position
  , posUCtrs   :: Vector Integer  -- ^ intermediate values of counters of the structure
  , posUSufMax :: Vector Integer  -- ^ back-propagated maximum of future values of counters
  }

data Run = Run
  { runPos     :: Vector PosVars  -- ^ endcodes information present for every schema position
  , runLHasPsi :: Vector Bool     -- ^ flag that says whether the last loop has a psi
  , runLDelta  :: Vector Integer  -- ^ deltas of loop for the counters for U[m/n], outside loops: 0
  }

-- | loop type enum, different encodings in Z3 can be toggled
data LoopType = Out | Start | In | End deriving (Eq, Read, Show, Ord)

-- | is one of given items mapped by some value
mkAny f ls p = mkOr =<< mapM (flip f p) ls

-- | input: graph structure and configuration with formula and settings
--   output: valid run if possible
findRun :: SolveConf -> Graph Char -> IO (Maybe Run)
findRun (SolveConf f n _ ml useIntIds useBoolLT verbose) gr = evalZ3 $ do
  when (n<=0) $ error "path schema must have positive size!"

  lens <- case ml of
    [] -> do
      log "Enumerating simple cycle lengths..."
      start0 <- currTime
      -- calculate valid loop lens with Johnsons algorithm in (n+e)(c+1)
      -- selfloops must be unrolled to loops of size 2 -> we must always allow 2
      -- apart of self-loops, all guessed loops are simple cycles in graph
      let lens = IS.elems $ IS.insert 2 $ getCycleLens gr
      end0 <- currTime
      log $ "Found lengths " ++ show lens ++ " in: " ++ showTime start0 end0
      return lens
    -- if the provided lengths are incomplete, probably a solution will not be found!
    -- if a superset is provided, the formula will be bigger than neccessary,
    -- but may be a good idea for small, but REALLY dense graphs (provide [1..n])
    ls -> log ("Using provided simple cycle lengths: "++show ls) >> return (2:ls)

  --------------------------------------------------------------------------------------------------
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

  -- variables to store node ids of path schema
  (EnumAPI mkFreshNodeVar evalNid isNid eqNid) <- bool (mkEnumSort "Nid") mkIntEnumSort useIntIds $ (nodes gr) ++ [-1]
  ids <- mkVarVec mkFreshNodeVar "nid" indices

  -- variables to indicate loop structure
  -- no self loops, only "simple" loops (no internal id equal to left or right border)
  (EnumAPI mkFreshLTVar evalLT isLtype _) <- bool (mkEnumSort "Lt") mkBoolEnumSort useBoolLT $ [Out,Start,In,End]
  lt <- mkVarVec mkFreshLTVar "lt" indices
  let isOneOfLT = mkAny isLtype

  -- loop counters (how often is this node taken? >1 at loops only)
  lcnt <- mkVarVec mkFreshIntVar "lct" indices
  -- prefix sum of lcnt (has total run length in last position)
  steps <- mkVarVec mkFreshIntVar "stp" indices
  -- loop start propagation
  lst  <- mkVarVec mkFreshNodeVar "lst" indices
  -- loop length counter
  lctr <- mkVarVec mkFreshIntVar "lct" indices
  -- loop length indicator (derived from lctr)
  llen <- mkVarVec mkFreshIntVar "lln" indices

  -- get all subformulas with assigned id
  let sfs = enumerateSubformulas f
  -- variable sets to store labels (list of lists, each node has vars with flags of all subf)
  labels <- mkVarMat mkFreshBoolVar "lbl" indices [1..length sfs]

  -- to correctly label the rational untils, we need to employ the counters
  -- each state of the path has an own counter per ratio-U subformula which is firstly updated there
  -- there are 2 guards per counter: <0, >=0. both can be on the incoming edge of a node
  let untils = getEvilUntils sfs
  let numUntils = length untils
  let uindices = [1..numUntils]
  -- vars per state and U-formula: X[i][j] i=current schema state, j=number U-formula counter
  -- intermediate counter values
  uctrs    <- mkVarMat mkFreshIntVar "uct" indices uindices
  -- maximum of all future countervalues encountered at psis of U-formula j
  ucsufmax <- mkVarMat mkFreshIntVar "usm" indices uindices

  -- loop delta of last loop for each U[r] -> total is in [n-1][j]
  let maxllen = min n (maximum lens) -- maximum allowed loop len (simple loops in graph)
  -- ldelta[i][j] is meaning ldelta[n-maxllen+i][j]
  ldeltas  <- mkVarMat mkFreshIntVar  "ld" [1..maxllen] uindices
  -- last loop has psi of U[r]_j ?
  lhaspsi  <- mkVarVec mkFreshBoolVar "lp" uindices
  -- helper: last loop has psi and is good
  lnice    <- mkVarVec mkFreshBoolVar "lpd" uindices

  --------------------------------------------------------------------------------------------------
  -- always start path at node 0
  assert =<< isNid 0 (ids V.! 0)

  -- path ends with ending of a loop (we consider only infinite paths!)
  assert =<< isLtype End (lt   V.! (n-1))
  -- force loop count = 0 in last loop (special case! all other lcnt are > 0)
  assert =<< mkEq _0     (lcnt V.! (n-1))

  -- start counting steps at zero with lcnt[0]
  assert =<< mkEq (steps V.! 0) (lcnt V.! 0)

  -- we want the complete formula to be satisfied, i.e. total formula labeled at first node (the node with id 0)
  assert =<< mkEq (V.last $ labels V.! 0) _T

  -- all until phi freq. counters start at 0
  assert =<< mkForallI (M.toList untils) (\(_,j) -> mkEq (at uctrs 0 j) _0)

  -- helper: f shall hold with one of the valid loop lengths
  let withLoopLen i prop = mkExistsI lens (\l -> mkAnd =<< sequence [join $ mkEq (llen V.! i) <$> (mkInteger $ fromIntegral l), prop l])
  -- helper: a + c = b, where c const
  let isInc c a b = join $ mkEq b <$> (mkAdd =<< sequence [mkInteger $ fromIntegral c, pure a])
  -- helper: forall j. mat[i][j] = mat[i2][j]
  let allEq i i2 js mat = mkForallI js (\j -> mkEq (at mat i j) (at mat i2 j))

  -- general assertions about path schema structure
  assert =<< mkForallI indices (\i -> mkAnd =<< sequence
    [ -- neighboring ids must have valid edge (check that non-looping path is valid)
      ifT (i>0) $ isValidEdge ge isNid ((ids V.! (i-1)),(ids V.! i))
      -- enforce looptype structure (Out | Start (In*) End)*(Start (In*) End)
    , ifT (i>0) $ mkAnd =<< sequence (map join
        [ mkImplies <$> (isLtype Start (lt V.! i)) <*> (isLtype Out           (lt V.! (i-1)))
        , mkImplies <$> (isLtype End   (lt V.! i)) <*> (isOneOfLT [In,Start]  (lt V.! (i-1)))
        , mkImplies <$> (isLtype In    (lt V.! i)) <*> (isOneOfLT [In,Start]  (lt V.! (i-1)))
        , mkImplies <$> (isLtype Out   (lt V.! i)) <*> (isOneOfLT [Out,End]   (lt V.! (i-1)))
        ])

      -- loop count >= 0 in general
    , mkLe _0 (lcnt V.! i)
      -- loop count > 1 in all loops but last
    , ifT (i<n-1) $ join $ mkImplies <$> isLtype End (lt V.! i) <*> mkLt _1 (lcnt V.! i)
      -- loop count = 1 <-> outside of loop
    , join $ mkIff <$> isLtype Out (lt V.! i) <*> mkEq (lcnt V.! i) _1
      -- consistent loopcount in loops
    , ifT (i>0 && i<n-1) $ mkAnd =<< sequence
      [ join $ mkImplies <$> isLtype Start (lt V.! i) <*> (mkEq (lcnt V.! i) (lcnt V.! (i+1)))
      , join $ mkImplies <$> isLtype In    (lt V.! i) <*> (mkEq (lcnt V.! i) (lcnt V.! (i+1)))
      , join $ mkImplies <$> isLtype End   (lt V.! i) <*> (mkEq (lcnt V.! i) (lcnt V.! (i-1)))
      ]
      -- add up all step repetitions to get run length
    , ifT (i>0) $ join $ mkEq (steps V.! i) <$> mkAdd [steps V.! (i-1), lcnt V.! i]

    -- take loop start id at start from curr id
    , join $ mkImplies <$> (isLtype Start (lt V.! i)) <*> (eqNid (lst V.! i) (ids V.! i))
    -- outside loops start id is -1 (as dummy)
    , join $ mkImplies <$> (isLtype Out (lt V.! i)) <*> (isNid (-1) (lst V.! i))
    -- propagate start id forward in loop
    , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> eqNid (lst V.! (i-1)) (lst V.! i)

    -- loop length counter outside of loops is zero
    , join $ mkImplies <$> isLtype Out   (lt V.! i) <*> mkEq (lctr V.! i) _0
    -- loop length counter init at loop start
    , join $ mkImplies <$> isLtype Start (lt V.! i) <*> mkEq (lctr V.! i) _1
    -- loop length counter propagate
    , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> (isInc (1::Integer) (lctr V.! (i-1)) (lctr V.! i))

    -- loop length outside of loops is zero
    , join $ mkImplies <$> isLtype Out (lt V.! i) <*> mkEq (llen V.! i) _0
    -- loop length init at loop end
    , join $ mkImplies <$> isLtype End (lt V.! i) <*> mkEq (lctr V.! i) (llen V.! i)
    -- loop length counter propagate
    , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> mkEq (llen V.! (i-1)) (llen V.! i)

    -- valid backloop and also loop length (restrict to possible lengths of simple loops in orig. graph)
    , join $ mkImplies <$> isLtype End (lt V.! i) <*> (mkAnd =<< sequence
        [ isValidEdge ge isNid (ids V.! i, lst V.! i) -- valid backloop
        , withLoopLen i $ const mkTrue              -- valid loop length
        ])

    -- the following unrollings enforce that the loops satisfy all until label
    -- conditions, as only such loops can be chosen which don't need to be split

    -- enforce 2x unrolled left (same ids, labels, guards and updates, but outside of loop)
    , join $ mkImplies <$> (mkNot =<< isLtype Out (lt V.! i)) <*> (withLoopLen i (\l -> ifF (i-2*l>=0) (mkAnd =<< sequence
        [ isLtype Out (lt V.! (i-l))
        , isLtype Out (lt V.! (i-2*l))
        , eqNid (ids V.! i) (ids V.! (i-l))
        , eqNid (ids V.! i) (ids V.! (i-2*l))
        , allEq i (i-l)   (snd <$> M.toList sfs) labels
        , allEq i (i-2*l) (snd <$> M.toList sfs) labels
        ])))

    -- enforce 1x unrolled right (unless last loop)
    , join $ mkImplies <$> (mkAnd =<< sequence [mkNot =<< isLtype Out (lt V.! i), mkNot =<< (mkEq (lcnt V.! i) _0)])
        <*> (withLoopLen i (\l -> ifF (i+l<=n-1) (mkAnd =<< sequence
        [ isLtype Out (lt V.! (i+l))
        , eqNid (ids V.! i) (ids V.! (i+l))
        , allEq i (i+l) (snd <$> M.toList sfs) labels
        ])))

    -- enforce correct counter updates
    , mkForallI (M.toList untils) (\((Until r a _), j) -> do
      let phi    = sfs M.! a
          (x, y) = (numerator r, denominator r)
          withUpdateAt k prop = mkAnd =<< sequence                        -- let r=x/y is the ratio at U[r]). do something with...
            [ join $ mkImplies           (at labels k phi) <$> prop (fromIntegral (y-x) :: Integer) -- positive update if phi holds: y-x
            , join $ mkImplies <$> mkNot (at labels k phi) <*> prop (fromIntegral (-x)  :: Integer) -- and negative if it does not:  -x
            ]

      mkAnd =<< sequence
          -- counter value at i>0 = old value at i-1 + update on edge from i-1 times the number of visits of i-1
          -- (proportional to number of node visits, semantically invalid inside loops, just used as accumulator there)
          -- notice: counter value in last loop does not change (lcnt==0!) but it does not matter, see at loop delta to decide whether its a good loop
        [ ifT (i>0) $ withUpdateAt (i-1) $ \u -> join $
            mkEq (at uctrs i j) <$> (mkAdd =<< sequence [pure $ at uctrs (i-1) j,
                                               mkMul =<< sequence [mkInteger u, pure $ lcnt V.! (i-1)]])

          -- accumulate loop deltas for last loop (we have only maxllen positions, at right of the schema)
        , let i' = n-maxllen+i in
          ifT (i<maxllen) $ mkAnd =<< sequence
          [ join $ mkImplies <$> isLtype Out (lt V.! i') <*> mkEq (at ldeltas i j) _0 -- outside of loop -> 0
          , join $ mkImplies <$> (mkEq (lcnt V.! i') _0) <*> (mkAnd =<< sequence      -- in last loop:
            -- propagate and add as usual to the right
            [ join $ mkImplies <$> isLtype Start (lt V.! i') <*> withUpdateAt i' (\u -> join $ mkEq (at ldeltas i j) <$> (mkInteger u))
            , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i')) <*> withUpdateAt i' (\u -> isInc u (at ldeltas (i-1) j) (at ldeltas i j)) ])
          ]
        ]
      )

    -- enforce correct labelling
    , mkForallI (M.toList sfs) (\(sf,j) -> do --for all the subformulae...
      let subf = subformulas sfs sf --children of current subformula
          lbl = at labels
          lbl_ij_equiv_to t = join $ mkIff <$> pure (lbl i j) <*> t
      case sf of
          -- an atomic proposition holds if the chosen node contains the proposition
          Prop p -> lbl_ij_equiv_to $ mkExistsI (filter (hasProp gr p) $ nodes gr) (\node -> isNid node (ids V.! i))
          -- obvious
          Tru -> lbl_ij_equiv_to mkTrue
          Fls -> lbl_ij_equiv_to mkFalse
          And _ _ -> lbl_ij_equiv_to $ mkAnd (lbl i <$> subf)
          Or _ _ ->  lbl_ij_equiv_to $ mkOr  (lbl i <$> subf)
          Not _ ->   lbl_ij_equiv_to $ mkNot (head $ lbl i <$> subf)
          -- for next the subf. must hold on all successors -> next node and backloop if any
          Next _ ->  lbl_ij_equiv_to $ mkAnd =<< sequence
            [ ifT (i<n-1) $ mkAnd (lbl (i+1) <$> subf) -- subf. must hold in succ. node
            -- backloop edge -> must check that subformula holds in target
            , join $ mkImplies <$> (isLtype End (lt V.! i)) <*> withLoopLen i (\l -> ifF (i-l+1>=0) $ mkAnd (lbl (i-l+1) <$> subf))
            ]
          -- need to consider subformulas in until separately.. get their subformula index and set constraints
          Until 1 a b -> do -- this is the regular until
            let (phi, psi) = (sfs M.! a, sfs M.! b)
            -- psi holds at some time in the future and for all positions until then phi holds.
            lbl_ij_equiv_to (mkOr =<< sequence
                -- psi holds -> until holds here
              [ pure $ lbl i psi
                -- phi holds -> until works here if it holds in next position too
              , ifF (i<n-1) $ mkAnd =<< sequence [pure $ lbl i phi, pure $ lbl (i+1) j]
                -- if we are at the last position, psi must hold somewhere at last loop
              , ifF (i==n-1) $ mkExistsI [i-maxllen+1..i] (\k -> ifF (k>=0) $ mkAnd =<< sequence [pure $ at labels k psi, mkEq (lcnt V.! k) _0])
              ])

          u@(Until _ _ b) -> do -- this is the frequency until
            let psi = sfs M.! b
                k   = untils M.! u -- get index of this evil until in evil until list
            -- implementation of the witness condition outside of loops. U[r]_j holds here if:
            lbl_ij_equiv_to $ (mkOr =<< sequence
              [ pure $ lbl i psi   -- psi holds ...
              , pure $ lnice V.! k -- or last loop is good and has psi ...
                -- or there is a pos. k>i where psi holds guarded with at least >= current phi counter for U[r]_j
              , mkGe (at ucsufmax i k) (at uctrs i k)
              ])
      )
    ])

  assert =<< mkForallI (M.toList untils) (\((Until r _ b), j) -> do
    let (psi,x) = (sfs M.! b, numerator r)
    mkAnd =<< sequence
        -- for which U[r]'s do we have a psi in the last loop?
      [ join $ mkIff (lhaspsi V.! j) <$> (mkExistsI [n-maxllen..n-1] (\i ->
          mkAnd =<< sequence [pure $ at labels i psi, mkEq (lcnt V.! i) _0]))

        -- last loop is "nice" to an evil until if it has the psi and has good phi balance
      , join $ mkIff (lnice V.! j) <$> (mkAnd =<< sequence [ pure $ lhaspsi V.! j, mkGt (at ldeltas (maxllen-1) j) _0 ])

        -- calculate counter suffix max: start out with worst possible value for maximum (semantically -inf)
      , join $ mkEq (at ucsufmax (n-1) j)
            <$> (mkAdd =<< sequence [pure _N1
                 , mkMul =<< sequence [pure $ steps V.! (n-1), mkInteger $ fromIntegral (-x)]])

        -- then, at psi positions take maximum of current and future, otherwise just push through
      , mkForallI (init indices) (\i -> mkAnd =<< sequence [
          join $ mkImplies (at labels i psi) <$> (mkWithMax (at ucsufmax (i+1) j) (at uctrs i j)) (mkEq (at ucsufmax i j))
        , join $ mkImplies <$> (mkNot $ at labels i psi) <*> mkEq (at ucsufmax i j) (at ucsufmax (i+1) j)
        ])
      ])

  -------------------------------------------------------------------------------------------------------------------------------
  -- extract satisfying model from Z3 if possible
  end1 <- currTime
  log $ "Build constraints: " ++ showTime start1 end1
  st <- if verbose then T.pack <$> solverToString else pure T.empty --slow, do only in verbose mode for infos
  let countInts = length $ T.breakOnAll (T.pack "Int") st
  let countBools = length $ T.breakOnAll (T.pack "Bool") st
  let countNids = bool ((subtract 1) . length $ T.breakOnAll (T.pack "Nid_T") st) 0 useIntIds
  let countLTs = bool ((subtract 1) . length $ T.breakOnAll (T.pack "Lt_T") st) 0 useBoolLT
  log $ "Formula size: " ++ show (T.length st) ++ " Ints: " ++ show countInts ++ " Bools: " ++ show countBools
                         ++ " Nids: " ++ show countNids ++ " LTs: " ++ show countLTs

  start2 <- currTime
  log "Searching..."
  result <- fmap snd $ withModel $ \m -> do
    let getVec :: (Model -> b -> Z3 (Maybe a)) -> Vector b -> Z3 (Vector a)
        getVec evalfunc vec = fromMaybe V.empty <$> (sequence <$> (mapM (evalfunc m) vec))

        getMat :: EvalAst Z3 a -> Vector (Vector AST) -> Z3 (Vector (Vector a))
        getMat fun mat = fromMaybe V.empty . V.sequence <$> V.forM mat (\row -> mapEval fun m row)

    idvals <- getVec evalNid ids
    -- ltvals <- fmap toLtype <$> (V.zip <$> getVec evalBool lt1 <*> getVec evalBool lt2)
    ltvals <- getVec evalLT lt

    lcntvals <- getVec evalInt lcnt
    lstvals <- getVec evalNid lst
    lctrvals <- getVec evalInt lctr
    llenvals <- getVec evalInt llen

    ucvals <- getMat evalInt uctrs
    usvals <- getMat evalInt ucsufmax

    lblvals <- getMat evalBool labels

    lpvals <- getVec evalBool lhaspsi
    ldvals <- getVec evalInt $ ldeltas V.! (maxllen-1)

    return $ Run (V.generate (length indices) (\i ->
      PosVars {
        posId = idvals V.! i

      , posLType = ltvals V.! i
      , posLCount = lcntvals V.! i
      , posLStart = lstvals V.! i
      , posLCtr = lctrvals V.! i
      , posLLen = llenvals V.! i

      , posUCtrs = ucvals V.! i
      , posUSufMax = usvals V.! i

      , posLbls = lblvals V.! i
      })) lpvals ldvals
  end2 <- currTime
  log $ "Finished after: "++showTime start2 end2
  return result
  where log = when verbose . liftIO . putStrLn

-- | generate pretty-printed run string for output
showRun :: Formula Char -> Run -> String
showRun f run = B.render (B.hsep 4 B.left [B.hsep 1 B.left [ids,lts,lst,lln,lcs, uctrs], lbl])
  where rv = runPos run
        lp = runLHasPsi run
        ld = runLDelta run
        r = V.toList rv

        mkCol name cells = (B.text name) B.// (B.vcat B.top cells)
        addLT fun p = (fun p, posLType p)
        showIfLoop (_,Out) = ""
        showIfLoop (a,_) = show a
        sfs = enumerateSubformulas f

        ids = mkCol "ID" $ map (B.text . show       . posId) r
        lts = mkCol "LT" $ map (B.text . lsym       . posLType) r
        lst = mkCol "LS" $ map (B.text . showIfLoop . addLT posLStart) r
        lln = mkCol "LL" $ map (B.text . showIfLoop . addLT posLLen) r
        lcs = mkCol "LC" $ map (B.text . lcount     . posLCount) r

        -- show counter column only if there are any
        uctrs = if V.null lp then B.nullBox
                else mkCol "[(UC,UM)_j]" $ (map (B.text . show . (\p -> V.zip (posUCtrs p) (posUSufMax p))) r) ++ [lastloopinfo]
        lastloopinfo = B.text $ intercalate ", " $ V.toList $ V.zipWith (\a b->a++"/"++b) (V.map show lp) (V.map goodness ld)

        lbl = mkCol "Labels" $ map (B.text . lbls . posLbls) r
        lblids = map fst . filter ((==True).snd) . zip [0..] . V.toList
        lbls = intercalate ", " . map show . map (isfs M.!) . lblids
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
        goodness n | n>0 = "+" | n==0 = "=" | otherwise = "-"
