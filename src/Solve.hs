module Solve (
  SolveConf(..), defaultSolveConf, findRun, showRun
) where
import Data.Data
import Prelude hiding (log)
import Data.Bool
import Data.Ratio
import Data.Maybe
import Data.Char (isAlphaNum)
import Data.List (intercalate, transpose, sortOn)
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
import Util (currTime, showTime, at)
import Types
import Z3Util

-- | configuration structure for the checker
data SolveConf a b = SolveConf
  { slvFormula    :: Formula a    -- ^ the fLTL formula to check
  , slvSchemaSize :: Int          -- ^ schema size to use
  , slvGraphFile  :: String       -- ^ source file of the graph (not necessary for operation)
  , slvLoopLens   :: [Int]        -- ^ all simple loop lengths in graph (if empty, will be calculated)
  , slvUseIntIds  :: Bool         -- ^ use ints for node ids instead of enum
  , slvUseBoolLT  :: Bool         -- ^ use pairs of bools for loop type instead of enum
  , slvVerbose    :: Bool         -- ^ show additional information
  }
-- | default configuration for the checker
defaultSolveConf :: Formula a -> Int -> SolveConf a b
defaultSolveConf f n = SolveConf f n "" [] False False False

data PosVars = PosVars
  { posId     :: Int              -- ^ node id at current position (first node: 0)
  , posLType  :: LoopType         -- ^ are we in or outide/at border of a loop
  , posLCount :: Integer          -- ^ how often is this node visited (outside of loop: 1)
  , posLStart :: Int              -- ^ if in loop, start node, else: 0 as dummy
  , posLCtr   :: Integer          -- ^ counter to calculate loop length
  , posLLen   :: Integer          -- ^ length of current loop (outside: 0)

  , posLbls    :: Vector Bool     -- ^ for each subformula, flag whether it holds at this position
  , posGCtrs   :: Vector Integer  -- ^ intermediate values of counters defined by the graph
  , posUDCtrs   :: Vector Integer  -- ^ intermediate values of counters of the structure (delta)
  , posUWCtrs   :: Vector Integer  -- ^ intermediate values of counters of the structure (witness)
  , posUSufMax :: Vector Integer  -- ^ back-propagated maximum of future values of counters
  }

data Run = Run
  { runPos     :: Vector PosVars  -- ^ endcodes information present for every schema position
  , runLHasPsi :: Vector Bool     -- ^ flag that says whether the last loop has a psi
  , runLDelta  :: Vector Integer  -- ^ deltas of loop for the counters for U[m/n], outside loops: 0
  }

-- | loop type enum, different encodings in Z3 can be toggled
data LoopType = Out | Start | In | End deriving (Eq, Read, Show, Ord)

-- | abbreviation for often used combination
(=<<<) :: (Traversable t, Monad m) => (t a -> m b) -> t (m a) -> m b
f =<<< xs = f =<< sequence xs

-- | input: graph structure and configuration with formula and settings
--   output: valid run if possible
findRun :: (Data a, Ord a, Ord b) => SolveConf a b -> Graph a b -> IO (Maybe Run)
findRun (SolveConf f n _ ml useIntIds useBoolLT verbose) gr = evalZ3 $ do
  when (n<=0) $ error "path schema must have positive size!"

  lens <- case ml of
    [] -> do
      -- calculate valid loop lens with Johnsons algorithm in (v+e)(c+1)
      -- selfloops must be unrolled to loops of size 2 -> we must always allow 2.
      -- apart of self-loops, all guessed loops are simple cycles in graph
      log "Enumerating simple cycle lengths..."
      start0 <- currTime
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
  _0 <- mkInteger 0
  _1 <- mkInteger 1
  let indices = [0..n-1]            -- helper to quantify over indices of variables
  let ge = edges gr                 -- get directed edges of graph
  let ctrs = counters gr            -- get list of all symbols used as counters in graph
  let ctr2num = M.fromList $ zip ctrs [0..] -- mapping from counters in graph to their indices

  -- variables to store node ids of path schema
  (EnumAPI mkFreshNidVar evalNid isNid eqNid) <- bool (mkEnumSort "Nid") mkIntEnumSort useIntIds $ (nodes gr) ++ [-1]
  ids <- mkVarVec mkFreshNidVar "nid" indices

  -- | given an edge and a pair of variable node ids, express that they represent this edge
  let isEdge (i,j) (fromVar,toVar) = mkAnd =<<< [isNid i fromVar, isNid j toVar]
  -- | given valid edges and two variable syms, enumerate all valid assignments
  let isValidEdge = mkAny isEdge (toEdge <$> ge)

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
  lst  <- mkVarVec mkFreshNidVar "lst" indices
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
  -- intermediate counter values (total effect)
  udctrs    <- mkVarMat mkFreshIntVar "ud" indices uindices
  -- intermediate counter values (in loops for first iteration)
  uwctrs    <- mkVarMat mkFreshIntVar "uw" indices uindices
  -- maximum of all future countervalues encountered at psis of U-formula j
  ucsufmax <- mkVarMat mkFreshIntVar "usm" indices uindices

  -- loop delta of last loop for each U[r] -> total is in [n-1][j]
  let maxllen = min n (maximum lens) -- maximum allowed loop len (simple loops in graph)
  -- ldelta[i][j] is meaning ldelta[n-maxllen+i][j]
  ldeltas  <- mkVarMat mkFreshIntVar  "ld" [1..maxllen] uindices
  -- last loop has psi of U[r]_j ?
  lhaspsi  <- mkVarVec mkFreshBoolVar "lp" uindices

  -- values for graph counters, similar to uctrs
  let cindices = [0..length ctrs-1]
  gctrs <- mkVarMat mkFreshIntVar "gct" indices cindices

  -- linear combination of variables at position i
  let lincomb i lc = mkAdd =<< mapM (\(c,var) -> mkMul =<<< [mkInteger c, pure $ at gctrs i $ ctr2num M.! var]) lc
  -- constraint that the variables at position i should respect the given guard
  let respectGuardAt i (t,(lc,v)) = join $ opop M.! t <$> lincomb i lc <*> (mkInteger v)
      opop = M.fromList [(GuardGt, mkGt), (GuardGe, mkGe), (GuardEq, mkEq), (GuardLe, mkLe), (GuardLt, mkLt)]

  --------------------------------------------------------------------------------------------------
  -- always start path at node 0
  assert =<< isNid   0   (ids  V.! 0    )

  -- path ends with ending of a loop (we consider only infinite paths!)
  assert =<< isLtype End (lt   V.! (n-1))
  -- force loop count = 0 in last loop (special case! all other lcnt are > 0)
  assert =<< mkEq    _0  (lcnt V.! (n-1))

  -- start counting steps at zero with lcnt[0]
  assert =<< mkEq (steps V.! 0) (lcnt V.! 0)

  -- we want the complete formula to be satisfied, i.e. total formula labeled at first node (the node with id 0)
  assert =<< mkEq (V.last $ labels V.! 0) _T

  -- all until phi freq. counters start at 0
  assert =<< mkForallI (M.toList untils) (\(_,j) -> mkEq (at udctrs 0 j) _0)
  assert =<< mkForallI (M.toList untils) (\(_,j) -> mkEq (at uwctrs 0 j) _0)

  -- all user defined counters start at 0
  assert =<< mkForallI cindices (\i -> mkEq (at gctrs 0 i) _0)

  -- helper: f shall hold with one of the valid loop lengths
  let withLoopLen i prop = mkExistsI lens (\l -> mkAnd =<<< [join $ mkEq (llen V.! i) <$> (mkInteger $ fromIntegral l), prop l])
  -- helper: a + C = b, C const
  let isInc c a b = join $ mkEq b <$> (mkAdd =<<< [mkInteger c, pure a])
  -- helper: a + x*C = b, C const
  let isIncMul c x a b = join $ mkEq b <$> (mkAdd =<<< [pure a,  mkMul =<<< [mkInteger c, pure x]])
  -- helper: forall j. mat[i][j] = mat[i2][j]
  let allEq i i2 js mat = mkForallI js (\j -> mkEq (at mat i j) (at mat i2 j))

  -- general assertions about path schema structure
  assert =<< mkForallI indices (\i -> mkAnd =<<<
    [ -- neighboring ids must have valid edge (check that non-looping path is valid)
      ifT (i>0) $ isValidEdge (ids V.! (i-1), ids V.! i)
      -- enforce looptype structure (Out | Start (In*) End)*(Start (In*) End)
    , ifT (i>0) $ mkAnd =<<< (map join
        [ mkImplies <$> (isLtype Start (lt V.! i)) <*> (isLtype Out           (lt V.! (i-1)))
        , mkImplies <$> (isLtype End   (lt V.! i)) <*> (isOneOfLT [In,Start]  (lt V.! (i-1)))
        , mkImplies <$> (isLtype In    (lt V.! i)) <*> (isOneOfLT [In,Start]  (lt V.! (i-1)))
        , mkImplies <$> (isLtype Out   (lt V.! i)) <*> (isOneOfLT [Out,End]   (lt V.! (i-1)))
        ])

      -- loop count >= 0 in general
    , mkLe _0 (lcnt V.! i)
      -- loop count > 1 in all loops but last (which ends at n-1)
    , ifT (i<n-1) $ join $ mkImplies <$> isLtype End (lt V.! i) <*> mkLt _1 (lcnt V.! i)
      -- loop count = 1 <-> outside of loop
    , join $ mkIff <$> isLtype Out (lt V.! i) <*> mkEq (lcnt V.! i) _1
      -- consistent loopcount in loops
    , ifT (i>0) $ mkAnd =<<<
      [ join $ mkImplies <$> isLtype In    (lt V.! i) <*> (mkEq (lcnt V.! i) (lcnt V.! (i-1)))
      , join $ mkImplies <$> isLtype End   (lt V.! i) <*> (mkEq (lcnt V.! i) (lcnt V.! (i-1)))
      ]
      -- add up all node repetitions to get run length
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
    , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> (isInc 1 (lctr V.! (i-1)) (lctr V.! i))

    -- loop length outside of loops is zero
    , join $ mkImplies <$> isLtype Out (lt V.! i) <*> mkEq (llen V.! i) _0
    -- loop length init at loop end
    , join $ mkImplies <$> isLtype End (lt V.! i) <*> mkEq (lctr V.! i) (llen V.! i)
    -- loop length counter propagate
    , ifT (i>0) $ join $ mkImplies <$> (isOneOfLT [In,End] (lt V.! i)) <*> mkEq (llen V.! (i-1)) (llen V.! i)

    -- valid backloop and also loop length (restrict to possible lengths of simple loops in orig. graph)
    , join $ mkImplies <$> isLtype End (lt V.! i) <*> (mkAnd =<<<
        [ isValidEdge (ids V.! i, lst V.! i) -- valid backloop
        , withLoopLen i $ const mkTrue       -- valid loop length
        ])

    -- the following unrollings enforce that the loops satisfy all until label
    -- conditions, as only such loops can be chosen which don't need to be split

    -- enforce 1x unrolled left (same ids, but outside of loop)
    -- required for checking untils in last loop and the graph guards in all loops
    , join $ mkImplies <$> (mkNot =<< isLtype Out (lt V.! i))
        <*> (withLoopLen i (\l -> ifF (i-l >= 0) (mkAnd =<<<
        [ isLtype Out (lt V.! (i-l))
        , eqNid (ids V.! i) (ids V.! (i-l))
        , allEq i (i-l) (snd <$> M.toList sfs) labels
        ])))

    -- enforce 1x unrolled right for efficient normal until checking (unless last loop)
    -- this is required for the regular until to check psi and to check graph guards
    , join $ mkImplies <$> (mkAnd =<<< [mkNot =<< isLtype Out (lt V.! i), mkNot =<< (mkEq (lcnt V.! i) _0)])
        <*> (withLoopLen i (\l -> ifF (i+l<=n-1) (mkAnd =<<<
        [ isLtype Out (lt V.! (i+l))
        , eqNid (ids V.! i) (ids V.! (i+l))
        , allEq i (i+l) (snd <$> M.toList sfs) labels
        ])))

    -- enforce correct graph counter updates and guards
    , ifT (i>0) $ mkForallI ge (\(a,b,l) -> do
        let (upd, grd) = (updates l, guards l)
        join $ mkImplies <$> isEdge (a,b) (ids V.! (i-1), ids V.! i) <*> mkAnd =<<<
          [ -- update graph counters corresponding to edge labelling
            mkForallI ctrs (\ctr ->
              let (j, u) = (ctr2num M.! ctr, fromMaybe 0 $ M.lookup ctr upd)
              in isIncMul u (lcnt V.! (i-1)) (at gctrs (i-1) j) (at gctrs i j) )
            -- guards are respected outside loops. as each loop is unrolled in
            -- both directions and a loop has a constant delta, this is sufficient
          , join $ mkImplies <$> (isLtype Out (lt V.! (i-1))) <*> mkForallI grd (respectGuardAt i)
          ])

    -- enforce correct until counter updates
    , mkForallI (M.toList untils) (\((Until r a _), j) -> do
      let phi    = sfs M.! a
          (x, y) = (numerator r, denominator r)
          -- let r=x/y is the ratio at U[r]). do something with...
          withUpdateAt k prop = join $ mkIte (at labels k phi) <$> prop (fromIntegral (y-x)) -- positive update if phi holds: y-x
                                                               <*> prop (fromIntegral (-x) ) -- and negative if it does not:  -x
      mkAnd =<<<
          -- counter value at i>0 = old value at i-1 + update on edge from i-1 times the number of visits of i-1
          -- (proportional to number of node visits, semantically invalid inside loops, just used as accumulator there)
          -- notice: counter value in last loop does not change (lcnt==0!) but it does not matter, see at loop delta to decide whether its a good loop
        [ ifT (i>0) $ withUpdateAt (i-1) $ \u ->
            isIncMul u (lcnt V.! (i-1)) (at udctrs (i-1) j) (at udctrs i j)
          -- counter update for witness counters. count updates just once, but synchronize after loops with delta counters
        , ifT (i>0) $ withUpdateAt (i-1) $ \u -> join $
            mkIte <$> (isLtype End (lt V.! (i-1)))
                  <*> (mkEq (at udctrs i j) (at uwctrs i j))
                  <*> (isInc u (at uwctrs (i-1) j) (at uwctrs i j))


          -- accumulate loop deltas for last loop (we have only maxllen positions, at right of the schema)
        , let i' = n-maxllen+i in
          ifT (i<maxllen) $ mkAnd =<<<
          [ join $ mkImplies <$> isLtype Out (lt V.! i') <*> mkEq (at ldeltas i j) _0 -- outside of loop -> 0
          , join $ mkImplies <$> (mkEq (lcnt V.! i') _0) <*> (mkAnd =<<<              -- in last loop:
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
          Next _ ->  lbl_ij_equiv_to $ mkAnd =<<<
            [ ifT (i<n-1) $ mkAnd (lbl (i+1) <$> subf) -- subf. must hold in succ. node
            -- backloop edge -> check value from left unrolled copy (it's successor is the same node)
            , join $ mkImplies <$> (isLtype End (lt V.! i)) <*> withLoopLen i (\l -> ifF (i-l>=0) $ pure $ lbl (i-l) j)
            ]

          -- need to consider subformulas in until separately.. get their subformula index and set constraints
          Until 1 a b -> do -- this is the regular until
            let (phi, psi) = (sfs M.! a, sfs M.! b)
            -- psi holds at some time in the future and for all positions until then phi holds.
            lbl_ij_equiv_to $ mkOr =<<<
                -- psi holds -> until holds here
              [ pure $ lbl i psi
                -- phi holds -> until works here if it holds in next position too
              , ifF (i<n-1) $ mkAnd =<<< [pure $ lbl i phi, pure $ lbl (i+1) j]
                -- if we are at the last position, check the unrolled copy at the left and ensure that there really is a psi
              , ifF (i==n-1) $ mkAnd =<<<
                  [ withLoopLen i (\l -> ifF (i-l>=0) $ pure $ lbl (i-l) j)
                  , mkExistsI [i-maxllen+1..i] (\k -> ifF (k>=0) $ mkAnd =<<< [pure $ at labels k psi, mkEq (lcnt V.! k) _0])
                  ]
              ]

          u@(Until _ _ b) -> do -- this is the frequency until
            let psi = sfs M.! b
                k   = untils M.! u -- get index of this evil until in evil until list
            -- implementation of the witness condition outside of loops. U[r]_j holds here if:
            join $ mkImplies <$> (isLtype Out (lt V.! i)) <*> lbl_ij_equiv_to (mkOr =<<<
              [ pure $ lbl i psi   -- psi holds ...
              , mkAnd =<<< [ pure $ lhaspsi V.! k, mkGt (at ldeltas (maxllen-1) k) _0 ] -- or last loop is good and has psi ...
                -- or there is a pos. k>i where psi holds guarded with at least >= current phi counter for U[r]_j
              , mkGe (at ucsufmax i k) (at uwctrs i k)
              ])
      )
    ])

  assert =<< mkForallI (M.toList untils) (\((Until r _ b), j) -> do
    let (psi,x) = (sfs M.! b, numerator r)
    mkAnd =<<<
        -- lhaspsi_j <-> there is a psi in the last loop for U[r]_j
      [ join $ mkIff (lhaspsi V.! j) <$> (mkExistsI [n-maxllen..n-1] (\i ->
          mkAnd =<<< [pure $ at labels i psi, mkEq (lcnt V.! i) _0]))

         -- calculate counter suffix max: start out with worst possible value for maximum (semantically -inf)
         , join $ mkEq (at ucsufmax (n-1) j)
             <$> (mkAdd =<<< [mkInteger (-1), mkMul =<<< [pure $ steps V.! (n-1), mkInteger $ fromIntegral (-x)]])

         -- then, at psi positions take maximum of current and future, otherwise just push through
         , mkForallI (init indices) (\i -> join $
             mkIte (at labels i psi) <$> (mkWithMax (at ucsufmax (i+1) j) (at uwctrs i j)) (mkEq (at ucsufmax i j))
                                     <*> (mkEq (at ucsufmax i j) (at ucsufmax (i+1) j)))
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
        getVec evalfunc vec = fromMaybe V.empty <$> (V.sequence <$> (mapM (evalfunc m) vec))

        getMat :: EvalAst Z3 a -> Vector (Vector AST) -> Z3 (Vector (Vector a))
        getMat fun mat = fromMaybe V.empty . V.sequence <$> V.forM mat (\row -> mapEval fun m row)

    idvals <- getVec evalNid ids
    ltvals <- getVec evalLT lt

    lcntvals <- getVec evalInt lcnt
    lstvals <- getVec evalNid lst
    lctrvals <- getVec evalInt lctr
    llenvals <- getVec evalInt llen

    udvals <- getMat evalInt udctrs
    uwvals <- getMat evalInt uwctrs
    usvals <- getMat evalInt ucsufmax

    lblvals <- getMat evalBool labels

    gcvals <- getMat evalInt gctrs

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

      , posUDCtrs = udvals V.! i
      , posUWCtrs = uwvals V.! i
      , posUSufMax = usvals V.! i

      , posLbls = lblvals V.! i

      , posGCtrs = gcvals V.! i
      })) lpvals ldvals
  end2 <- currTime
  log $ "Finished after: "++showTime start2 end2
  return result
  where log = when verbose . liftIO . putStrLn

-- | generate pretty-printed run string for output
showRun :: (Data a, Ord a, Ord b, Show a, Show b) => Formula a -> Graph a b -> Run -> Maybe Int -> String
showRun f g run width = B.render $ B.vcat B.top rows
  where rv = runPos run
        lp = runLHasPsi run
        ld = runLDelta run
        r = V.toList rv
        ctrs = counters g

        mkCol name cells = (B.text name) B.// (B.vcat B.top cells)
        addLT fun p = (fun p, posLType p)
        showIfLoop (_,Out) = ""
        showIfLoop (a,_) = show a
        sfs = enumerateSubformulas f
        untils = map fst $ sortOn snd $ M.toList $ getEvilUntils sfs

        num = mkCol "N"  $ map (B.text . show) [1..length rv]
        sep = mkCol "|"  $ map B.text (["|"] <* [1..length rv])
        ids = mkCol "ID" $ map (B.text . show       . posId) r
        lts = mkCol "LT" $ map (B.text . lsym       . posLType) r
        lst = mkCol "LS" $ map (B.text . showIfLoop . addLT posLStart) r
        lln = mkCol "LL" $ map (B.text . showIfLoop . addLT posLLen) r
        lcs = mkCol "LC" $ map (B.text . lcount     . posLCount) r

        -- show counter column only if there are any
        -- uctrs = if V.null lp then B.nullBox
        --         else mkCol "[(UD,UW,UM)_j]" $ (map (B.text . show . (\p -> V.zip3 (posUDCtrs p) (posUWCtrs p) (posUSufMax p))) r) ++ [lastloopinfo]
        uctrs = if V.null lp then B.nullBox
                else B.hsep 1 B.left $ map (B.vcat B.top) $ transpose
                     $ (map (B.text . show) untils):
                       (map (map (B.text . show) . V.toList . (\p -> V.zip3 (posUDCtrs p) (posUWCtrs p) (posUSufMax p))) r)
                       ++[lastloopinfo]
        lastloopinfo = map B.text $ V.toList $ V.zipWith (\a b->a++"/"++b) (V.map show lp) (V.map goodness ld)

        -- show graph counter col if any counters present
        gctrs = if V.null (posGCtrs $ V.head $ rv) then B.nullBox
                else B.hsep 1 B.left $ map (B.vcat B.top) $ transpose $ ctrhdr:(map ((B.text "" :) . map (B.text . show) . V.toList . posGCtrs) r)
        ctrhdr = B.text "GC:" : (B.text . filter isAlphaNum . show <$> ctrs)

        lblock = map B.text $ lines $ B.render $ B.hsep 1 B.left [num,sep,ids,lts,lst,lln,lcs, uctrs, gctrs]
        wl = B.cols $ head lblock
        -- if max. width provided, wrap labels
        labelfunc = case width of
                      Nothing -> B.text
                      Just w -> B.para B.left $ w-wl-4

        lbl = B.text "Labels:" : map (labelfunc . lbls . posLbls) r
        lblids = map fst . filter snd . zip [0..] . V.toList
        lbls = intercalate ", " . sortOn (\s -> (length s, s)) . map show . map (isfs M.!) . lblids
        isfs = M.fromList $ map (\(a,b) -> (b,a)) $ M.toList sfs --to map indices back to subformulas

        rows = zipWith (\a b -> B.hsep 4 B.top [a,b]) lblock (lbl++[B.nullBox])

        lsym Start = "<"
        lsym End = "-"
        lsym In = "|"
        lsym Out = " "
        lcount 1 = ""
        lcount n = show n
        goodness n | n>0 = "+" | n==0 = "=" | otherwise = "-"
