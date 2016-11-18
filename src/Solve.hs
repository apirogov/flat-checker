module Solve where
import System.Clock

import Data.Maybe
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Vector (Vector)
import qualified Data.Vector as V

import Z3.Monad
import Control.Monad
import Control.Monad.IO.Class (liftIO)

import Types
import Data.Ratio

-- given valid edges and two variable syms, enumerate all valid assignments
isValidEdge :: [(Int,Int)] -> (AST,AST) -> Z3 AST
isValidEdge validEdges (fromVar,toVar) =
    mkOr =<< forM validEdges (\(i,j) -> do
      _i <- mkInteger $ fromIntegral i
      _j <- mkInteger $ fromIntegral j
      mkAnd =<< sequence [mkEq fromVar _i, mkEq toVar _j])

-- helper: generate a variable name from prefix and a list of indices
varname pref ind = pref++(intercalate "_" $ map show ind)

mkNeq a b = mkNot =<< mkEq a b

-- sugar, expand quantifiers over variables
mkForallI [] _ = mkTrue
mkForallI ind f = mkAnd =<< forM ind f
mkExistsI [] _ = mkFalse
mkExistsI ind f = mkOr =<< forM ind f

-- helper: allocate a vector of variable symbols with given prefix, indexed over is
mkVarVec mkf name is = V.fromList <$> forM is (\i -> mkf $ varname name [i])

-- vector of run in a path schema, components: -- id,loopid,loopcount,loopflag,labels
type Run = Vector (Integer,Integer,Integer,Bool,Vector Bool)

-- input: graph structure, ltl formula, path schema length
-- output: valid run if possible
findRun :: Graph Char -> Formula Char -> Int -> IO (Maybe Run)
findRun g f n = evalZ3 $ do
  start1 <- liftIO $ getTime Monotonic
  liftIO $ putStrLn "Building model..."

  -- create a few constant elements
  _T <- mkTrue
  _F <- mkFalse
  _N1 <- mkInteger (-1)
  _0 <- mkInteger 0
  _n <- mkInteger $ fromIntegral n -- constant n = number of states in path schema
  let indices = [0..n-1]           -- helper to quantify over indices of variables
  let ge = edges g                 -- get directed edges of graph

  -- variables to store node ids of path schema
  ids <- mkVarVec mkFreshIntVar "nid" indices
  -- add edge constraints
  assert =<< mkEq _0 (ids V.! 0) -- always start path at node 0
  -- neighboring ids must have valid edge
  assert =<< mkAnd =<< return . V.toList =<< V.forM (V.zip ids $ V.tail ids) (isValidEdge ge)
  -- now we have assured that the backbone of the path schema is itself a valid path in the graph.

  -- variables to indicate backloop connections, >0 values always pairwise, inbetween -1, outside 0
  -- no self loops, only "simple" loops (no internal id equal to left or right border)
  bls <- mkVarVec mkFreshIntVar "lid" indices
  -- variables to act as loop counters for the run, decorating nodes that are part of aloop
  lct <- mkVarVec mkFreshIntVar "lct" indices
  -- backloop flag, only true on the nodes that loop back (right border of loop)
  blf <- mkVarVec mkFreshBoolVar "blf" indices

  assert =<< mkAnd =<< V.toList <$> mapM (mkLe _N1) bls -- loop ids >= -1
  assert =<< mkAnd =<< V.toList <$> mapM (mkLe _0) lct  -- loop count >= 0
  assert =<< mkLt _0 (V.last bls) -- path ends with loop (we consider only infinite paths!)
  -- loop count zero <-> loop id zero
  assert =<< mkForallI indices (\i-> join $ mkIff <$> mkEq (bls V.! i) _0 <*> mkEq (lct V.! i) _0)
  -- loop id <= 0 -> backloop = False
  assert =<< mkForallI indices (\i-> join $ mkImplies <$> mkLe (bls V.! i) _0 <*> mkEq (blf V.! i) _F)

  -- NOTE: within means NOT border of loop, strictly inside
  let samePositiveLoopId j k = mkAnd =<< sequence [mkEq (bls V.! j) (bls V.! k), mkLt _0 (bls V.! j)]
      isWithinLoop i = mkExistsI [(j,k) | j<-indices, k<-indices, j<i, i<k] $ uncurry samePositiveLoopId
      ifWithinLoop i f = mkForallI [(j,k) | j<-indices, k<-indices, j<i, i<k]
                       (\(j,k) -> join $ mkImplies <$> (samePositiveLoopId j k) <*> (f j k))
      atLoopStartOf i f = mkExistsI [j | j <- indices, j<i] (\j -> mkAnd =<< sequence
                                                              [ mkLt _0 (bls V.! j)
                                                              , mkForallI [k | k<-indices, j<k, k<i]
                                                                  (\k -> mkEq _N1 (bls V.! k)),f j])

  -- if the loop id is ==-1 -> we are within a loop (there are positions left and right with same positive loop id)
  assert =<< mkForallI indices (\i -> join $ mkImplies <$> (mkEq _N1 (bls V.! i)) <*> (isWithinLoop i))

  -- if the loop id is >0, we are at a loop border (r backloops to l, r /= l)
  assert =<< mkForallI [i | i <- indices, i<n] (\i -> do
      join $ mkImplies <$> (mkLt _0 (bls V.! i)) <*> (mkExistsI [j | j <- indices] (\j -> do
        let (i',j') = (min i j, max i j) -- TODO: think about doing less stuff assuming i<j... but it made problems
        mkAnd =<< sequence
          [ mkEq (bls V.! i') (bls V.! j') -- they have the same loop id
          -- no other index has this loop id
          , mkForallI [k | k<-indices, k/=i', k/=j'] (\k -> mkNeq (bls V.! i') (bls V.! k))
          -- the loop edge is possible in graph
          , isValidEdge ge (ids V.! j', ids V.! i')
          -- enforce correct backloop flag
          , mkEq (blf V.! i') _F , mkEq (blf V.! j') _T
          -- monotonely increasing (just convenient, can be turned off as optimization)
          , mkForallI [k | k<-indices, k<i'] (\k -> mkLe (bls V.! k) (bls V.! i'))
          -- consistent loop count -> all nodes of loop have same loop count
          , mkAnd =<< sequence [mkEq (lct V.! i') (lct V.! j'), mkForallI [k | k<-indices, i'<k, k<j'] (\k -> mkEq (lct V.! i') (lct V.! k))]
          -- all internal loop nodes have id -1 (meaning: its inside a loop)
          , mkForallI [k | k<-indices, i'<k, k<j'] (\k -> mkEq _N1 (bls V.! k))
          -- and loops are simple (internal nodes never equal to a border node)
          , mkForallI [k | k<-indices, i'<k, k<j']
              (\k -> mkNot =<< mkOr =<< sequence [mkEq (ids V.! i') (ids V.! k), mkEq (ids V.! j') (ids V.! k)])
          ])))

  -- get all subformulas with assigned id
  let sfs = listAllSubformulas f

  -- variable sets to store labels (list of lists, each node has vars with flags of all subf)
  labels <- V.fromList <$> forM indices (\i -> V.fromList <$> mapM (\j -> mkFreshBoolVar $ varname "lbl" [i,j]) [1..length sfs])
  -- we want the formula to be satisfied, i.e. total formula labeled at first node (the node with id 0)
  assert =<< mkEq (V.last $ labels V.! 0) _T

  assert =<< mkForallI indices (\i ->  --for all states of schema...
    mkForallI (M.toList sfs) (\(sf,j) -> do --and all subformula flags...
      let lbl i j = ((labels V.! i) V.! j)
          subf = subformulas sfs sf
          lbl_ij_equiv_to t = join $ mkIff <$> pure (lbl i j) <*> t
      case sf of  --and the given subformula flag is valid (depending on kind of subf.)
          -- an atomic proposition holds in all positions with ids of vertices where is holds
          Prop p -> mkExistsI (nodes g) (\node ->  --there exists a graph vertex...
              mkAnd =<< sequence [ join $ mkEq (ids V.! i) <$> mkInteger (fromIntegral node)
                                 , mkEq (lbl i j) $ if hasProp g node p then _T else _F ])
          -- obvious
          And _ _ -> lbl_ij_equiv_to $ mkAnd (fmap (lbl i) subf)
          Or _ _ ->  lbl_ij_equiv_to $ mkOr (fmap (lbl i) subf)
          Not _ ->   lbl_ij_equiv_to $ mkNot (head $ fmap (lbl i) subf)
          -- for next the subf. must hold on all successors -> next node and backloop if any
          Next _ ->  lbl_ij_equiv_to $ mkAnd =<< sequence
            [ if i==n-1 then mkTrue else mkAnd (fmap (lbl (i+1)) subf) -- subf. must hold in succ. node
            -- backloop edge -> must check that subformula holds in target
            , if i==0   then mkTrue else join $ mkImplies <$> pure (blf V.! i)
                                <*> (mkExistsI [j | j<-indices, j<i] (\j ->
                                      mkAnd =<< sequence [mkEq (bls V.! i) (bls V.! j),
                                                mkAnd (fmap (lbl j) subf)]))
            ]
          -- need to consider subformulas in until separately.. get their subformula index and set constraints
          -- TODO: is the until correct?
          Until 1 f g -> do -- this is the regular until
            let (phi, psi) = (fromJust $ M.lookup f sfs, fromJust $ M.lookup g sfs)
                -- psi holds at some time in the future and for all positions until then phi holds
                untilConstraint i j = mkExistsI [i..j] (\k -> mkAnd =<< sequence [pure $ lbl k psi, mkForallI [l | l<-indices, l>=i, l<k] (\l -> pure $ lbl l phi)])
            lbl_ij_equiv_to $ mkAnd =<< sequence [
              -- case: outside of loop or loop start node
                join $ mkImplies <$> (mkOr =<< sequence [mkEq _0 (bls V.! i), mkAnd =<< sequence [mkLt _0 (bls V.! i), mkNot (blf V.! i)]]) <*> untilConstraint i (n-1)
              -- case: in loop, not at start -> find start first
              , join $ mkImplies <$> (mkOr =<< sequence [mkEq _N1 (bls V.! i),mkAnd =<< sequence [mkLt _0 (bls V.! i), pure $ blf V.! i]]) <*> atLoopStartOf i (\j -> untilConstraint j (n-1))
              ]

          _ -> mkTrue --TODO: consistency of evil until
          ))

  -- to correctly label the rational untils, we need to employ the counters
  -- each state of the path has an own counter per ratio-U subformula which is firstly updated there
  -- there are 2 guards per counter: <0, >=0. both can be on the incoming edge of a node
  let untils = getEvilUntils f
  let numUntils = length untils
  let ctrMat f = V.fromList <$> forM indices (\i ->
                   V.fromList <$> forM [0..i] (\j ->
                     V.fromList <$> forM [1..numUntils] (\k -> f i j k)))

  -- per state and U-formula: one counter flag, two incoming guard flags
  -- dimensions: i=current schema state, j=state where the counter initially started
  --             k=which counter U-formula fst: update/guard for inc / snd: for dec counter
  updates <- ctrMat (\i j k -> mkFreshBoolVar $ varname "upd" [i,j,k])
  guards <- ctrMat (\i j k -> mkVarVec mkFreshBoolVar (varname "grd" [i,j,k]) [0,1])
  -- TODO: intermediate counter states

  -- extract satisfying model from Z3 if possible
  end1 <- liftIO $ getTime Monotonic
  liftIO $ putStrLn $ "Build constraints: " ++ showTime start1 end1
  -- TODO: slow, and add more stats about vars used
  st <- solverToString
  liftIO $ putStrLn $ "Formula size: " ++ show (length st)
  start2 <- liftIO $ getTime Monotonic
  liftIO $ putStrLn "Searching..."
  fmap snd $ withModel $ \m -> do
    end2 <- liftIO $ getTime Monotonic
    liftIO $ putStrLn $ "Find model: "++showTime start2 end2

    let getVec :: EvalAst Z3 a -> Vector AST -> Z3 (Vector a)
        getVec evalfunc vec = fromMaybe V.empty . V.sequence <$> V.mapM (evalfunc m) vec
    idvals <- getVec evalInt ids
    blvals <- getVec evalInt bls
    lcvals <- getVec evalInt lct
    bfvals <- getVec evalBool blf
    lblvals <- mapM (\l -> fromMaybe V.empty . V.sequence <$> mapM (evalBool m) l) labels

    let getCtrMat :: Vector (Vector (Vector a)) -> (a -> Z3 (Maybe b)) -> Z3 (Vector (Vector (Vector b)))
        getCtrMat cube f = fromMaybe V.empty . V.sequence <$> V.forM cube (\mat ->
                             V.sequence <$> V.forM mat (\row ->
                               V.sequence <$> V.forM row f))
    uvals <- getCtrMat updates (evalBool m)
    gvals <- getCtrMat guards $ (sequence <$>) <$> mapM (evalBool m)

    return $ V.zip5 idvals blvals lcvals bfvals lblvals

-- helper: return time difference between a and b
showTime a b = show ((/1000000) . fromIntegral . abs . toNanoSecs $ b-a)++"ms"

-- pretty-print the results
printRun f r = forM_ r (\(i,b,c,f,ls) -> do
  let lblids = map fst $ filter ((==True).snd) $ zip [0..] $ V.toList ls
      lbls = intercalate ", " $ map show $ catMaybes $ map (flip M.lookup isfs) lblids
      lsym = if b==0 then " " else if b==(-1) then "|" else if f then show b else "<"
      lcnt = if c>0 then show c else " "
  putStrLn $ show i ++ " " ++ lsym ++ " " ++ lcnt ++ "\t" ++ lbls
  ) where isfs = M.fromList $ map (\(a,b)->(b,a)) $ M.toList $ listAllSubformulas f

