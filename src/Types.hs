{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Types (
  Formula(..), enumerateSubformulas, getEvilUntils, subformulas, isLocal, simplify, simplify', formulaProps,
  Graph, LEdge, EdgeL, ConstraintOp(..), Constraint(..), Update(..),
  nodes, edges, usedProps, hasProp, realId, toEdge, edgeLabel, counters, updates, guards, splitDisjunctionGuards
) where
-- required for formula
import Data.Maybe (catMaybes, mapMaybe, fromMaybe)
import Data.Map (Map)
import Data.List (sortOn)
import qualified Data.Map as M
import Data.Data

import Control.Applicative
import Control.Monad.State
import Control.Lens.Plated
import Control.Lens.Fold
import Control.Lens.TH

-- required for graph
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive (Gr, LEdge)

data ConstraintOp = CLt | CLe | CEq | CGe | CGt deriving (Eq, Ord, Data)

instance Show ConstraintOp where
  show x | x==CLt = " < "  | x==CLe = " <= " | x==CEq = " = "
         | x==CGe = " >= " | x==CGt = " > "  | otherwise = ""

-- | universal linear constraint representation
data Constraint a = Constraint [(Integer,a)] ConstraintOp Integer deriving (Eq, Ord, Data)

instance Show a => Show (Constraint a) where
  show (Constraint xs op c) = lincomb ++ show op ++ show c
    where lincomb = dropWhile (=='+') $ concatMap (\(a,v) -> showNum a ++ show v) xs
          showNum x | x < 0 = show x | otherwise = '+':show x

-- | AST of an fcLTL formula. Until has an optional constraint [Σ a_i·φ_i OP c]
data Formula a = Tru | Fls | Prop a
               | And (Formula a) (Formula a) | Or (Formula a) (Formula a)
               | Not (Formula a) | Next (Formula a)
               | Until (Maybe (Constraint (Formula a))) (Formula a) (Formula a)
               deriving (Eq,Ord,Data)

instance Data a => Plated (Formula a)
makePrisms ''Formula

-- | custom Show instance for prettyprinting. same format is accepted by parseFormula
instance Show a => Show (Formula a) where
  show Tru = "true"
  show Fls = "false"
  show (Prop p) = if c == '\'' || c=='\"' then init $ tail $ show p else show p
    where c = head (show p)
  show (Not (Until c Tru (Not g))) = "G"++maybeShowConstraint c++show g
  show (Not (Until c (Not Fls) (Not g))) = "G"++maybeShowConstraint c++show g
  show (Not (Until c (Not f) (Not g))) = "("++show f++"R"++maybeShowConstraint c++show g++")"
  show (Not f) = "~"++show f
  show (Next f) = "X"++show f
  show (And f g) = "("++show f ++ "&" ++ show g++")"
  show (Or f g) = "("++show f ++ "|" ++ show g++")"
  show (Until c Tru g) = "F"++maybeShowConstraint c++show g
  show (Until c f g) = "("++show f++"U"++maybeShowConstraint c++show g++")"

maybeShowConstraint :: Show a => Maybe (Constraint a) -> String
maybeShowConstraint Nothing = ""
maybeShowConstraint (Just c) = "[" ++ show c ++ "]"

type CollectState a = State (Int, Map (Formula a) Int) ()
-- | collect all unique subformulas and assign them numbers
addFormula :: Ord a => Formula a -> CollectState a
addFormula f = modify addIfNew
  where addIfNew old@(currid, subfs) | f `M.member` subfs = old
                                     | otherwise = (currid+1, M.insert f currid subfs)

-- | post-order traversal collecting all subformulas
enumerateSubformulas :: (Ord a,Data a) => Formula a -> Map (Formula a) Int
enumerateSubformulas = snd . (`execState` (0,M.empty)) . go
  where go f@(Until (Just _) g h) = traverseOf_ plate go f
        -- to label constraint until correctly, we also need the normal one!
                                  *> addFormula (Until Nothing g h) *> addFormula f
        go f                      = traverseOf_ plate go f *> addFormula f

-- | filter out the U-subformulas only
getEvilUntils :: (Ord a) => Map (Formula a) Int -> Map (Formula a) Int
getEvilUntils = M.fromList . flip zip [0..] . filter evil . filter (has _Until)
              . map fst . sortOn snd . M.toList
  where evil (Until Nothing _ _) = False
        evil _ = True

-- | given all existing subformulas and a formula, tell its direct deps
subformulas :: (Ord a,Data a) => Map (Formula a) Int -> Formula a -> [Int]
subformulas msubf f = catMaybes $ flip M.lookup msubf <$> children f

-- | can this formula be evaluated by simple lookup?
isLocal :: Data a => Formula a -> Bool
isLocal = any (\f -> has _Next f || has _Until f) . universe

-- reorder if possible
normalize :: (Ord a) => Formula a -> Formula a
normalize (And f g) | f' == g' = f' | f' < g' = And f' g' | otherwise = And g' f'
  where (f',g') = (normalize f, normalize g)
normalize (Or f g) | f' == g' = f' | f' < g' = Or f' g' | otherwise = Or g' f'
  where (f',g') = (normalize f, normalize g)
-- can't swap anything
normalize (Until c f g) = Until c (normalize f) (normalize g)
normalize (Next f) = Next $ normalize f
normalize (Not  f) = Not  $ normalize f
normalize f = f

simplify' f = obtain $ takeWhile (uncurry (/=)) $ zip fs $ tail fs
  where fs = iterate (simplify . normalize) f
        obtain [] = f
        obtain (x:_) = snd x

-- | simplify formula by reducing number of AST elements (negations, triviality...)
simplify :: (Ord a) => Formula a -> Formula a
-- GGp = Gp
simplify (Not (Until Nothing Tru (Not (Not (Until Nothing Tru (Not f)))))) =
  simplify $ Not (Until Nothing Tru (Not f))
-- FFp = Fp
simplify (Until Nothing Tru (Until Nothing Tru f)) = simplify $ Until Nothing Tru f

-- Fp | Fq = F(p | q)
simplify (Or (Until Nothing Tru f) (Until Nothing Tru g)) =
  simplify $       Until Nothing Tru $       Or  f g
-- Gp & Gq = G(p & q)
simplify (And (Not (Until Nothing Tru (Not f))) (Not (Until Nothing Tru (Not g)))) =
  simplify $ Not $ Until Nothing Tru $ Not $ And f g

-- DeMorgan ~(~p & ~q) = (p | q), ~(~p | ~q) = (p & q)
simplify (Not (Not (And (Not f) (Not g)))) = simplify $ Not $ Or  f g
simplify (Not (Not (Or  (Not f) (Not g)))) = simplify $ Not $ And f g
simplify (Not (And (Not f) (Not g))) = simplify (Or  f g)
simplify (Not (Or  (Not f) (Not g))) = simplify (And f g)

-- ~Xp = X~p and distributivity
simplify (Not (Next f)) = Next $ simplify $ Not f
simplify (Or      (Next f) (Next g)) = Next $ simplify $ Or      f g
simplify (And     (Next f) (Next g)) = Next $ simplify $ And     f g
simplify (Until c (Next f) (Next g)) = Next $ simplify $ Until c f g

-- trivial cases
simplify (Not (Not f)) = simplify f
simplify (Or Fls f) = simplify f
simplify (Or f Fls) = simplify f
simplify (And Tru f) = simplify f
simplify (And f Tru) = simplify f
simplify (Or Tru _) = Tru
simplify (Or _ Tru) = Tru
simplify (And Fls _) = Fls
simplify (And _ Fls) = Fls
simplify (Not Tru) = Fls
simplify (Not Fls) = Tru
simplify (Next Tru) = Fls
simplify (Next Fls) = Tru
simplify (Until _ _ Fls) = Fls
simplify (Until Nothing _ Tru) = Tru

-- push through
simplify (Until c f g) = Until c (simplify f) (simplify g)
simplify (Next f)  = Next $ simplify f
simplify (Not f)   = Not  $ simplify f
simplify (Or  f g) = Or  (simplify f) (simplify g)
simplify (And f g) = And (simplify f) (simplify g)
simplify (Prop p)  = Prop p
simplify Tru = Tru
simplify Fls = Fls

formulaProps :: (Data a, Ord a) => Formula a -> [a]
formulaProps f = mapMaybe (getProp . fst) $ M.toList $ enumerateSubformulas f
  where getProp (Prop p) = Just p
        getProp _ = Nothing

-- | represents counter update for a variable annotated at an edge
data Update b = UpdateInc b Integer | UpdateEq b Integer deriving (Show, Eq, Ord)

-- | edges can be labelled with linear combinations of counters >=(true) / <(false) some value
--  and an increment for each counter can be provided
type EdgeL b = Either [Constraint b] (Update b)

-- | atomic propositions indexed by a, counters indexed by b, start node always has id 0
-- constraint guards are in DNF, each inner list is a monome
-- nodes labelled with prop subsets and potential original copy of node (for bookkeeping)
type Graph a b = Gr (Set a, Maybe G.Node) [EdgeL b]

-- | has node n of graph gr the atomic proposition p?
hasProp :: (Ord a) => Graph a b -> a -> Int -> Bool
hasProp gr p n = case G.lab gr n of
  Nothing -> False
  Just ps -> S.member p $ fst ps

-- | propositions used in graph
usedProps :: (Ord a) => Graph a b -> Set a
usedProps g = S.unions . map fst . mapMaybe (G.lab g) $ nodes g

-- | if this node is a clone, return id of its original copy (for the user output)
realId :: Graph a b -> Int -> Int
realId gr n = case G.lab gr n of
  Nothing -> n
  Just l -> fromMaybe n $ snd l

-- | filter out the updates stored at an edge
updates :: (Ord b) => [EdgeL b] -> Map b (Update b)
updates xs = M.fromList $ mapMaybe getUpdate xs
  where getUpdate (Right (UpdateInc b i)) = Just (b, UpdateInc b i)
        getUpdate (Right (UpdateEq  b i)) = Just (b, UpdateEq  b i)
        getUpdate _ = Nothing

-- | filter out the guards stored at an edge, repacked in a tuple
guards :: [EdgeL b] -> [(ConstraintOp, ([(Integer,b)], Integer))]
guards xs = catMaybes $ concatMap getGuard xs
  where getGuard (Left (Constraint vs op c : cs)) = Just (op, (vs, c)) : getGuard (Left cs)
        getGuard _ = [Nothing]

-- | specialized for reexport
nodes :: Graph a b -> [Int]
nodes = G.nodes

-- | specialized for reexport
edges :: Graph a b -> [LEdge [EdgeL b]]
edges = G.labEdges

-- | specialized for reexport
edgeLabel :: LEdge [EdgeL b] -> [EdgeL b]
edgeLabel = G.edgeLabel

-- | specialized for reexport
toEdge :: LEdge [EdgeL b] -> (Int,Int)
toEdge = G.toEdge

-- | return a list of all counters used in given graph
counters :: (Ord b) => Graph a b -> [b]
counters gr = S.toList $ S.fromList $ concatMap (concatMap extract . G.edgeLabel) $ G.labEdges gr
  where extract (Right (UpdateInc b _)) = [b]
        extract (Right (UpdateEq  b _)) = [b]
        extract (Left (Constraint xs _ _:cs)) = map snd xs ++ extract (Left cs)
        extract (Left []) = []

-- | convert edges with multiple sets of guards (disjunction) to single edges (results in multigraph!)
splitDisjunctionGuards :: Graph a b -> Graph a b
splitDisjunctionGuards g = execState (mapM splitEdges $ edges g) g

cloneNode :: G.Node -> State (Graph a b) G.Node
cloneNode n = do
  g <- get
  let (_, ub) = G.nodeRange g
  let n' = succ ub
  -- NOTE: we dont need to copy incoming edges, does not matter which copy is visited
  let outes = map (\(_,b,c) -> (n',b,c)) $ G.out g n
  case G.lab g n of
    Nothing -> error "something went wrong, node not labelled!"
    Just (ps,orig) -> do
      put $ G.insEdges outes $ G.insNode (n', (ps, orig <|> Just n)) g
      return n'

-- | clone edges for each case of disjunction, keep same updates
splitEdges :: LEdge [EdgeL b] -> State (Graph a b) ()
splitEdges (a,b,l) = do
  let (grds, upd) = separate l
  case grds of
    [] -> return ()
    [_] -> return ()
    (g:gs) -> do
      put =<< G.insEdge (a,b,map Right upd ++ [Left g]) . G.delEdge (a,b) <$> get
      mapM_ (\gg -> cloneNode b >>= (\n -> put =<< G.insEdge (a, n, map Right upd ++ [Left gg]) <$> get)) gs

-- | separate guard monomes and updates
separate :: [EdgeL b] -> ([[Constraint b]], [Update b])
separate = foldl getGuard ([],[])
  where getGuard (g,u) (Left x)  = (x:g, u)
        getGuard (g,u) (Right x) = (g, x:u)
