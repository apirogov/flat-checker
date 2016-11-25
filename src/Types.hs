{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Types (
  Formula(..), until1, getUFrac, enumerateSubformulas, getEvilUntils, subformulas, isLocal,
  Graph, toGraph, nodes, edges, hasEdge, hasProp, props, next, calcValidCycleLengths
) where
import Data.Maybe (catMaybes)
import Data.Ratio
import Data.Map (Map)
import Data.Set (Set)
import Data.IntSet (IntSet)
import Data.List (sortOn, nub)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntSet as IS
import Data.Data
import Control.Monad.State
import Control.Lens.Plated
import Control.Lens.Fold
import Control.Lens.TH

import Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.Graph.Inductive as G
import Graph

-- Until ratios allowed: 0 < r <= 1
data Formula a = Tru | Fls | Prop a | And (Formula a) (Formula a) | Or (Formula a) (Formula a)
               | Not (Formula a) | Next (Formula a) | Until (Ratio Int) (Formula a) (Formula a)
               deriving (Eq,Ord,Data)
until1 = Until 1 --normal until, for convenient infix usage

-- extract associated fraction
getUFrac (Until r _ _) = Just (numerator r, denominator r)
getUFrac _ = Nothing

instance Data a => Plated (Formula a)
makePrisms ''Formula

-- custom Show instance for prettyprinting. same format is accepted by parseFormula
instance Show a => Show (Formula a) where
  show Tru = "1"
  show Fls = "0"
  show (Prop p) = if c == '\'' || c=='\"' then init $ tail $ show p else show p
    where c = head (show p)
  show (Not (Until r Tru (Not g))) = "G"++showRat r++show g
  show (Not f) = "~"++show f
  show (Next f) = "X"++show f
  show (And f g) = "("++show f ++ "&" ++ show g++")"
  show (Or f g) = "("++show f ++ "|" ++ show g++")"
  show (Until r Tru g) = "F"++showRat r++show g
  show (Until r f g) = "("++show f++"U"++showRat r++show g++")"

showRat r = if r<1 then "["++show (numerator r)++"/"++show (denominator r)++"]" else ""

type CollectState a = State (Int, Map (Formula a) Int) ()
addFormula :: Ord a => Formula a -> CollectState a
addFormula f = modify addIfNew
  where addIfNew old@(currid, subfs) | f `M.member` subfs = old
                                     | otherwise = (currid+1, M.insert f currid subfs)

-- post-order traversal collecting all subformulas
enumerateSubformulas :: (Ord a,Data a) => Formula a -> Map (Formula a) Int
enumerateSubformulas = snd . (flip execState (0,M.empty)) . go
  where go f = traverseOf_ plate go f *> addFormula f

-- filter out the U-subformulas only
getEvilUntils :: (Ord a) => Map (Formula a) Int -> Map (Formula a) Int
getEvilUntils = M.fromList . flip zip [0..] . filter evil . filter (has _Until)
              . map fst . sortOn snd . M.toList
  where evil (Until 1 _ _) = False
        evil _ = True

-- given all existing subformulas and a formula, tell its direct deps
subformulas :: (Ord a,Data a) => Map (Formula a) Int -> Formula a -> [Int]
subformulas msubf f = catMaybes $ flip M.lookup msubf <$> children f

-- can this formula be evaluated by simple lookup?
isLocal :: Data a => Formula a -> Bool
isLocal = not . or . map (\f -> has _Next f || has _Until f) . universe

-- a graph is just a adj. list decorated with proposition sets
type Graph a = Vector (Set a, IntSet)

-- a directed adj. list for kripke structure graph, start node implicitly has id 0
toGraph :: Ord a => [([a],[Int])] -> Graph a
toGraph l = V.fromList $ map (\(ps,ns) -> (S.fromList ps, IS.fromList ns)) l

-- is there an edge from i to j in g?
hasEdge :: Graph a -> (Int,Int) -> Bool
g `hasEdge` (i,j) = j `IS.member` next g i

-- return the vertex ids
nodes :: Graph a -> [Int]
nodes g = [0..length g-1]
-- return a complete list of edges
edges :: Graph a -> [(Int,Int)]
edges g = concatMap (\(i,l)->zip (replicate (length l) i) l)
        $ zip [0..(length g - 1)] $ V.toList $ fmap (IS.toList . snd) g

-- does vertex i of g contain p as proposition?
hasProp g i p = p `S.member` props g i
-- propositions of vertex i of graph g
props g i = fst $ g V.! i
-- successors of vertex i of graph g
next g i = snd $ g V.! i

calcValidCycleLengths :: Graph a -> [Int]
calcValidCycleLengths g = if hasSelfloops then nub (2:llens) else llens -- selfloops must be unrolled to loops of size 2
  where g' = G.mkGraph (zip (nodes g) (repeat ())) (map (\(i,j) -> (i,j,())) (edges g)) :: G.Gr () ()
        llens = S.toList $ S.fromList $ map length $ cyclesIn' g'
        hasSelfloops = any (\(i,j) -> i==j) (edges g)

-- Tarjans algorithm for finding all cycles in digraph, based on https://github.com/josch/cycles_tarjan/
-- TODO: implement Johnson from https://blog.mister-muffin.de/2012/07/04/enumerating-elementary-circuits-of-a-directed_graph/
{-
data TarjanState a = TarjanState { tsG :: Vector IntSet, tsPointStack :: SQ.Seq Int, tsMarked :: Vector Bool, tsMarkedStack :: SQ.Seq Int, tsLens :: S.Set Int }

calcSimpleCycleLengths :: Graph a -> [Int]
calcSimpleCycleLengths g = toList $ tsLens $ execState (
  forM [0..length g-1] (\i -> do      -- for s in range(len(A)):
  ret <- backtrack i i                -- backtrack(s)
  ms <- toList <$> gets tsMarkedStack -- while marked_stack: u = marked_stack.pop(); marked[u] = False
  modify (\s -> s{tsMarked=tsMarked s V.// (zip ms (repeat False)), tsMarkedStack=SQ.empty})
  return ret)) emptyTarjanState
  -- at start: for i in range(len(A)): marked[i] = False, stacks empty
  where emptyTarjanState = (TarjanState (fmap snd g) SQ.empty (V.replicate (length g) False) SQ.empty (S.singleton 1))

backtrack :: Int -> Int -> State (TarjanState a) Bool
backtrack st v = do
  trace ("backtrack "++show st++" " ++show v) (return ())
  modify (\s -> s{tsPointStack=tsPointStack s SQ.|> v})   -- point_stack.push(v)
  modify (\s -> s{tsMarked=tsMarked s V.// [(v,True)]})   -- marked[v] = True
  modify (\s -> s{tsMarkedStack=tsMarkedStack s SQ.|> v}) -- point_stack.push(v)
  g <- gets tsG
  marked <- gets tsMarked
  f <- or <$> forM (IS.toList $ g V.! v) (\w ->
    if w < st then do
      g <- gets tsG
      modify (\s -> s{tsG=g V.// [(v, IS.delete w $ (g V.! v))]})
      return False
    else if w==st then do
      ps <- gets tsPointStack
      modify (\s -> s{tsLens = S.insert (length ps) $ tsLens s}) -- print point_stack / output cycle
      trace (show ps) (return ())
      return True
    else if not $ marked V.! w then
      backtrack st w
    else
      return False
    )
  when f $ do -- if f, pop and unmark until and including v
    (keep,remove) <- SQ.breakl (/=v) <$> gets tsMarkedStack
    modify (\s -> s{tsMarked=tsMarked s V.// (zip (toList remove) (repeat False)), tsMarkedStack=keep})
    return ()
  return f
-}
