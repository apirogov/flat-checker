{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Types (
  Formula(..), enumerateSubformulas, getEvilUntils, subformulas, isLocal,
  Graph, toGraph, nodes, edges, hasEdge, hasProp, props, next,
  calcValidCycleLengths, kripke2fgl
) where
-- required for formula
import Data.Maybe (catMaybes)
import Data.Ratio
import Data.Map (Map)
import Data.List (sortOn)
import qualified Data.Map as M
import Data.Data

import Control.Monad.State
import Control.Lens.Plated
import Control.Lens.Fold
import Control.Lens.TH

-- required for graph
import qualified Data.Set as S
import qualified Data.IntSet as IS
import qualified Data.Vector as V
import Data.Set (Set)
import Data.IntSet (IntSet)
import Data.Vector (Vector)

import qualified Data.Graph.Inductive as G
import Cycles

-- Until ratios allowed: 0 < r <= 1
data Formula a = Tru | Fls | Prop a | And (Formula a) (Formula a) | Or (Formula a) (Formula a)
               | Not (Formula a) | Next (Formula a) | Until (Ratio Int) (Formula a) (Formula a)
               deriving (Eq,Ord,Data)

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

showRat :: Ratio Int -> [Char]
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

hasSelfloops = any (\(i,j) -> i==j) . edges

calcValidCycleLengths :: Graph a -> [Int]
calcValidCycleLengths g = IS.elems . (if hasSelfloops g then IS.insert 2 else id) . getCycleLens $ kripke2fgl g

-- helper: drop labels, remove selfloops. no multiloops anyway as input are adj. sets
kripke2fgl :: Graph a -> G.Gr () ()
kripke2fgl g = G.mkGraph (zip (nodes g) $ repeat ()) $ map (\(i,j) -> (i,j,())) $ filter (\(i,j) -> i/=j) $ edges g
