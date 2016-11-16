{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Lib where
import Data.Maybe (catMaybes)
import Data.Ratio
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (sortOn)
import Data.Data
import Control.Monad.State
import Control.Lens.Plated
import Control.Lens.Fold
import Control.Lens.TH

import Data.Vector (Vector)
import qualified Data.Vector as V

-- Until ratios allowed: 0 < r <= 1
data Formula a = Prop a | And (Formula a) (Formula a) | Or (Formula a) (Formula a)
               | Not (Formula a) | Next (Formula a) | Until (Ratio Int) (Formula a) (Formula a)
               deriving (Eq,Ord,Data)
until1 = Until 1 --normal until

instance Data a => Plated (Formula a)
makePrisms ''Formula

-- custom Show instance for prettyprinting
instance Show a => Show (Formula a) where
  show (Prop p) = if c == '\'' || c=='\"' then init $ tail $ show p else show p
    where c = head (show p)
  show (Not f) = "~"++show f
  show (Next f) = "X"++show f
  show (And f g) = "("++show f ++ "&" ++ show g++")"
  show (Or f g) = "("++show f ++ "|" ++ show g++")"
  show (Until r f g) = "("++show f++"U"++rat++show g++")"
    where rat = if r<1 then "["++show (numerator r)++"/"++show (denominator r)++"]" else ""

-- TODO: write parser with parsec?

type CollectState a = State (Int, Map (Formula a) Int) ()
addFormula :: Ord a => Formula a -> CollectState a
addFormula f = modify addIfNew
  where addIfNew old@(currid, subfs) | f `M.member` subfs = old
                                     | otherwise = (currid+1, M.insert f currid subfs)

-- post-order traversal collecting all subformulas
listAllSubformulas :: (Ord a,Data a) => Formula a -> Map (Formula a) Int
listAllSubformulas = snd . (flip execState (0,M.empty)) . go
  where go f = traverseOf_ plate go f *> addFormula f

-- filter out the U-subformulas only
getEvilUntils :: (Ord a,Data a) => Formula a -> Map (Formula a) Int
getEvilUntils = M.fromList . flip zip [0..] . filter evil . filter (has _Until) . universe
  where evil (Until 1 _ _) = False
        evil _ = True

-- given all existing subformulas and a formula, tell its direct deps
subformulas :: (Ord a,Data a) => Map (Formula a) Int -> Formula a -> [Int]
subformulas msubf f = catMaybes $ flip M.lookup msubf <$> children f

-- can this formula be evaluated by simple lookup?
isLocal :: Data a => Formula a -> Bool
isLocal = not . or . map (\f -> has _Next f || has _Until f) . universe

type Graph a = Vector (Set a, Vector Int)

-- a directed adj. list for kripke structure graph, start node implicitly has id 0
readGraph :: Ord a => [([a],[Int])] -> Graph a
readGraph l = V.fromList $ map (\(ps,ns) -> (S.fromList ps, V.fromList ns)) l

-- is there an edge from i to j in g?
hasEdge :: Graph a -> (Int,Int) -> Bool
g `hasEdge` (i,j) = j `V.elem` next g i

-- return the vertex ids
nodes :: Graph a -> [Int]
nodes g = [0..length g-1]
-- return a complete list of edges
edges :: Graph a -> [(Int,Int)]
edges g = concatMap (\(i,l)->zip (replicate (length l) i) l)
        $ zip [0..(length g - 1)] $ V.toList $ fmap (V.toList.snd) g

-- does vertex i of g contain p as proposition?
hasProp g i p = p `S.member` props g i
-- propositions of vertex i of graph g
props g i = fst $ g V.! i
-- successors of vertex i of graph g
next g i = snd $ g V.! i

