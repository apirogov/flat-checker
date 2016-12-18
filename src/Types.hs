{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}
module Types (
  Formula(..), enumerateSubformulas, getEvilUntils, subformulas, isLocal,
  Graph, LEdge, EdgeL(..), GuardOp(..), nodes, edges, hasProp, toEdge, edgeLabel, counters, updates, guards
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
import Data.Set (Set)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive (Gr, LEdge)

-- | AST of an fLTL formula. Until ratios allowed: 0 < r <= 1
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

-- | post-order traversal collecting all subformulas
enumerateSubformulas :: (Ord a,Data a) => Formula a -> Map (Formula a) Int
enumerateSubformulas = snd . (flip execState (0,M.empty)) . go
  where go f = traverseOf_ plate go f *> addFormula f

-- | filter out the U-subformulas only
getEvilUntils :: (Ord a) => Map (Formula a) Int -> Map (Formula a) Int
getEvilUntils = M.fromList . flip zip [0..] . filter evil . filter (has _Until)
              . map fst . sortOn snd . M.toList
  where evil (Until 1 _ _) = False
        evil _ = True

-- | given all existing subformulas and a formula, tell its direct deps
subformulas :: (Ord a,Data a) => Map (Formula a) Int -> Formula a -> [Int]
subformulas msubf f = catMaybes $ flip M.lookup msubf <$> children f

-- | can this formula be evaluated by simple lookup?
isLocal :: Data a => Formula a -> Bool
isLocal = not . or . map (\f -> has _Next f || has _Until f) . universe

-- | edges can be labelled with linear combinations of counters >=(true) / <(false) some value
--  and an increment for each counter can be provided
data GuardOp = GuardLt | GuardLe | GuardEq | GuardGe | GuardGt deriving (Show, Eq, Ord)
data EdgeL b = Guard [(Integer,b)] GuardOp Integer | UpdateInc b Integer deriving (Show)

-- | atomic propositions indexed by a, counters indexed by b, start node always has id 0
type Graph a b = Gr (Set a) [EdgeL b]

-- | has node n of graph gr the atomic proposition p?
hasProp :: (Ord a) => Graph a b -> a -> Int -> Bool
hasProp gr p n = case G.lab gr n of
  Nothing -> False
  Just ps -> S.member p ps

-- | filter out the updates stored at an edge
updates :: (Ord b) => [EdgeL b] -> Map b Integer
updates xs = M.fromList $ catMaybes $ map getUpdate xs
  where getUpdate (UpdateInc b i) = Just (b,i)
        getUpdate _ = Nothing

-- | filter out the GE guards stored at an edge, repacked in a tuple (neg.,([lin.comb.], const.))
--   LT guards are GE guards with neg. flag = True
guards :: [EdgeL b] -> [(GuardOp, ([(Integer,b)], Integer))]
guards xs = catMaybes $ map getGuard xs
  where getGuard (Guard vs op c) = Just (op, (vs, c))
        getGuard _ = Nothing

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
  where extract (UpdateInc b _) = [b]
        extract (Guard xs _ _) = map snd xs
