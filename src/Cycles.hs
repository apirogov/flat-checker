{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module Cycles (
  getCyclesWith, getCycles, getCycleLens, getCycles'
) where

import qualified Data.IntSet as IS
import qualified Data.Vector as V
import qualified Data.Sequence as SQ
import Data.Foldable (toList)

import Data.List (sort, sortOn)
import Control.Monad
import Control.Monad.State
import Control.Monad.Loops (whileM_)
import Control.Lens

import qualified Data.Graph.Inductive as G
import Graph (cyclesIn')

-- | get simple cycle lengths (not including self-loops!) using graphalyze/fgl for comparison
getCycles' :: (G.DynGraph g) => g a b -> [[Int]]
getCycles' = cyclesIn'

-- | the state is parametrised over the graph type (g a b) and the desired output type c
type JState g a b c = State (Johnson g a b c)
data Johnson g a b c = Johnson { _js :: Int    -- ^ current start node of exploration
                               , _jG :: g a b  -- ^ the (rest-)graph
                               , _jB :: V.Vector IS.IntSet
                               , _jBlocked :: V.Vector Bool
                               , _jNodeStack :: SQ.Seq Int
                               , _jCycles :: c -- ^ accumulator type for found cycles
                               }
makeLenses ''Johnson

type ReportFunc c = SQ.Seq Int -> c -> c

-- | input: graph (so selfloops or multi-edges), output: list of cycle paths
getCycles :: (G.DynGraph g) => g a b -> [[Int]]
getCycles g = reverse $ getCyclesWith g (\s c -> toList s:c) []

-- | input: graph (so selfloops or multi-edges), output: list of cycle lengths
getCycleLens :: (G.DynGraph g) => g a b -> IS.IntSet
getCycleLens g = getCyclesWith g (\s c -> IS.insert (SQ.length s) c) IS.empty

getCyclesWith :: (G.DynGraph g) => g a b -> ReportFunc c -> c -> c
getCyclesWith g f c = _jCycles $ execState (johnsonWith f) (Johnson 0 g V.empty V.empty SQ.empty c)

-- implementation of Johnson's algorithm for finding simple cycles
-- f = reporting function that takes the current nodestack (containing the cycle nodes)
-- and some container and does something with it
johnsonWith :: (G.DynGraph g) => ReportFunc c -> JState g a b c ()
johnsonWith f = do
  n <- use $ jG . to G.nodes . to length
  jBlocked .= V.replicate n False
  jB .= V.replicate n IS.empty
  js .= 0
  whileM_ ((<n-1) <$> use js) $ do
    g <- use jG
    let sccs = sortOn head $ map sort $ G.scc g
    case sccs of
      (k:_) -> do
        let s = head k -- scc can not be empty, safe
            ak = G.subgraph k g
        js .= s
        jBlocked %= \bl -> bl V.// (zip k $ repeat False)
        jB       %= \b  -> b  V.// (zip k $ repeat IS.empty)
        circuit ak s s f
        jG %= G.delNode s
        js += 1
      [] -> js .= n

-- ak = Ak (adj. list of scc containing smallest node of subgraph containing nodes [s..n-1]
-- s = current start of search
-- v = next to visit
-- rf = reporting function (if we find a cycle)
circuit :: (G.DynGraph g) => g a b -> Int -> Int -> ReportFunc c -> JState g a b c Bool
circuit ak s v rf = do
  jNodeStack %= push v
  jBlocked %= \x -> x V.// [(v, True)]                -- blocked(v) = true

  let akv = sort $ G.suc ak v
  f <- or <$> forM akv (\w -> do                      -- for w in Ak(v)
    blockedw <- use $ jBlocked . to (V.! w)
    if w==s then do
      use jNodeStack >>= \ns -> jCycles %= rf ns      --   report cycle
      return True
    else if (not blockedw) then
      circuit ak s w rf
    else
      return False
    )

  if f then
    unblock v
  else do
    forM_ akv $ \w -> do                              -- for w in Ak(v)
      bw <- use $ jB . to (V.! w)
      when (v `IS.notMember` bw) $                    --   if v not in B(w)
        jB %= \b -> b V.// [(w, IS.insert v bw)]      --     put v in B(w)

  jNodeStack %= pop
  return f
  where pop (SQ.viewr -> xs SQ.:> _) = xs
        pop x = x
        push x sq = sq SQ.|> x

unblock :: Int -> JState g a b c ()
unblock u = do
  jBlocked %= \x -> x V.// [(u, False)]               -- blocked(u) := false
  bu <- use $ jB . to (V.! u) . to IS.toList
  forM_ bu $ \w -> do                                 -- for w in B(u):
    jB %= \b -> b V.// [(u, IS.delete w $ b V.! u)]   --  delete w from B(u)
    blockedw <- use $ jBlocked . to (V.! w)
    when blockedw $ unblock w                         --  if blocked(w): unblock(w)
