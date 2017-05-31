{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-type-defaults #-}
module Bench where
import Data.Maybe (fromJust)
import qualified Data.Set as S
import qualified Data.Graph.Inductive as G
import Text.Show.Functions ()

import Types
import Parse
import Solve

-- | some orphan instances for tests in GHCI
instance Show Run where
  show _ = "<run>"
deriving instance Show Response

-- | parse formula. exception on failure, use with care
formula :: String -> Formula String
formula = fromJust . either (const Nothing) Just . parseFormula

-- | parse graph in dot format. exception on failure.
dotFromFile :: FilePath -> IO (Graph String String)
dotFromFile f = readFile f >>= return . parseDot'


-- | for interactive repl use, can throw errors
solve :: Graph String String -> String -> Int -> IO Response
solve g f n = findRun (defaultSolveConf (formula f) n){slvDebug=True} g

-- | same, but graph from given file name
solve' :: String -> String -> Int -> IO Response
solve' gf f n = dotFromFile gf >>= \g -> solve g f n

-- | given response, print it
printRun :: Response -> IO ()
printRun r = putStrLn $ rShow r Nothing

-- parametrized tests --

-- benchmark loop length search
solveLoopLens m n = solve (full m) "true" n

-- should always succeed to find way through tree
solveBinEasy n = solve (binary n) (replicate (n'+2) 'X' ++ "G(~p&q)")  $ n'+6
  where n' = ceiling $ log $ fromIntegral n

-- should always fail
solveBinEasy' n = solve (binary n) (replicate (n'+2) 'X' ++ "G(~p&r)")  $ n'+6
  where n' = ceiling $ log $ fromIntegral n

-- graphs --

-- | fully connected graph of size n (e.g. to benchmark cycle search)
full :: Int -> Graph String String
full n = G.mkGraph (map (\x -> (x,(S.singleton $ "p"++show x,Nothing))) [0..n-1])
                   [(a,b,[]) | a<-[0..n-1], b<-[0..n-1], a/=b]

-- | binary tree with n nodes and self-loop on rightmost leaf
binary :: Int -> Graph String String
binary n = G.mkGraph ((n-1, (S.fromList ["q"],Nothing)):(map (\x -> (x,(S.singleton "p",Nothing))) $ init ns))
         $  [(a,b,[]) | a<-ns, b<-ns, b==2*a+1]
         ++ [(a,b,[]) | a<-ns, b<-ns, b==2*a+2]
         ++ [(n-1, n-1, [])]
  where ns = [0..n-1]
