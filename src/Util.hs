module Util where
import Data.Maybe (fromJust)
import Control.Monad.IO.Class (liftIO, MonadIO)

import qualified Data.Graph.Inductive as G

import System.Clock

import Types
import Parse

full :: Int -> G.Gr () ()
full n = G.mkGraph (zip [0..n-1] $ repeat ()) [(a,b,()) | a<-[0..n-1], b<-[0..n-1], a/=b]

currTime :: MonadIO m => m TimeSpec
currTime = liftIO $ getTime Monotonic

 -- print time diff. of a and b
msTimeDiff a b = (/1000000) . fromIntegral . abs . toNanoSecs $ b-a

bench f = do
  s <- getTime Monotonic
  putStrLn $ show f
  e <- getTime Monotonic
  return $ diffTimeSpec e s

-- unsafe REPL helpers

formula = fromJust . parseFormula

graphFromFile :: String -> IO (Graph Char)
graphFromFile f = readFile f >>= return . fromJust . parseGraph f

dotFromFile :: String -> IO (Graph Char)
dotFromFile f = readFile f >>= return . parseDot'

