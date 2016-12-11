module Util where
import Data.Maybe (fromJust)
import Control.Monad.IO.Class (liftIO, MonadIO)

import Data.Graph.Inductive (Gr, mkGraph)

import System.Clock

import Types
import Parse

eitherToMaybe = either (const Nothing) Just

-- | fully connected graph of size n
full :: Int -> Gr () ()
full n = mkGraph (zip [0..n-1] $ repeat ()) [(a,b,()) | a<-[0..n-1], b<-[0..n-1], a/=b]

-- | get current system time for measurments
currTime :: MonadIO m => m TimeSpec
currTime = liftIO $ getTime Monotonic

-- | print time diff. of two time measurements in milliseconds
msTimeDiff :: TimeSpec -> TimeSpec -> Double
msTimeDiff a b = (/1000000) . fromIntegral . abs . toNanoSecs $ b-a

showTime a b = show (msTimeDiff a b) ++ " ms"

bench f = do
  s <- getTime Monotonic
  putStrLn $ show f
  e <- getTime Monotonic
  return $ diffTimeSpec e s

-- unsafe REPL helpers

-- | parse formula. exception on failure, use with care
formula = fromJust . eitherToMaybe . parseFormula

-- | parse graph in dot format. exception on failure.
dotFromFile :: String -> IO (Graph Char)
dotFromFile f = readFile f >>= return . parseDot'

