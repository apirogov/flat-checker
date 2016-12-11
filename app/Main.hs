module Main where
import System.IO (hSetBuffering, BufferMode(..), stdout)
import System.Directory (doesFileExist)
import Options.Applicative

import Types
import Parse
import Solve
import Util

-- | applicative parser for the args given on the command line
confFromArgs :: Parser SolveConf
confFromArgs = SolveConf
  <$> option (eitherReader parseFormula) (long "formula" <> short 'f' <> metavar "FLTL-FORMULA"
    <> help "fLTL-formula to check")
  <*> option auto (long "schema-size" <> short 'n' <> metavar "NUM"
    <> help "Defines the path-schema size")
  <*> option str (long "graph-file" <> short 'g' <> metavar "FILE"
    <> help "File containing the graph definition" <> value "" <> showDefault)
  <*> option (eitherReader parseLoopLens) (long "loop-lens" <> short 'l' <> metavar "L1,L2,..."
    <> help "List of simple loop lengths possible in given graph (on faith!)" <> value [])
  <*> switch (long "use-int-ids" <> short 'i' <> help "Use ints for node ids")
  <*> switch (long "use-bool-lt" <> short 'b' <> help "Use bools for loop types")
  <*> switch (long "verbose" <> short 'v' <> help "Enable verbose server log")

-- | given filename, try to load in one of the supported formats or fail
readGraph :: String -> IO (Graph Char)
readGraph filename = do
  filedata <- if null filename --if no graph file given, read from stdin
              then Just <$> getContents
              else do
                exf <- doesFileExist filename
                if exf then Just <$> readFile filename
                       else putStrLn "Error: File does not exist." >> return Nothing
  mg <- maybe (return Nothing) parseDot filedata
  case mg of
    Nothing -> error "Error: Could not load graph from file."
    Just g  -> return g

-- | reads a directed graph from a file or stdin and checks the given formula for the specified schema size
main :: IO ()
main = do
  conf <- execParser $ info (helper <*> confFromArgs) fullDesc
  g <- readGraph $ slvGraphFile conf
  findAndPrint conf g

-- | check some formula on some graph This can also be used in ghci
findAndPrint :: SolveConf -> Graph Char -> IO ()
findAndPrint conf g = do
  hSetBuffering stdout LineBuffering
  r <- findRun conf g
  case r of
    Just run -> putStrLn "Solution:" >> putStrLn (showRun (slvFormula conf) run)
    Nothing -> putStrLn "No solution found."

-- | unsafe REPL helper. tries to load graph, parse formula and solve. can throw exceptions
unsafeSolve :: String -> String -> Int -> IO ()
unsafeSolve gf f n = dotFromFile gf >>= \g -> findAndPrint (defaultSolveConf (formula f) n) g
