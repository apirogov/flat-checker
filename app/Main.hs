module Main where
import System.IO (hSetBuffering, BufferMode(..), stdout)
import System.Directory (doesFileExist)
import Options.Applicative

import Types
import Parse
import Solve
import Util

data Args = Args { argFormula :: String
                 , argMaxSchemaSize :: Int
                 , argGraphFile :: String
                 , argLoopLens :: [Int]
                 , argVerbose :: Bool
                 }

parseArgs :: Parser Args
parseArgs = Args
        <$> option str (long "formula" <> short 'f' <> metavar "FLTL-FORMULA"
         <> help "fLTL-formula to check")
        <*> option auto (long "schema-size" <> short 'n' <> metavar "NUM"
         <> help "Defines the path-schema size" {- <> value 10 <> showDefault -} )
        <*> option str (long "graph-file" <> short 'g' <> metavar "FILE"
         <> help "File containing the graph definition" <> value "" <> showDefault)
        <*> option (eitherReader parseLoopLens) (long "loop-lens" <> short 'l' <> metavar "L1,L2,..."
         <> help "List of simple loop lengths possible in given graph (on faith!)" <> value [])
        <*> switch (long "verbose" <> short 'v' <> help "Enable verbose server log")

-- reads a directed graph from a file or stdin and checks the given formula for the specified schema size
main :: IO ()
main = do
  args <- execParser $ info (helper <*> parseArgs) fullDesc

  -- if no graph file given, read from stdin
  let filename = argGraphFile args
  filedata <- if null filename
              then Just <$> getContents
              else do
                exf <- doesFileExist filename
                if exf then Just <$> readFile filename
                       else putStrLn "Error: File does not exist." >> return Nothing

  let gg = maybe Nothing (parseGraph filename) filedata -- try .graph
  mg <- case gg of                                      -- then try .dot
            Nothing -> maybe (return Nothing) parseDot filedata
            Just gf -> return $ Just gf

  -- formula must be provided as argument
  let mf = parseFormula $ argFormula args

  case mf of
    Nothing -> putStrLn "Error: Failed parsing formula."
    Just f -> do
      case mg of
        Nothing -> putStrLn "Error: Could not load graph from file."
        Just g  -> findAndPrint g (argLoopLens args) f (argMaxSchemaSize args) (argVerbose args)

-- this is also useful in the ghci REPL
findAndPrint :: Graph Char -> [Int] -> Formula Char -> Int -> Bool -> IO ()
findAndPrint g ml f n v = do
  hSetBuffering stdout LineBuffering
  r <- findRun g ml f n v
  case r of
    Just run -> putStrLn "Solution:" >> putStrLn (showRun f run)
    Nothing -> putStrLn "No solution found."

-- unsafe REPL helper
unsafeSolve :: String -> String -> Int -> IO ()
unsafeSolve gf f n = graphFromFile gf >>= \g -> findAndPrint g [] (formula f) n True
