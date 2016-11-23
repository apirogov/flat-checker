module Main where
import System.IO (hSetBuffering, BufferMode(..), stdout)
import System.Directory (doesFileExist)
import Options.Applicative

import Data.Ratio

import Types
import Parse
import Solve

data Args = Args { argFormula :: String
                 , argMaxSchemaSize :: Int
                 , argGraphFile :: String
                 , argVerbose :: Bool
                 }

parseArgs :: Parser Args
parseArgs = Args
        <$> option str (long "formula" <> short 'f' <> metavar "FLTL-FORMULA"
         <> help "fLTL-formula to check")
        <*> option auto (long "schema-size" <> short 'n' <> metavar "NUM"
         <> help "Defines the path-schema size" {- <> value 10 <> showDefault -} )
        <*> option str (long "graph-file" <> short 'f' <> metavar "FILE"
         <> help "File containing the graph definition" <> value "" <> showDefault)
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
  let mg = maybe Nothing (parseGraph filename) filedata

  -- formula must be provided as argument
  let mf = parseFormula $ argFormula args

  case mf of
    Nothing -> putStrLn "Error: Failed parsing formula."
    Just f -> do
      case mg of
        Nothing -> putStrLn "Error: Could not load graph from file."
        Just g  -> findAndPrint g f (argMaxSchemaSize args)

-- this is also useful in the ghci REPL
findAndPrint :: Graph Char -> Formula Char -> Int -> IO ()
findAndPrint g f n = do
  hSetBuffering stdout LineBuffering
  r <- findRun g f n
  case r of
    Just run -> printRun f run
    Nothing -> putStrLn "No solution found."
