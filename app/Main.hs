{-# LANGUAGE TemplateHaskell #-}
module Main where
import Data.Data (Data)
import Data.Time (getCurrentTime)
import Language.Haskell.TH (stringE, runIO)
import System.IO (hSetBuffering, BufferMode(..), stdout)
import System.Console.Terminal.Size (size, width)
import System.Directory (doesFileExist)
import Development.GitRev (gitBranch, gitHash, gitDirty)
import Options.Applicative

import Types
import Parse
import Solve

-- | applicative parser for the args given on the command line
confFromArgs :: Parser (SolveConf String String)
confFromArgs = SolveConf
  <$> option (eitherReader ((simplify' <$>) . parseFormula)) (long "formula" <> short 'f' <> metavar "LTL-FORMULA"
    <> help "fLTL-formula to check")
  <*> option auto (long "schema-size" <> short 'n' <> metavar "NUM"
    <> help "Defines the path-schema size")
  <*> option str (long "graph-file" <> short 'g' <> metavar "FILE"
    <> help "File containing the graph definition" <> value "" <> showDefault)
  <*> option (eitherReader parseLoopLens) (long "loop-lens" <> short 'l' <> metavar "L1,L2,..."
    <> help "List of simple loop lengths possible in given graph (on faith!)" <> value [])
  <*> switch (long "use-int-ids" <> short 'i' <> help "Use ints for node ids")
  <*> switch (long "use-bool-lt" <> short 'b' <> help "Use bools for loop types")
  <*> switch (long "search" <> short 's' <> help "Iteratively try to find run up to given max size")
  <*> switch (long "minimal" <> short 'm' <> help "Implies -s, ensures that the schema size is minimal")
  <*> switch (long "verbose" <> short 'v' <> help "Enable verbose log")
  <*> switch (long "debug" <> short 'd' <> help "Show debugging messages")

-- | given filename, try to load in one of the supported formats or fail
readGraph :: String -> IO (Graph String String)
readGraph filename = do
  filedata <- if null filename -- if no graph file given, read from stdin
              then Just <$> getContents
              else do
                exf <- doesFileExist filename
                if exf then Just <$> readFile filename
                       else putStrLn "Error: File does not exist." >> return Nothing
  mg <- maybe (return Nothing) parseDot filedata
  case mg of
    Nothing -> error "Error: Could not load graph from file."
    Just g  -> return g

-- | check some formula on some graph.
findAndPrint :: (Data a, Ord a, Ord b, Show a, Show b) => SolveConf a b -> Graph a b -> IO ()
findAndPrint conf g = do
  hSetBuffering stdout LineBuffering  -- we want to see progress immediately
  w <- fmap width <$> size            -- obtain terminal width for pretty-printing
  r <- findRun conf g
  putStrLn $ maybe "No solution found." (const $ "Solution:\n" ++ rShow r w) $ rRun r

-- | reads a directed graph from a file or stdin and checks the given formula for the specified schema size
main :: IO ()
main = do
  let verStr = footer $ "Git: " ++ gitStr ++ "\tBuild time: " ++ btime
        where btime = $(stringE =<< runIO (show <$> getCurrentTime))
              gitStr = concat [$(gitBranch), "@", take 7 $(gitHash),
                               if $(gitDirty) then "(modified)" else ""]

  conf <- execParser $ info (helper <*> confFromArgs) (verStr <> fullDesc)
  g <- readGraph $ slvGraphFile conf
  findAndPrint conf g
