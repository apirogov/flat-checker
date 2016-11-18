module Main where
import System.IO (hSetBuffering, BufferMode(..), stdout)
import System.Directory (doesFileExist)
import Options.Applicative

import Types
import Parse
import Solve

import Data.Ratio

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

-- parseGraph :: String -> Maybe (Graph Char)
-- parseGraph = const $ Just g --TODO

-- given: kripke structure (directed graph with start node and letters at nodes)
-- given: fLTL formula of length m with r Untils
-- given: maximal schema size n
-- task: tell if there is a run on a path schema of length n that is model of formula
-- -> obtain size of maximal simple loop
-- -> guess path schema (node ids and backloops), guess number of loopings
--    -> n node ids, n backloop pairs
-- -> guess correct labelling (composite subformulae)
--    -> linear in formula size m
-- -> guess correct counter updates (at states) and guards (at edges)
-- -> verify validity

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

-- some examples for REPL usage
g = toGraph [("p",[1]),("py",[2]),("q",[0,3]),("pq",[4,3]),("y",[5]),("z",[3])]

f = Not $ Prop 'p' `And` (Prop 'q' `Or` Prop 'z')
f2 = Until (1%2) (Prop 'p') (Prop 'q' `Or` Prop 'z')
f3 = Next (Next (Next (Next (Prop 'z' `And` Next (Prop 'q')))))
f4 = Prop 'p' `And` (Next $ ((Prop 'y')`Or`(Prop 'q')) `until1` (Prop 'z'))

