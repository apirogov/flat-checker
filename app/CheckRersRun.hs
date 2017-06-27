module Main where
import System.Environment (getArgs)
import System.IO.Temp (withSystemTempFile)
import System.Process
import System.IO (hPutStrLn, hClose, hFlush, stdout)
import System.Exit (ExitCode(..))
import Data.Char (toLower)
import Data.List (sort, nub, intercalate)
import Data.Maybe (isJust, fromJust)
import Control.Monad
import Control.Arrow
import qualified Data.Map as M

import Types (Formula(..), formulaProps, simplify')
import Parse (parseFormula, parseDot')
import Solve

type RunRep = ([String],[String])

toMap :: String -> M.Map Int String
toMap = M.fromList . map ((\(n:ws) -> (read n, unwords ws)) . words) . lines

parseRun :: String -> Maybe RunRep
parseRun str = if null rawprops then Nothing else Just $ trim $ second (map init) $ break ((=='*').last) rawprops
  where rawprops = map mapprop $ words str

trim :: (Eq a) => ([a],[a]) -> ([a],[a])
trim (l,r) = if r'/=ll then (l,r) else trim (take (length l - lenr) l, r)
  where (l', r') = (reverse l, reverse r)
        ll = take lenr l'
        lenr = length r

mapprop :: String -> String
mapprop "" = ""
mapprop s@(x:_)
 | x >= 'A' && x <= 'E' = 'i':(toLower <$> s)
 | otherwise = 'o':(toLower <$> s)

makeDot :: Formula String -> RunRep -> String
makeDot _ ([],[]) = error "ERROR: Empty run"
makeDot _ (_,[]) = error "ERROR: Finite run"
makeDot f (l,r) = "//Check with: " ++ show f ++ "\ndigraph {\n"
  ++ nodes ++ edges ++ "\n}\n"
  where lenl = length l
        lenr = length r
        nodes = concatMap (\(i,p) -> show (i::Int)++"[props=\""++p++"\"];\n") $ zip [0..] (l ++ r)
        edges = (++ " -> " ++ show lenl ++ ";") $ intercalate " -> " $ map show [0..(lenl+lenr-1)]

-- | given formula and a run, produce a promela file encoding that task
makePml :: Formula String -> RunRep -> String
makePml _ ([],[]) = error "ERROR: Empty run"
makePml f ([],r:rs) = makePml f ([r],rs++[r])
makePml f r@(l:ll,rr) = "//Alphabet:\n" ++ decls ++ "\n//Initial state:\nbyte _prop = "++l++";\n"
  ++ "// w = "++show r++"\n"++"active proctype runproc() {\n"++row
  ++"\tdo :: {\n"++lasso++"\t} od\n}\n//formula = "++show f ++"\nltl formula {"++fltlToPltl f++"}"
  where ps = nub $ sort $ formulaProps f++ uncurry (++) r
        decls = concatMap (\(i,p) -> "byte "++p++" = "++show (i::Int)++";\n") $ zip [1..] ps
        row = mkseq ll
        lasso = mkseq rr
        mkseq = concatMap (\p -> "\t_prop=0; _prop = "++p++";\n")

fltlToPltl :: Formula String -> String
fltlToPltl Tru       = "true"
fltlToPltl Fls       = "false"
fltlToPltl (Prop p)  = "(_prop=="++p++")"
fltlToPltl (And g h) =  "("++fltlToPltl g++" && "++fltlToPltl h++")"
fltlToPltl (Or  g h) =  "("++fltlToPltl g++" || "++fltlToPltl h++")"
fltlToPltl (Next g)  =  "((_prop!=0)U((_prop==0)U("++fltlToPltl g++")))"
fltlToPltl (Not (Until Nothing Tru (Not g)))  =  "([]("++fltlToPltl g++"))"
fltlToPltl (Until Nothing Tru g)  =  "(<>("++fltlToPltl g++"))"
fltlToPltl (Until Nothing g h)  =  "("++fltlToPltl g++"U"++fltlToPltl h++")"
fltlToPltl (Not g)   = "(!("++fltlToPltl g++"))"
fltlToPltl _  = error "ERROR: Constrained until not supported here."

-- | convert counterexample I/O trace into counter system and use flat-checker itself
checkWithFlatchecker :: Int -> Formula String -> RunRep -> IO ()
checkWithFlatchecker num f r = do
  putStr $ show num ++ "\t"
  let dot = makeDot f r
  -- putStrLn dot
  let g = parseDot' dot
  let n = length (fst r) + 3*length (snd r)
  run <- findRun (defaultSolveConf (Not f) n) g
  putStrLn $ case rRun run of
    Just _  -> "successfully falsified formula with supplied run."
    Nothing -> "failed falsification of formula with supplied run."

-- | verify the counterexample with a formula using spin
checkWithSpin :: Int -> Formula String -> RunRep -> IO ()
checkWithSpin num f r = withSystemTempFile "spinjob" $ \filename h -> do
  putStr $ show num ++ " "
  hPutStrLn h $ makePml f r
  hClose h
  print f
  -- putStrLn $ makePml f r
  putStrLn $ fltlToPltl f
  print r
  hFlush stdout
  -- (_,out,_) <- readProcessWithExitCode "spin" ["-search", filename] ""
  (ec,out,_) <- readProcessWithExitCode "timeout" ["1d", "spin", "-search", filename] ""
  let ls = lines out
      (l1:l2:_) = ls
  let violated l = length l > 2 && ("violated" == words l !! 2)
  let acccycle l = length l > 2 && ("acceptance" == words l !! 1)
  if ec == ExitFailure 124 then
    putStrLn "failed falsification (timeout)"
  else if violated l1 || acccycle l1 then do
    _ <- readProcess "rm" [words l2 !! 2] "" -- remove .trail file
    putStrLn $ init $ unlines $ take 2 ls
    putStrLn "successfully falsified formula.\n"
  else do
    putStrLn $ init out
    putStrLn "failed falsification of formula with given run.\n"

-- | Input: Numbered list of flat-checker parsable formulas, numbered list of the counterexamples
--   Output: Spin falsification of formula on run
main :: IO ()
main = do
  args' <- getArgs
  when (length args' < 2) $ error "Usage: checkltl.hs [-s] formulas.txt results.txt [num]"
  let (args,spin) = if head args' == "-s" then (tail args', True) else (args', False)
  let check = if spin then checkWithSpin else checkWithFlatchecker

  let (ffile:rfile:_) = args
  let num :: Maybe Int
      num = if length args >= 3 then Just $ read (args !! 2)  else Nothing
      parseFormula' f = either (\e -> error $ "Could not parse formula "++f++": "++e) simplify' $ parseFormula f
  fs <- (M.map parseFormula' . toMap) <$> readFile ffile
  rs <- (M.map parseRun . toMap) <$> readFile rfile
  case num of
    Nothing -> forM_ (M.keys $ M.filterWithKey (\k _ -> k `M.member` fs) $ M.filter isJust rs) $ \n ->
      check n (fs M.! n) (fromJust $ rs M.! n)
    Just n -> do
      let (f,r) = (fs M.! n, rs M.! n)
      case r of
        Nothing -> error "No counterexample to verify."
        Just run -> check n f run
