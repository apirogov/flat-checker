module Main where

import Types (Formula(..), simplify)
import Control.Arrow
import Bench (formula)

inout = Prop "inout"

wrap :: Formula String -> Formula String
wrap f = Until Nothing (Not inout) (And inout f)

rersify :: Formula String -> Formula String
rersify Tru = Tru
rersify Fls = Fls
rersify (Prop p) = Prop p
rersify (Not f) = Not $ rersify f
rersify (And f g) = And (rersify f) (rersify g)
rersify (Or f g) = Or (rersify f) (rersify g)
rersify (Next g)  = Next $ Until Nothing (Not inout) $ And inout (rersify g)
rersify (Until Nothing g h) = Until Nothing (Or (Not inout) $ rersify g) (And inout $ rersify h)
rersify _  = error "ERROR: Constrained until not supported here."

main :: IO ()
main = putStrLn =<< unlines . map (uncurry (\l r -> l++"\t"++r) . second (show . simplify . wrap . rersify . formula) . break (=='\t')) . lines <$> getContents
