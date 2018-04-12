module Main where

import Control.Arrow
import Types (Formula(..), Constraint(..), simplify')
import Util (formula)

inout :: Formula String
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
rersify (Until c g h) = Until (rersifyC c) (Or (Not inout) $ rersify g) (And inout $ rersify h)
  where rersifyC Nothing = Nothing
        rersifyC (Just (Constraint fs op k)) = Just (Constraint fs' op k)
          where fs' = map (second (And inout . rersify)) fs

main :: IO ()
main = putStrLn =<< unlines . map (uncurry (\l r -> l++"\t"++r) . second (show . simplify' . wrap . rersify . formula) . break (=='\t')) . lines <$> getContents
