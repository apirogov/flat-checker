module Parse (
  ltlformula, parseLoopLens, parseFormula, parseDot, parseDot'
) where

import Types

import Data.Ratio ((%))
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import Text.Parsec hiding (State)
import Text.Parsec.String (Parser)

import qualified Data.Text.Lazy as TL
import Data.GraphViz.Types hiding (parse)
import Data.GraphViz (DotGraph)
import Data.GraphViz.Attributes.Complete
import Data.GraphViz.Exception
import Control.Exception

import Data.Graph.Inductive (mkGraph)

-- | parse a list of natural numbers
parseLoopLens :: String -> Either String [Int]
parseLoopLens str = either (const $ Left errmsg) Right
                  $ parse (parseint `sepBy1` char ',' <* eof) str str
  where errmsg = "Parse error: Could not read supplied list of lengths"

-- | parser for formulae
parseFormula :: String -> Either String (Formula Char)
parseFormula str = either (Left . (errmsg++) . show) Right $ parse (ltlformula <* eof) str str
  where errmsg = "Parse error: Failed to parse formula: "

-- | reads spaces, but not newlines
spc :: Parser ()
spc = many (oneOf " \t") *> pure ()

-- | reads a token surrounded by whitespace
sym :: String -> Parser ()
sym x = spc *> string x *> spc

-- | reads a natural number (no minus sign etc.)
parseint :: Parser Int
parseint = read <$> many1 digit

-- | reads an fLTL formula
ltlformula :: Parser (Formula Char)
ltlformula = skipMany space *> (ptru <|> pfls <|> pprop <|> pnot <|> pnext <|> pfin <|> pglob <|> pbinary) <* skipMany space
  where ptru = sym "1" *> pure Tru
        pfls = sym "0" *> pure Fls
        pprop  = Prop <$> lower
        pnot  = Not  <$> (sym "~" *> ltlformula)
        pnext = Next <$> (sym "X" *> ltlformula)
        -- syntactic sugar
        pfin = Until 1 <$> pure Tru <*> (sym "F" *> ltlformula)
        pglob = Not <$> (Until 1 <$> pure Tru <*> (Not <$> (sym "G" *> ltlformula)))

        parseufrac = do
          (m,n) <- (,) <$> (sym "[" *> parseint <* sym "/") <*> (parseint  <* sym "]")
          if m>n || m<=0 || n<=0
            then fail $ "Parse error: Invalid fraction at U[..] in formula: " ++ show m ++ "/" ++ show n
            else return $ m % n

        andop = char '&' *> pure And
        orop  = char '|' *> pure Or
        untilop = Until <$> (sym "U" *> option 1 parseufrac)
        binop = spaces *> andop <|> orop <|> untilop <* spaces
        pbinary = (\f op g -> op f g) <$> (sym "(" *> ltlformula) <*> (spaces *> binop <* spaces) <*> (ltlformula <* sym ")")

-- | load a digraph from a dot file. needs IO to catch failure
parseDot :: String -> IO (Maybe (Graph Char))
parseDot dgs = catch (Just <$> evaluate g) handleErr
  where handleErr :: GraphvizException -> IO (Maybe (Graph Char))
        handleErr _ = return Nothing
        g = parseDot' dgs

-- | load a digraph from a dot file. unfortunately an exception can be thrown
parseDot' :: String -> Graph Char
parseDot' dgs = mkGraph ns es
  where dg = parseDotGraph (TL.pack dgs) :: DotGraph Int
        ns = map (\n -> (nodeID n, at n)) $ graphNodes dg
        es = map (\(DotEdge f t _) -> (f,t,())) $ graphEdges dg
        --throw all symbols in all text labels in one set
        at n = S.unions $ map S.fromList $ catMaybes $ map getStr $ nodeAttributes n
        getStr (Label (StrLabel s)) = Just $ TL.unpack s
        getStr _ = Nothing
