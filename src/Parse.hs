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
                  $ parse (parsenat `sepBy1` char ',' <* eof) str str
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
parsenat :: Parser Int
parsenat = read <$> many1 digit

-- | reads an integer (possible minus sign)
parseint :: Parser Int
parseint = (*) <$> option 1 (char '-' *> pure (-1)) <*> parsenat

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
          (m,n) <- (,) <$> (sym "[" *> parsenat <* sym "/") <*> (parsenat  <* sym "]")
          if m>n || m<=0 || n<=0
            then fail $ "Parse error: Invalid fraction at U[..] in formula: " ++ show m ++ "/" ++ show n
            else return $ m % n

        andop = char '&' *> pure And
        orop  = char '|' *> pure Or
        untilop = Until <$> (sym "U" *> option 1 parseufrac)
        binop = spaces *> andop <|> orop <|> untilop <* spaces
        pbinary = (\f op g -> op f g) <$> (sym "(" *> ltlformula) <*> (spaces *> binop <* spaces) <*> (ltlformula <* sym ")")

parseedgel :: Parser [EdgeL String]
parseedgel = edgel `sepBy` sym ";"
  where edgel = skipMany space *> (grd <|> upd)
        ctr = (:) <$> letter <*> many alphaNum
        upd = UpdateInc <$> ctr <*> (sym "+=" *> (fromIntegral <$> parseint) <* spaces)
        grdge = string ">=" *> spaces *> pure GuardGE
        grdlt = string "<" *> spaces *> pure GuardLT
        lincomb = ((,) <$> (fromIntegral <$> parseint) <*> (ctr <* spaces)) `sepBy1` (char '+' *> spaces)
        grd = do
          comb <- lincomb
          op <- grdge <|> grdlt
          cst <- fromIntegral <$> parseint
          return $ op comb cst

-- | load a digraph from a dot file. needs IO to catch failure
parseDot :: String -> IO (Maybe (Graph Char String))
parseDot dgs = catch (Just <$> evaluate g) handleErr
  where handleErr :: GraphvizException -> IO (Maybe (Graph Char String))
        handleErr _ = return Nothing
        g = parseDot' dgs

-- | load a digraph from a dot file. unfortunately an exception can be thrown
parseDot' :: String -> Graph Char String
parseDot' dgs = mkGraph ns es
  where dg = parseDotGraph (TL.pack dgs) :: DotGraph Int
        ns = map (\n -> (nodeID n,  at n)) $ graphNodes dg
        es = map (\e@(DotEdge f t _) -> (f,t, parseEdge $ at' e)) $ graphEdges dg
        --throw all symbols in all text labels in one set
        at n  = S.unions $ map S.fromList $ catMaybes $ map getStr $ nodeAttributes n
        at' n = concat $ catMaybes $ map getStr $ edgeAttributes n
        getStr (Label (StrLabel s)) = Just $ TL.unpack s
        getStr _ = Nothing
        parseEdge s = either (error $ "could not parse edge: \"" ++ s ++ "\"") id $ parse parseedgel s s
