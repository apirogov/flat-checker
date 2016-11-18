module Parse where

import Types
import Data.Ratio

import qualified Data.Set as S
import qualified Data.IntSet as IS
import qualified Data.Vector as V
import Data.List (sort, sortOn, nub)
import Text.Parsec hiding (State)
import Text.Parsec.String (Parser)

sym :: String -> Parser ()
sym x = spaces *> string x *> spaces

parse' :: Parser a -> String -> String -> Maybe a
parse' p f s = either (const Nothing) Just $ parse p f s

parseint::Parser Int
parseint = read <$> many1 digit

ltlformula :: Parser (Formula Char)
ltlformula = skipMany space *> (parseprop <|> parsenot <|> parsenext <|> parsebinary) <* skipMany space
  where parseprop  = Prop <$> lower
        parsenot  = Not  <$> (sym "~" *> ltlformula)
        parsenext = Next <$> (sym "X" *> ltlformula)

        parseufrac = do
          (m,n) <- (,) <$> (sym "[" *> parseint <* sym "/") <*> (parseint  <* sym "]")
          if m>n || m<=0 || n<=0
            then error $ "Parse error: Invalid fraction at U[..] in formula: " ++ show m ++ "/" ++ show n
            else return $ m % n

        andop = char '&' *> pure And
        orop  = char '|' *> pure Or
        untilop = Until <$> (sym "U" *> option 1 parseufrac)
        binop = spaces *> andop <|> orop <|> untilop <* spaces
        parsebinary = (\f op g -> op f g) <$> (sym "(" *> ltlformula) <*> (spaces *> binop <* spaces) <*> (ltlformula <* sym ")")

-- parser for input in same format as pretty printed formulae
parseFormula :: String -> Maybe (Formula Char)
parseFormula str = parse' (ltlformula <* eof) "<formula>" str

-- parser for graph
graph :: Parser (Graph Char)
graph = do
  nodedefs <- sortOn fst <$> many node <* eof
  let nodeids = map fst nodedefs
      maxnode = maximum (maximum nodeids:map (IS.findMax . snd . snd) nodedefs)
  if (length . nub . sort $ nodeids) < length nodeids
  then error $ "Parse error: Multiple definition of a node!"
  else return $ (V.replicate (maxnode+1) (S.empty, IS.empty)) V.// nodedefs
  where node = (,) <$> (spc *> parseint <* spc) <*> ( (,) <$> (option S.empty propset) <*> (sym "->" *> succlist) )
        propset = S.fromList <$> (sym "{" *> ((lower <* spc) `sepBy` (char ',' *> spc)) <* char '}')
        succlist = IS.fromList <$> ((parseint <* spc) `sepBy1` (char ',' *> spc)) <* newline
        spc = many (oneOf " \t") -- space but not newline

-- parser for labelled adj. graph
parseGraph :: String -> String -> Maybe (Graph Char)
parseGraph filename str = parse' graph filename' str
  where filename' = if null filename then "<stdin>" else filename
