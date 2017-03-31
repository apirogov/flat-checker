module Parse (
  ltlformula, parseLoopLens, parseFormula, parseDot, parseDot'
) where

import Types
import Data.Maybe (catMaybes)
import Data.List (intercalate)
import qualified Data.Set as S
import Text.Parsec hiding (State)
import Text.Parsec.String (Parser)

import qualified Data.Text.Lazy as TL
import Data.GraphViz.Types hiding (parse)
import Data.GraphViz (DotGraph)
import Data.GraphViz.Attributes.Complete hiding (Constraint)
import Data.GraphViz.Exception
import Control.Exception hiding (try)

import Data.Graph.Inductive (mkGraph)

parse' :: String -> Parser a -> String -> String -> Either String a
parse' errmsg p f s = either (Left . (errmsg++) . show) Right $ parse p f s

-- | parse a list of natural numbers
parseLoopLens :: String -> Either String [Int]
parseLoopLens str = parse' "Parse error: Could not read supplied list of lengths: " (parsenat `sepBy1` char ',' <* eof) str str

-- | parser for formulae
parseFormula :: String -> Either String (Formula String)
parseFormula str = parse' "Parse error: Failed to parse formula: " (ltlformula <* eof) str str

-- | reads spaces, but not newlines
spc :: Parser ()
spc = many (oneOf " \t") *> pure ()

-- | reads a token followed by whitespace
sym :: String -> Parser ()
sym x = string x *> spc

-- | reads a natural number (no minus sign etc.)
parsenat :: Parser Int
parsenat = read <$> many1 digit <* spc

-- | reads an integer (possible minus sign)
parseint :: Parser Int
parseint = (*) <$> option 1 (char '-' *> pure (-1)) <*> parsenat

-- | propositions start with a letter, then can contain numbers
prop :: Parser String
prop = ((:) <$> lower <*> many (char '_' <|> lower <|> digit)) <* spc

-- | mapping of constraint operators to symbols
opMap = [("=",CEq), ("<=",CLe), (">=",CGe), ("<",CLt), (">",CGt)]

parseConstraint ::  [(String,ConstraintOp)] -> Parser a -> Parser (Constraint a)
parseConstraint ops p = Constraint <$> lincomb <*> op <*> (fromIntegral <$> parseint)
  where lincomb = (:) <$>      ((,) <$> (((*) <$> optneg <*> option 1 (fromIntegral <$> parsenat))) <*> p)
                      <*> many ((,) <$> (((*) <$> sign   <*> option 1 (fromIntegral <$> parsenat))) <*> p)
        optneg = option 1 (sym "-" *> pure (-1))
        sign = (sym "+" *> pure 1) <|> (sym "-" *> pure (-1))
        op = foldl1 (<|>) (map (\(a,b) -> try (string a *> pure b)) ops) <* spc

-- | reads an fLTL formula
ltlformula :: Parser (Formula String)
ltlformula = spc *> (try ptru <|> try pfls <|> pprop <|> pnot <|> pnext <|> pfin <|> pglob <|> pparens) <* spc
  where ptru = sym "true" *> pure Tru
        pfls = sym "false" *> pure Fls
        pprop  = Prop <$> prop
        pnot  = Not  <$> (sym "~" *> ltlformula)
        pnext = Next <$> (sym "X" *> ltlformula)
        -- syntactic sugar
        pfin  = (\c f -> Until c Tru f)             <$> (sym "F" *> parseUConstr) <*> ltlformula
        pglob = (\c f -> Not (Until c Tru (Not f))) <$> (sym "G" *> parseUConstr) <*> ltlformula

        pparens = do --either optional parentheses, or binary operator with mandatory
          left <- sym "(" *> ltlformula
          (sym ")" *> pure left) <|> (binop <*> pure left <*> (ltlformula <* sym ")"))

        -- equality constraints enforce quadratic blowup. we forbid that
        parseUConstr = option Nothing
                     $ Just <$> (sym "[" *> parseConstraint (filter ((/="=").fst) opMap) ltlformula <* sym "]")

        andop = sym "&" *> pure And
        orop  = sym "|" *> pure Or
        untilop = Until <$> (sym "U" *> parseUConstr)
        binop = andop <|> orop <|> untilop

-- | parse a node label in the dot digraph. filters out the unique set with props
parsenodel :: Parser (S.Set String)
parsenodel = S.fromList <$> (spc *> (prop `sepBy` sym ",") <* eof)

-- | parse an edge label in the dot digraph
parseedgel :: Parser [EdgeL String]
parseedgel = spc *> (edgel `sepBy` sym ",") <* eof
  where edgel = try (Right <$> upd) <|> (Left <$> (sym "[" *> (parseConstraint opMap prop `sepBy` sym ",") <* sym "]"))
        updop = (sym "+=" *> pure (*1)) <|> (sym "-=" *> pure (*(-1)))
        upd = UpdateInc <$> prop <*> (updop <*> (fromIntegral <$> parseint))

-- | load a digraph from a dot file. needs IO to catch failure
parseDot :: String -> IO (Maybe (Graph String String))
parseDot dgs = catch (Just <$> evaluate g) handleErr
  where handleErr :: GraphvizException -> IO (Maybe (Graph String String))
        handleErr _ = return Nothing
        g = parseDot' dgs

-- | load a digraph from a dot file. unfortunately an exception can be thrown by the GraphViz API.
--  edge guards and updates are read from the custom attributes 'updates' and 'guards'
--  node propositions are read from the custom 'props' attributes with just "{PROPS}"
--  both counters and propositions must start with a lowercase letter and can
--  contain lowercase letters, digits and underscores.
parseDot' :: String -> Graph String String
parseDot' dgs = mkGraph ns es
  where dg = parseDotGraph (TL.pack dgs) :: DotGraph Int
        ns = map (\(DotNode n at)   -> (n,   parseNode $ getLabel at)) $ graphNodes dg
        es = map (\(DotEdge f t at) -> (f,t, parseEdge $ getLabel at)) $ graphEdges dg
        parseNode s = either error id $ parse' "could not parse node annotation: " parsenodel s s
        parseEdge s = either error id $ parse' "could not parse edge annotation: " parseedgel s s
        getLabel = intercalate "," . catMaybes . map getStr
        -- getStr (Label (StrLabel s)) = Just $ TL.unpack s -- dont parse label, makes problems...
        getStr (UnknownAttribute k v) = if any (==TL.unpack k) ["props","updates","guards"] then Just $ TL.unpack v else Nothing
        getStr _ = Nothing
