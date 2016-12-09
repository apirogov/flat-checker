module Z3Util where
import Data.List (intercalate)
import Control.Monad
import Z3.Monad
import qualified Data.Vector as V

-- | make finite ID domain
mkEnum :: Show a => String -> String -> [a] -> Z3 Sort
mkEnum sname spref is = join $ mkDatatype <$> mkStringSymbol sname <*> forM is makeconst
  where makeconst i = join $ mkConstructor <$> mkStringSymbol (spref++(show i)) <*> mkStringSymbol (spref++(show i)) <*> pure []

-- | custom enumeration type (NOTE: seems even a bit slower than using ints? benchmark more!)
mkEnumSort :: [Int] -> Z3 (String -> Z3 AST, Model -> AST -> Z3 (Maybe Integer), V.Vector AST)
mkEnumSort is = do
  node <- mkEnum "NodeId" "n" is
  nodeConst <- V.fromList <$> getDatatypeSortConstructors node
  let mkFreshNodeVar = flip mkFreshConst node
  nid <- mapM (flip mkApp []) nodeConst
  -- evaluate resulting id back to an integer
  let evalNid m sym = do
        ret <- modelEval m sym True
        case ret of
          Nothing -> return Nothing
          Just v -> astToString v >>= return . Just . read . tail
  return (mkFreshNodeVar, evalNid, nid)

-- | return a fake enum sort that is just ints
mkDummyEnumSort :: [Int] -> Z3 (String -> Z3 AST, Model -> AST -> Z3 (Maybe Integer), V.Vector AST)
mkDummyEnumSort is = do
  nid <- V.fromList <$> mapM (mkInteger . fromIntegral) is
  return (mkFreshIntVar, evalInt, nid)


-- | sugar, expand quantifiers over variables
mkForallI :: [a] -> (a -> Z3 AST) -> Z3 AST
mkForallI [] _ = mkTrue
mkForallI ind f = mkAnd =<< forM ind f

mkExistsI :: [a] -> (a -> Z3 AST) -> Z3 AST
mkExistsI [] _ = mkFalse
mkExistsI ind f = mkOr =<< forM ind f

-- | if (a>b) then f(a) else f(b) .ite is MUCH faster than using implications here
mkWithMax a b f = join $ mkIte <$> mkGt a b <*> f a <*> f b

-- | only enforce f if predicate (known at compile time) is true,
-- otherwise make it trivially true or false. useful to prevent out-of-bounds errors
ifT False _ = mkTrue
ifT True f = f
ifF False _ = mkFalse
ifF True f = f

-- | generate a variable name from prefix and a list of indices
varname pref ind = intercalate "_" $ pref:(map show ind)

-- | allocate a vector of variable symbols with given prefix, indexed over is
mkVarVec mkf name is = V.fromList <$> forM is (\i -> mkf $ varname name [i])
-- | allocate a matrix of variable symbols with given prefix, indexed over is and js
mkVarMat mkf name is js = V.fromList <$> forM is (\i -> mkVarVec mkf (varname name [i]) js)
