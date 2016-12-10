{-# LANGUAGE RankNTypes, ExistentialQuantification #-}
module Z3Util where
import Data.List (intercalate)
import Control.Monad
import Z3.Monad
import qualified Data.Map as M
import qualified Data.Vector as V

-- | make finite ID domain
mkEnum :: Show a => String -> String -> [a] -> Z3 Sort
mkEnum sname spref is = join $ mkDatatype <$> mkStringSymbol sname <*> forM is makeconst
  where makeconst i = join $ mkConstructor <$> mkStringSymbol (spref++(show i)) <*> mkStringSymbol (spref++(show i)) <*> pure []

-- | variable constructor, evaluator and list of constructor symbols
-- type EnumAPI a = (String -> Z3 AST, Model -> AST -> Z3 (Maybe a), V.Vector AST)
data EnumAPI a = forall b. EnumAPI (String -> Z3 b, Model -> b -> Z3 (Maybe a), a -> b -> Z3 AST, b -> b -> Z3 AST)

-- | create a custom enumeration type for a list of values
mkEnumSort :: (Show a, Read a, Ord a) => String -> [a] -> Z3 (EnumAPI a)
mkEnumSort name is = do
  enum <- mkEnum (name++"_T") name is
  enumConst <-getDatatypeSortConstructors enum
  let mkFreshNodeVar = flip mkFreshConst enum
  constrs <- mapM (flip mkApp []) enumConst
  let cmap = M.fromList $ zip is constrs
  -- evaluate resulting id back to an integer
  let evalEnum m sym = do
        ret <- modelEval m sym True
        case ret of
          Nothing -> return Nothing
          Just v -> astToString v >>= return . Just . read . drop (length name)
  return $ EnumAPI (mkFreshNodeVar, evalEnum, mkEq . (cmap M.!), mkEq)

-- | represent a list of scalars as integers in Z3
mkIntEnumSort :: (Ord a) => [a] -> Z3 (EnumAPI a)
mkIntEnumSort is = do
  let idx = [0..length is - 1]
  let ism = M.fromList $ zip idx is
  let evalEnum m s = do
        i <- evalInt m s
        case i of
          Nothing -> return Nothing
          Just i' -> return $ M.lookup (fromIntegral i') ism
  constrs <- mapM (mkInteger . fromIntegral) idx
  let cmap = M.fromList $ zip is constrs
  return $ EnumAPI (mkFreshIntVar, evalEnum, mkEq . (cmap M.!), mkEq)

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
