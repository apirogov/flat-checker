{-# LANGUAGE RankNTypes, ExistentialQuantification #-}
module Z3Util where
import Data.List (intercalate)
import Control.Monad
import Z3.Monad
import qualified Data.Map as M
import qualified Data.Vector as V

-- | declare finite ID domain inside Z3
mkEnum :: Show a => String -> String -> [a] -> Z3 Sort
mkEnum sname spref is = join $ mkDatatype <$> mkStringSymbol sname <*> forM is makeconst
  where makeconst i = join $ mkConstructor <$> mkStringSymbol (spref++(show i)) <*> mkStringSymbol (spref++(show i)) <*> pure []

-- | variable constructor, evaluator and list of constructor symbols
data EnumAPI a = forall b. EnumAPI
      { enumMk   :: String -> Z3 b              -- ^ constructor
      , enumEval :: Model -> b -> Z3 (Maybe a)  -- ^ evaluator
      , enumIs   :: a -> b -> Z3 AST            -- ^ compare to fixed value
      , enumEq   :: b -> b -> Z3 AST            -- ^ compare two variable enums
      }

-- | create a custom enumeration type for a list of values
mkEnumSort :: (Show a, Read a, Ord a) => String -> [a] -> Z3 (EnumAPI a)
mkEnumSort name is = do
  enum <- mkEnum (name++"_T") name is
  enumConst <- getDatatypeSortConstructors enum
  let mkFreshNodeVar = flip mkFreshConst enum
  let evalEnum m sym = do
        ret <- modelEval m sym True
        case ret of
          Nothing -> return Nothing
          Just v -> astToString v >>= return . Just . read . drop (length name)
  constrs <- mapM (flip mkApp []) enumConst
  let cmap = M.fromList $ zip is constrs
  return $ EnumAPI mkFreshNodeVar evalEnum (mkEq . (cmap M.!)) mkEq

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
  return $ EnumAPI mkFreshIntVar evalEnum (mkEq . (cmap M.!)) mkEq

-- | create an enum where each of n values is encoded in log(n) bits
mkBoolEnumSort :: (Ord a) => [a] -> Z3 (EnumAPI a)
mkBoolEnumSort is = do
  _T <- mkTrue
  _F <- mkFalse
  let n = length is
      bits = (log $ fromIntegral n) :: Double
      lbits = (2::Integer)^((floor bits)::Integer)
      m = fromIntegral $ if lbits < fromIntegral n then ceiling bits else lbits
      comb = replicateM m [False,True]  -- 0,0 / 0,1 / 1,0 / 1,1 ... for fixed length
      ism = M.fromList $ zip is comb    -- given value -> combination
      iism = M.fromList $ zip comb is   -- combination -> back to value
      mkBE s = forM [1..m] $ \i -> mkFreshBoolVar (s++"_"++show i)
      evalBE mdl bs = do
        bvs <- mapEval evalBool mdl bs
        case bvs of
          Nothing -> return Nothing
          Just bv -> return $ Just $ iism M.! bv
      -- compare to fixed value <-> check for its combination
      isBE a b = mkAnd =<< mapM (\(bv,v) -> mkEq bv $ if v then _T else _F) (zip b (ism M.! a))
      -- compare equality <-> bitwise
      eqBE a b = mkAnd =<< mapM (\(c,d) -> mkEq c d) (zip a b)
  return $ EnumAPI mkBE evalBE isBE eqBE

-- | sugar, expand quantifiers over variables where all possible values are
-- known at compile-time (generates subformula for each valuation).
mkForallI :: [a] -> (a -> Z3 AST) -> Z3 AST
mkForallI [] _ = mkTrue
mkForallI ind f = mkAnd =<< forM ind f

mkExistsI :: [a] -> (a -> Z3 AST) -> Z3 AST
mkExistsI [] _ = mkFalse
mkExistsI ind f = mkOr =<< forM ind f

-- | b has one of the a values
mkAny :: (a -> b -> Z3 AST) -> [a] -> b -> Z3 AST
mkAny f ls p = mkOr =<< forM ls (flip f p)

-- | if (a ~ b) then f(a) else f(b). ite is MUCH faster than using implications here
mkWithCmp :: (AST -> AST -> Z3 AST) -> AST -> AST -> (AST -> Z3 AST) -> Z3 AST
mkWithCmp op a b f = join $ mkIte <$> op a b <*> f a <*> f b

-- | only enforce f if predicate (known at compile time) is true,
-- otherwise make it triv. true or false. useful to prevent out-of-bounds errors
ifT :: Bool -> Z3 AST -> Z3 AST
ifT False _ = mkTrue
ifT True f = f

ifF :: Bool -> Z3 AST -> Z3 AST
ifF False _ = mkFalse
ifF True f = f

-- | generate a variable name from prefix and a list of indices
varname :: (Show i) => String -> [i] -> String
varname pref ind = intercalate "_" $ pref:(map show ind)

-- | allocate a vector of variable symbols with given prefix, indexed over is
mkVarVec :: (Show i) => (String -> Z3 a) -> String -> [i] -> Z3 (V.Vector a)
mkVarVec mkf name is = V.fromList <$> forM is (\i -> mkf $ varname name [i])

-- | allocate a matrix of variable symbols with given prefix, indexed over is and js
mkVarMat :: (Show i, Show j) => (String -> Z3 a) -> String -> [i] -> [j] -> Z3 (V.Vector (V.Vector a))
mkVarMat mkf name is js = V.fromList <$> forM is (\i -> mkVarVec mkf (varname name [i]) js)
