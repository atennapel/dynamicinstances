{-# LANGUAGE OverloadedStrings #-}

import GHC.Exts (IsString(..))
import qualified Data.Map as Map
import qualified Data.List as List

type Index = Int
newtype Name = Name String
  deriving (Eq, Ord)

instance Show Name where
  show (Name x) = x

instance IsString Name where
  fromString = Name

data Type
  = TConst Name
  | TFun Type Type
  deriving (Eq)

instance Show Type where
  show (TConst x) = show x
  show (TFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"

instance IsString Type where
  fromString = TConst . Name

data Term n
  = Var n
  | Abs Name Type (Term n)
  | App (Term n) (Term n)
  deriving (Eq)

instance Show n => Show (Term n) where
  show (Var n) = show n
  show (Abs x ty b) = "(\\(" ++ (show x) ++ " : " ++ (show ty) ++ "). " ++ (show b) ++ ")"
  show (App a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"

instance IsString n => IsString (Term n) where
  fromString = Var . fromString

hasVar :: Eq n => n -> Term n -> Bool
hasVar x (Var y) = x == y
hasVar x (Abs _ _ b) = hasVar x b
hasVar x (App a b) = hasVar x a || hasVar x b

type Named = Term Name
type Nameless = Term Index

-- convert closed named term to nameless term
toNameless :: Named -> Maybe Nameless
toNameless t = go 0 Map.empty t
  where
    go lv m (Var x) = fmap (\i -> Var (lv - i - 1)) $ Map.lookup x m
    go lv m (Abs x ty b) = Abs x ty <$> go (lv + 1) (Map.insert x lv m) b
    go lv m (App a b) = App <$> (go lv m a) <*> (go lv m b)

-- safe lookup
index :: Int -> [t] -> Maybe t
index i _ | i < 0 = Nothing
index _ [] = Nothing
index 0 (h : _) = Just h
index n (_ : t) = index (n - 1) t

fresh :: [Name] -> Name -> Name
fresh xs x@(Name x') = if elem x xs then fresh xs (Name $ x' ++ "'") else x

-- convert closed nameless term to named term
toNamed :: Nameless -> Maybe Named
toNamed t = go [] t
  where
    go ix (Var i) = Var <$> index i ix
    go ix (Abs x ty b) =
      let x' = if maybe False (\i -> hasVar (i + 1) b) (List.elemIndex x ix) then fresh ix x else x in
      Abs x' ty <$> go (x' : ix) b
    go ix (App a b) = App <$> (go ix a) <*> (go ix b)

-- typechecking
whenBool :: Bool -> t -> Maybe t
whenBool True x = Just x
whenBool _ _ = Nothing

typecheck :: [Type] -> Nameless -> Maybe Type
typecheck ctx (Var i) = index i ctx
typecheck ctx (Abs _ ty b) = TFun ty <$> typecheck (ty : ctx) b
typecheck ctx (App a b) = do
  TFun l r <- typecheck ctx a
  tb <- typecheck ctx b
  whenBool (l == tb) r

-- eta/beta reduction
shift :: Index -> Index -> Nameless -> Nameless
shift d c (Var k) = Var $ if k < c then k else k + d
shift d c (Abs x ty b) = Abs x ty $ shift d (c + 1) b
shift d c (App a b) = App (shift d c a) (shift d c b)

subst :: Index -> Nameless -> Nameless -> Nameless
subst j s v@(Var k) = if k == j then s else v
subst j s (Abs x ty b) = Abs x ty $ subst (j + 1) (shift 1 0 s) b
subst j s (App a b) = App (subst j s a) (subst j s b)

substTop :: Nameless -> Nameless -> Nameless
substTop s b = shift (-1) 0 (subst 0 (shift 1 0 s) b)

step :: Nameless -> Maybe Nameless
step (App (Abs _ _ b) v) = Just $ substTop v b
step (Abs _ _ (App b (Var 0))) = Just b
step _ = Nothing

reduce :: Nameless -> Nameless
reduce t = maybe t reduce (step t)

-- testing
expr :: Named
expr = App (Abs "x" (TFun "Bool" "Bool") "x") (Abs "x" "Bool" "x") 

main :: IO ()
main = do
  putStrLn $ show expr
  case toNameless expr of
    Nothing -> return ()
    Just expr' -> do
      putStrLn $ show expr'
      case typecheck [] expr' of
        Nothing -> return ()
        Just ty -> do
          putStrLn $ show ty
          let val = reduce expr'
          putStrLn $ show val
          case toNamed val of
            Nothing -> return ()
            Just val' -> putStrLn $ show val'
