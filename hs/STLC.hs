{-# LANGUAGE OverloadedStrings #-}

import GHC.Exts (IsString(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

import Debug.Trace (trace)

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

type Index = Int
data Var
  = Bound Index
  | Free Name
  deriving (Eq)

instance Show Var where
  show (Bound i) = show i
  show (Free x) = show x

instance IsString Var where
  fromString = Free . Name

type Named = Term Name
type Nameless = Term Var

-- convert closed named term to nameless term
toNameless :: Named -> Nameless
toNameless t = go 0 Map.empty t
  where
    go lv m (Var x) = maybe (Var $ Free x) (\i -> Var $ Bound (lv - i - 1)) $ Map.lookup x m
    go lv m (Abs x ty b) = Abs x ty $ go (lv + 1) (Map.insert x lv m) b
    go lv m (App a b) = App (go lv m a) (go lv m b)

-- convert closed nameless term to named term
index :: Int -> [t] -> Maybe t
index i _ | i < 0 = Nothing
index _ [] = Nothing
index 0 (h : _) = Just h
index n (_ : t) = index (n - 1) t

fresh :: FV -> Name -> Name
fresh xs x@(Name x') = if Set.member x xs then fresh xs (Name $ x' ++ "'") else x

type FV = Set.Set Name

free :: Nameless -> FV
free (Var (Bound _)) = Set.empty
free (Var (Free x)) = Set.singleton x
free (Abs _ _ b) = free b 
free (App a b) = Set.union (free a) (free b)

toNamed :: Nameless -> Maybe Named
toNamed t = go [] t
  where
    go ix (Var (Bound i)) = Var <$> index i ix
    go _ (Var (Free x)) = Just $ Var x
    go ix (Abs x ty b) =
      let conflict = maybe False (\i -> hasVar (Bound $ i + 1) b) (List.elemIndex x ix) in
      let fv = free b in
      let x' = if conflict || (Set.member x fv) then fresh (Set.union (Set.fromList ix) fv) x else x in
      Abs x' ty <$> go (x' : ix) b
    go ix (App a b) = App <$> (go ix a) <*> (go ix b)

-- typechecking
type Env = Map.Map Name Type

whenBool :: Bool -> t -> Maybe t
whenBool True x = Just x
whenBool _ _ = Nothing

typecheckR :: Env -> [Type] -> Nameless -> Maybe Type
typecheckR _ ctx (Var (Bound i)) = index i ctx
typecheckR env _ (Var (Free x)) = Map.lookup x env
typecheckR env ctx (Abs _ ty b) = TFun ty <$> typecheckR env (ty : ctx) b
typecheckR env ctx (App a b) = do
  TFun l r <- typecheckR env ctx a
  tb <- typecheckR env ctx b
  whenBool (l == tb) r

typecheck :: Env -> Nameless -> Maybe Type
typecheck e t = typecheckR e [] t

-- eta/beta reduction
shift :: Index -> Index -> Nameless -> Nameless
shift d c (Var (Bound k)) = Var $ Bound (if k < c then k else k + d)
shift _ _ v@(Var (Free _)) = v
shift d c (Abs x ty b) = Abs x ty $ shift d (c + 1) b
shift d c (App a b) = App (shift d c a) (shift d c b)

subst :: Index -> Nameless -> Nameless -> Nameless
subst j s v@(Var (Bound k)) = if k == j then s else v
subst _ _ v@(Var (Free _)) = v
subst j s (Abs x ty b) = Abs x ty $ subst (j + 1) (shift 1 0 s) b
subst j s (App a b) = App (subst j s a) (subst j s b)

substTop :: Nameless -> Nameless -> Nameless
substTop s b = shift (-1) 0 (subst 0 (shift 1 0 s) b)

step :: Nameless -> Maybe Nameless
step (App (Abs _ _ b) v) = Just $ substTop v b
step (Abs _ _ (App b (Var (Bound 0)))) = Just b
step (App (Var (Free f)) (Var (Free x))) | f == "not" && x == "True" = Just $ Var (Free "False")
step (App (Var (Free f)) (Var (Free x))) | f == "not" && x == "False" = Just $ Var (Free "True")
step _ = Nothing

reduce :: Nameless -> Nameless
reduce t = maybe t reduce (step t)

-- testing
env :: Env
env = Map.fromList
  [
    ("Unit", "Unit"),

    ("True", "Bool"),
    ("False", "Bool"),

    ("not", TFun "Bool" "Bool")
  ]

expr :: Named
expr = App (Abs "x" (TFun "Bool" "Bool") $ Abs "not" "Bool" "x") "not" 

main :: IO ()
main = do
  putStrLn $ show expr
  let expr' = toNameless expr
  putStrLn $ show expr'
  case typecheck env expr' of
    Nothing -> return ()
    Just ty -> do
      putStrLn $ show ty
      let val = reduce expr'
      putStrLn $ show val
      case toNamed val of
        Nothing -> return ()
        Just val' -> putStrLn $ show val'
