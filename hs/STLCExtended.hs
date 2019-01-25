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

data Lit
  = LBool Bool
  | LInt Int
  deriving (Eq)

instance Show Lit where
  show (LBool b) = show b
  show (LInt i) = show i

data Prim
  = PEq
  | PAdd
  | PMul
  | PSub
  | PDiv
  deriving (Eq)

instance Show Prim where
  show PEq = "eq"
  show PAdd = "add"
  show PMul = "mul"
  show PSub = "sub"
  show PDiv = "div"

data Term n
  = Var n
  | Abs Name Type (Term n)
  | App (Term n) (Term n)
  | If (Term n) (Term n) (Term n)
  | Fix (Term n)
  | Lit Lit
  | Prim Prim
  deriving (Eq)

instance Show n => Show (Term n) where
  show (Var n) = show n
  show (Abs x ty b) = "(\\(" ++ (show x) ++ " : " ++ (show ty) ++ "). " ++ (show b) ++ ")"
  show (App a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (If c a b) = "(if " ++ (show c) ++ " then " ++ (show a) ++ " else " ++ (show b) ++ ")"
  show (Fix a) = "(fix " ++ (show a) ++ ")"
  show (Lit l) = show l
  show (Prim p) = show p

instance IsString n => IsString (Term n) where
  fromString = Var . fromString

hasVar :: Eq n => n -> Term n -> Bool
hasVar x (Var y) = x == y
hasVar x (Abs _ _ b) = hasVar x b
hasVar x (App a b) = hasVar x a || hasVar x b
hasVar x (If c a b) = hasVar x c || hasVar x a || hasVar x b
hasVar x (Fix a) = hasVar x a
hasVar _ _ = False

type Index = Int
data Var
  = Bound Index
  | Free Name
  deriving (Eq)

instance Show Var where
  show (Bound i) = "'" ++ (show i)
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
    go lv m (If c a b) = If (go lv m c) (go lv m a) (go lv m b)
    go lv m (Fix a) = Fix (go lv m a)
    go _ _ (Lit l) = Lit l
    go _ _ (Prim p) = Prim p

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
free (Var (Free x)) = Set.singleton x
free (Abs _ _ b) = free b
free (App a b) = Set.union (free a) (free b)
free (If c a b) = Set.union (free c) $ Set.union (free a) (free b)
free (Fix a) = free a
free _ = Set.empty

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
    go ix (If c a b) = If <$> (go ix c) <*> (go ix a) <*> (go ix b)
    go ix (Fix a) = Fix <$> go ix a
    go _ (Lit l) = Just (Lit l)
    go _ (Prim p) = Just (Prim p)

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
typecheckR env ctx (If c a b) = do
  TConst x <- typecheckR env ctx c
  ta <- typecheckR env ctx a
  tb <- typecheckR env ctx b
  whenBool (x == "Bool" && ta == tb) ta
typecheckR env ctx (Fix a) = do
  TFun a b <- typecheckR env ctx a
  whenBool (a == b) a
typecheckR _ _ (Lit (LBool _)) = Just (TConst "Bool")
typecheckR _ _ (Lit (LInt _)) = Just (TConst "Int")
typecheckR _ _ (Prim PEq) = Just (TFun "Int" $ TFun "Int" "Bool")
typecheckR _ _ (Prim PAdd) = Just (TFun "Int" $ TFun "Int" "Int")
typecheckR _ _ (Prim PMul) = Just (TFun "Int" $ TFun "Int" "Int")
typecheckR _ _ (Prim PSub) = Just (TFun "Int" $ TFun "Int" "Int")
typecheckR _ _ (Prim PDiv) = Just (TFun "Int" $ TFun "Int" "Int")

typecheck :: Env -> Nameless -> Maybe Type
typecheck e t = typecheckR e [] t

-- eta/beta reduction
shift :: Index -> Index -> Nameless -> Nameless
shift d c (Var (Bound k)) = Var $ Bound (if k < c then k else k + d)
shift d c (Abs x ty b) = Abs x ty $ shift d (c + 1) b
shift d c (App a b) = App (shift d c a) (shift d c b)
shift d c (If co a b) = If (shift d c co) (shift d c a) (shift d c b)
shift d c (Fix a) = Fix (shift d c a)
shift _ _ v = v

subst :: Index -> Nameless -> Nameless -> Nameless
subst j s v@(Var (Bound k)) = if k == j then s else v
subst j s (Abs x ty b) = Abs x ty $ subst (j + 1) (shift 1 0 s) b
subst j s (App a b) = App (subst j s a) (subst j s b)
subst j s (If c a b) = If (subst j s c) (subst j s a) (subst j s b)
subst j s (Fix a) = Fix (subst j s a)
subst _ _ v = v

substTop :: Nameless -> Nameless -> Nameless
substTop s b = shift (-1) 0 (subst 0 (shift 1 0 s) b)

step :: Nameless -> Maybe Nameless
step (App (Abs _ _ b) v) = return $ substTop v b
step (Abs _ _ (App b (Var (Bound 0)))) = return b
step (Abs x ty b) =
  case step b of
    Just b' -> return $ Abs x ty b'
    Nothing -> Nothing
step (If (Lit (LBool True)) a _) = return a
step (If (Lit (LBool False)) _ b) = return b
step (If c a b) = If <$> (step c) <*> (return a) <*> (return b)
step (App (Fix f) x) = return $ App (App f (Fix f)) x
step (App (App (Prim PEq) (Lit (LInt x))) (Lit (LInt y))) = return (Lit (LBool (x == y)))
step (App (App (Prim PAdd) (Lit (LInt x))) (Lit (LInt y))) = return (Lit (LInt (x + y)))
step (App (App (Prim PMul) (Lit (LInt x))) (Lit (LInt y))) = return (Lit (LInt (x * y)))
step (App (App (Prim PSub) (Lit (LInt x))) (Lit (LInt y))) = return (Lit (LInt (x - y)))
step (App (App (Prim PDiv) (Lit (LInt x))) (Lit (LInt y))) = return (Lit (LInt (quot x y)))
step (App a b) =
  case step a of
    Just a' -> return (App a' b)
    Nothing ->
      case step b of
        Just b' -> return (App a b')
        Nothing -> Nothing
step _ = Nothing

reduce :: Nameless -> Nameless
reduce t = maybe t reduce (step t)

-- testing
env :: Env
env = Map.fromList []

vFalse = Lit $ LBool False
vTrue = Lit $ LBool True
vInt n = Lit $ LInt n
pEq x y = App (App (Prim PEq) x) y
pAdd x y = App (App (Prim PAdd) x) y
pMul x y = App (App (Prim PMul) x) y
pSub x y = App (App (Prim PSub) x) y
pDiv x y = App (App (Prim PDiv) x) y

vpow = Fix $ Abs "f" (TFun "Int" $ TFun "Int" "Int") $ Abs "n" "Int" $ Abs "x" "Int" $
  If (pEq "n" (vInt 0)) (vInt 1)
    (pMul "x" (App (App "f" (pSub "n" (vInt 1))) "x"))

expr :: Named
--expr = Fix $ Abs "f" (TFun "Int" "Int") $ Abs "x" "Int" $ If (pEq "x" (vInt 0)) (vInt 1) (pMul "x" (App "f" (pSub "x" (vInt 1))))
expr = App vpow (vInt 3)

main :: IO ()
main = do
  putStrLn $ show expr
  let expr' = toNameless expr
  putStrLn $ show expr'
  case typecheck env expr' of
    Nothing -> putStrLn "typecheck failed"
    Just ty -> do
      putStrLn $ show ty
      let val = reduce expr'
      putStrLn $ show val
      case toNamed val of
        Nothing -> return ()
        Just val' -> putStrLn $ show val'
