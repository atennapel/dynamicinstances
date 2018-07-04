import Data.List (find)
import Data.Maybe (isJust, maybe)
import Debug.Trace (trace)

-- ast
data Name
  = Name String
  | Gen String Int
  deriving (Eq)

instance Show Name where
  show (Name x) = x
  show (Gen x n) = x ++ "$" ++ (show n)

data Ty
  = TCon Name
  | TEx Name
  | TFun Ty CompTy
  deriving (Eq)

instance Show Ty where
  show (TCon n) = show n
  show (TEx n) = "^" ++ (show n)
  show (TFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"

containsEx :: Name -> Ty -> Bool
containsEx x (TCon _) = False
containsEx x (TEx y) = x == y
containsEx x (TFun a b) = containsEx x a || containsExComp x b
  
data CompTy = CompTy Ty
  deriving (Eq)

instance Show CompTy where
  show (CompTy t) = show t

containsExComp :: Name -> CompTy -> Bool
containsExComp x (CompTy t) = containsEx x t

data Val
  = Var Name
  | Abs Name (Maybe Ty) Comp
  | Anno Val Ty
  deriving (Eq)

instance Show Val where
  show (Var x) = show x
  show (Abs x (Just t) c) = "(\\(" ++ (show x) ++ " : " ++ (show t) ++ ") -> " ++ (show c) ++ ")"
  show (Abs x Nothing c) = "(\\" ++ (show x) ++ " -> " ++ (show c) ++ ")"
  show (Anno v t) = "(" ++ (show v) ++ " : " ++ (show t) ++ ")"

substVal :: Name -> Val -> Val -> Val
substVal x v s@(Var y) = if x == y then v else s
substVal x v s@(Abs y t c) = if x == y then s else Abs y t (substComp x v c)
substVal x v (Anno w t) = Anno (substVal x v w) t

data Comp
  = Ret Val
  | App Val Val
  | Do Name Comp Comp
  deriving (Eq)

instance Show Comp where
  show (Ret v) = "(return " ++ show v ++ ")"
  show (App a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (Do x a b) = "(" ++ (show x) ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"

substComp :: Name -> Val -> Comp -> Comp
substComp x v (Ret w) = Ret $ substVal x v w
substComp x v (App a b) = App (substVal x v a) (substVal x v b)
substComp x v s@(Do y a b) = if x == y then s else Do y (substComp x v a) (substComp x v b)

-- Monad
type Res t = Either String t

err :: String -> Res t
err m = Left m

notr :: String -> Res t -> Res ()
notr x (Left m) = return ()
notr x (Right v) = err x

check :: String -> Bool -> Res ()
check x True = return ()
check x False = err x

checkMaybe :: String -> Maybe t -> Res t
checkMaybe x (Just v) = Right v
checkMaybe x Nothing = err x

lor :: (t -> Bool) -> (t -> Bool) -> (t -> Bool)
lor a b t = (a t) || (b t)

land :: (t -> Bool) -> (t -> Bool) -> (t -> Bool)
land a b t = (a t) && (b t)

debug :: Show t => t -> Res ()
debug x = trace (show x) (return ())

-- context
data Elem
  = CTCon Name
  | CTEx Name
  | CSolved Name Ty
  | CVar Name Ty
  | CMarker Name
  deriving (Eq)

instance Show Elem where
  show (CTCon x) = show x
  show (CTEx x) = "^" ++ (show x)
  show (CSolved x t) = "^" ++ (show x) ++ " = " ++ (show t)
  show (CVar x t) = (show x) ++ " : " ++ (show t)
  show (CMarker x) = "|>^" ++ (show x)

data Context = Context [Elem]
  deriving (Eq)

instance Show Context where
  show (Context es) = show $ reverse es

texs :: Context -> [Name]
texs (Context []) = []
texs (Context (CTEx x : t)) = x : texs (Context t)
texs (Context (CSolved x _ : t)) = x : texs (Context t)
texs (Context (_ : t)) = texs (Context t)

vars :: Context -> [Name]
vars (Context []) = []
vars (Context (CVar x _ : t)) = x : vars (Context t)
vars (Context (_ : t)) = vars (Context t)

ctcon :: Name -> (Elem -> Bool)
ctcon x (CTCon y) | x == y = True
ctcon x _ = False

ctex :: Name -> (Elem -> Bool)
ctex x (CTEx y) | x == y = True
ctex x _ = False

csolved :: Name -> (Elem -> Bool)
csolved x (CSolved y _) | x == y = True
csolved x _ = False

cvar :: Name -> (Elem -> Bool)
cvar x (CVar y _) | x == y = True
cvar x _ = False

cmarker :: Name -> (Elem -> Bool)
cmarker x (CMarker y) | x == y = True
cmarker x _ = False

contains :: Context -> (Elem -> Bool) -> Bool
contains (Context ctx) f = isJust $ find f ctx

findCtx :: Context -> (Elem -> Maybe t) -> Maybe t
findCtx (Context []) f = Nothing
findCtx (Context (h : t)) f = maybe (findCtx (Context t) f) Just (f h)

findSolved :: Context -> Name -> Maybe Ty
findSolved ctx x = findCtx ctx
  (\e -> case e of
    CSolved y t | x == y -> return t
    _ -> Nothing)

findVar :: Context -> Name -> Maybe Ty
findVar ctx x = findCtx ctx
  (\e -> case e of
    CVar y t | x == y -> return t
    _ -> Nothing)

apply :: Context -> Ty -> Ty
apply ctx v@(TEx x) = maybe v (apply ctx) (findSolved ctx x)
apply ctx (TFun a b) = TFun (apply ctx a) (applyComp ctx b)
apply ctx t = t

applyComp :: Context -> CompTy -> CompTy
applyComp ctx (CompTy t) = CompTy $ apply ctx t

comesBefore :: Context -> Name -> Name -> Bool
comesBefore (Context []) a b = False
comesBefore (Context (CTEx x : _)) a b | x == a = False
comesBefore (Context (CTEx x : _)) a b | x == b = True
comesBefore (Context (_ : t)) a b = comesBefore (Context t) a b

add :: Context -> [Elem] -> Context
add (Context c) es = Context $ (reverse es) ++ c

context :: [Elem] -> Context
context es = Context $ reverse es

replace :: Context -> (Elem -> Bool) -> [Elem] -> Context
replace (Context []) f es = Context []
replace (Context (h : t)) f es =
  if f h then
    add (Context t) es
  else
    add (replace (Context t) f es) [h]

split :: Context -> (Elem -> Bool) -> (Context, Context)
split (Context l) f = let (a, b) = split' [] l in (Context b, Context $ reverse a)
  where
    split' a [] = (a, [])
    split' a (h : t) | f h = (a, t)
    split' a (h : t) = split' (h : a) t

-- fresh names
incName :: Name -> Name
incName (Name x) = Gen x 0
incName (Gen x i) = Gen x (i + 1)

fresh :: [Name] -> Name -> Name
fresh t n = fresh' t
  where
    fresh' [] = n
    fresh' (m : r) | n == m = fresh t (incName n)
    fresh' (_ : r) = fresh' r

freshVar :: Context -> Name -> Name
freshVar ctx x = fresh (vars ctx) x

freshTEx :: Context -> Name -> Name
freshTEx ctx x = fresh (texs ctx) x

isComplete :: Context -> Bool
isComplete (Context []) = True
isComplete (Context (CTEx _ : t)) = False
isComplete (Context (_ : t)) = isComplete (Context t)

-- wellformedness
tyWF :: Context -> Ty -> Res ()
tyWF ctx t@(TCon x) = check ("tcon not found: " ++ (show t)) $ contains ctx (ctcon x)
tyWF ctx t@(TEx x) = check ("tex not found: " ++ (show t)) $ contains ctx (ctex x `lor` csolved x)
tyWF ctx (TFun a b) = do
  tyWF ctx a
  compTyWF ctx b

compTyWF :: Context -> CompTy -> Res ()
compTyWF ctx (CompTy t) = tyWF ctx t

elemWF :: Context -> Elem -> Res ()
elemWF ctx e@(CTCon x) = check ("duplicate tcon " ++ (show x)) $ not $ contains ctx (ctcon x)
elemWF ctx e@(CTEx x) = check ("duplicate tex " ++ (show x)) $ not $ contains ctx (ctex x `lor` csolved x)
elemWF ctx e@(CMarker x) = check ("duplicate marker " ++ (show x)) $ not $ contains ctx (cmarker x `lor` ctex x `lor` csolved x)
elemWF ctx e@(CSolved x t) = do
  check ("duplicate tex " ++ (show x)) $ not $ contains ctx (ctex x `lor` csolved x)
  tyWF ctx t
elemWF ctx e@(CVar x t) = do
  check ("duplicate var " ++ (show e)) $ not $ contains ctx (cvar x)
  tyWF ctx t

contextWF :: Context -> Res ()
contextWF (Context []) = return ()
contextWF (Context (e : r)) = do
  contextWF (Context r)
  elemWF (Context r) e

-- unification
occursCheck :: Name -> Ty -> Res ()
occursCheck x t = check ("occurs check failed " ++ (show x) ++ " in " ++ (show t)) $ not $ containsEx x t

solve :: Context -> Name -> Ty -> Res Context
solve ctx x t = do
  occursCheck x t
  case t of
    TEx y | comesBefore ctx x y ->
      return $ replace ctx (ctex y) [CSolved y (TEx x)]
    _ ->
      return $ replace ctx (ctex x) [CSolved x t]

unify :: Context -> Ty -> Ty -> Res Context
unify ctx a b = do
  debug $ "unify " ++ (show a) ++ " and " ++ (show b)
  contextWF ctx
  tyWF ctx a
  tyWF ctx b
  unify' ctx a b
    where
      unify' ctx (TCon x) (TCon y) | x == y = return ctx
      unify' ctx (TEx x) t = solve ctx x t
      unify' ctx t (TEx x) = solve ctx x t
      unify' ctx (TFun a b) (TFun x y) = do
        ctx' <- unify' ctx a x
        subtype ctx' (applyComp ctx' b) (applyComp ctx' y)
      unify' ctx a b = err $ "failed to unify " ++ (show a) ++ " and " ++ (show b)

subtype :: Context -> CompTy -> CompTy -> Res Context
subtype c (CompTy a) (CompTy b) = unify c a b

-- type inference
synthVal :: Context -> Val -> Res (Context, Ty)
synthVal ctx v = do
  contextWF ctx
  case v of
    Var x -> do
      t <- checkMaybe ("undefined var " ++ (show v)) $ findVar ctx x
      return (ctx, t)
    Abs x (Just t) c -> do
      tyWF ctx t
      let x' = freshVar ctx x
      (ctx', t') <- synthComp (add ctx [CVar x' t]) (substComp x (Var x') c)
      return (ctx', TFun t t')
    Abs x Nothing c -> do
      let x' = freshVar ctx x
      let a = freshTEx ctx (Name "a")
      let b = freshTEx ctx (Name "b")
      ctx' <- checkComp (add ctx [CTEx a, CTEx b, CVar x' (TEx a)]) (substComp x (Var x') c) (CompTy $ TEx b)
      return (ctx', apply ctx' $ TFun (TEx a) (CompTy $ TEx b))
    Anno v t -> do
      ctx' <- checkVal ctx v t
      return (ctx', t)

checkVal :: Context -> Val -> Ty -> Res Context
checkVal ctx v t = do
  contextWF ctx
  tyWF ctx t
  case (v, t) of
    (Abs x Nothing c, TFun a b) -> do
      let x' = freshVar ctx x
      checkComp (add ctx [CVar x' a]) (substComp x (Var x') c) b
    (v, t) -> do
      (ctx', t') <- synthVal ctx v
      unify ctx' t' t

synthComp :: Context -> Comp -> Res (Context, CompTy)
synthComp ctx c = do
  contextWF ctx
  case c of
    Ret v -> do
      (ctx', t) <- synthVal ctx v
      return (ctx', CompTy t)
    App a b -> do
      (ctx', t) <- synthVal ctx a
      synthApp ctx' t b
    Do x a b -> do
      let x' = freshVar ctx x
      (ctx', CompTy t) <- inferComp ctx a
      inferComp (add ctx' [CVar x' t]) (substComp x (Var x') b)

checkComp :: Context -> Comp -> CompTy -> Res Context
checkComp ctx c t = do
  contextWF ctx
  compTyWF ctx t
  case c of
    _ -> do
      (ctx', t') <- synthComp ctx c
      subtype ctx' (applyComp ctx' t') (applyComp ctx' t)

synthApp :: Context -> Ty -> Val -> Res (Context, CompTy)
synthApp ctx t v = do
  contextWF ctx
  tyWF ctx t
  case t of
    TFun a b -> do
      ctx' <- checkVal ctx v a
      return (ctx', b)
    TEx x -> do
      let a1 = freshTEx ctx x
      let a2 = freshTEx (add ctx [CTEx a1]) x
      ctx' <- checkVal (replace ctx (ctex x) [CTEx a2, CTEx a1, CSolved x (TFun (TEx a1) (CompTy $ TEx a2))]) v (TEx a1)
      return (ctx', CompTy $ TEx a2)
    _ -> err $ "cannot synthApp " ++ (show t)

inferComp :: Context -> Comp -> Res (Context, CompTy)
inferComp ctx c = do
  contextWF ctx
  let a = freshTEx ctx (Name "a")
  (ctx', t) <- synthComp (add ctx [CMarker a]) c
  debug $ t
  let (l, r) = split ctx' (cmarker a)
  debug $ r
  check ("incomplete context " ++ (show r)) $ isComplete r
  return (l, applyComp ctx' t)

-- test
initialCtx :: Context
initialCtx = context
  [
    CTCon (Name "Unit"),
    CVar (Name "Unit") (TCon $ Name "Unit"),
    CTCon (Name "Bool"),
    CVar (Name "True") (TCon $ Name "Bool"),
    CVar (Name "False") (TCon $ Name "Bool")
  ]

x = Name "x"
vx = Var x
prog = App (Abs x Nothing (Ret vx)) (Var $ Name "True")
main = putStrLn $ show $ inferComp initialCtx prog
