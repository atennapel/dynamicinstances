{-# LANGUAGE OverloadedStrings #-}

import GHC.Exts (IsString(..))
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Control.Monad (when)
import Control.Monad.State (State, get, put, runState, evalState)

import Debug.Trace (traceShowId, traceShow, trace)

-- names
data Name
  = Name String
  | Gen String Int
  deriving (Eq, Ord)

instance Show Name where
  show (Name x) = x
  show (Gen x i) = x ++ "$" ++ (show i)

instance IsString Name where
  fromString = Name

incName :: Name -> Name
incName (Name x) = Gen x 0
incName (Gen x i) = Gen x (i + 1)

freshName :: Set Name -> Name -> Name
freshName s x = if Set.member x s then freshName s (incName x) else x

-- HasTVar
class HasTVar t where
  openTyR :: Int -> Ty -> t -> t
  closeTyR :: Int -> Name -> t -> t
  isLocallyClosedTyR :: Int -> t -> Bool
  freeTVars :: t -> Set Name

openTy :: HasTVar t => Ty -> t -> t
openTy = openTyR 0

closeTy :: HasTVar t => Name -> t -> t
closeTy = closeTyR 0

isLocallyClosedTy :: HasTVar t => t -> Bool
isLocallyClosedTy = isLocallyClosedTyR 0

openTVar :: HasTVar t => Name -> t -> t
openTVar x t = openTy (TVar $ Free x) t

substTVar :: HasTVar t => Name -> Ty -> t -> t
substTVar x u = openTy u . closeTy x

isClosedTy :: HasTVar t => t -> Bool
isClosedTy = Set.null . freeTVars

freshInTy :: HasTVar t => Name -> t -> Bool
freshInTy x t = Set.notMember x $ freeTVars t

freshTVar :: HasTVar t => t -> Name -> Name
freshTVar t x = freshName (freeTVars t) x

-- HasVar
class HasVar t where
  openR :: Int -> Expr -> t -> t
  closeR :: Int -> Name -> t -> t
  isLocallyClosedR :: Int -> t -> Bool
  freeVars :: t -> Set Name

open :: HasVar t => Expr -> t -> t
open = openR 0

close :: HasVar t => Name -> t -> t
close = closeR 0

isLocallyClosed :: HasVar t => t -> Bool
isLocallyClosed = isLocallyClosedR 0

openVar :: HasVar t => Name -> t -> t
openVar x t = open (Var $ Free x) t

substVar :: HasVar t => Name -> Expr -> t -> t
substVar x u = open u . close x

isClosed :: HasVar t => t -> Bool
isClosed = Set.null . freeVars

freshIn :: HasVar t => Name -> t -> Bool
freshIn x t = Set.notMember x $ freeVars t

freshVar :: HasVar t => t -> Name -> Name
freshVar t x = freshName (freeVars t) x

-- vars
data Var
  = Bound Int
  | Free Name
  deriving (Eq, Ord)

instance Show Var where
  show (Bound i) = "'" ++ (show i)
  show (Free x) = show x

instance IsString Var where
  fromString = Free . Name

-- kinds
data Kind
  = KVar Name
  | KFun Kind Kind
  deriving (Eq)

instance Show Kind where
  show (KVar x) = show x
  show (KFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"

instance IsString Kind where
  fromString = KVar . Name

-- types
data Ty
  -- value types
  = TVar Var
  | TApp Ty Ty
  | TForall Name Kind Ty
  -- computation types
  | TComp Ty

instance Show Ty where
  show (TVar x) = show x
  show (TApp a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (TForall x t b) = "(forall(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"

  show (TComp b) = show b

instance Eq Ty where
  TVar x == TVar y = x == y
  TApp a1 b1 == TApp a2 b2 = a1 == a2 && b1 == b2
  TForall _ k1 t1 == TForall _ k2 t2 = k1 == k2 && t1 == t2

  TComp t1 == TComp t2 = t1 == t2

  _ == _ = False

instance IsString Ty where
  fromString = TVar . Free . Name

instance HasTVar Ty where
  openTyR k u t@(TVar (Bound m)) = if m == k then u else t
  openTyR k u t@(TVar _) = t
  openTyR k u (TApp a b) = TApp (openTyR k u a) (openTyR k u b)
  openTyR k u (TForall n ki c) = TForall n ki $ openTyR (k + 1) u c
  openTyR k u (TComp t) = TComp $ openTyR k u t

  closeTyR k x t@(TVar (Bound m)) = t
  closeTyR k x t@(TVar (Free y)) = if x == y then TVar (Bound k) else t
  closeTyR k x (TApp a b) = TApp (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (TForall n ki c) = TForall n ki $ closeTyR (k + 1) x c
  closeTyR k x (TComp t) = TComp $ closeTyR k x t

  isLocallyClosedTyR k (TVar (Bound m)) = m < k
  isLocallyClosedTyR k (TVar _) = True
  isLocallyClosedTyR k (TApp a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (TForall n ki c) = isLocallyClosedTyR (k + 1) c
  isLocallyClosedTyR k (TComp t) = isLocallyClosedTyR k t

  freeTVars (TVar (Bound _)) = Set.empty
  freeTVars (TVar (Free x)) = Set.singleton x
  freeTVars (TApp a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (TForall n ki c) = freeTVars c
  freeTVars (TComp t) = freeTVars t

toNamelessTy :: Ty -> Ty
toNamelessTy t@(TVar _) = t
toNamelessTy (TApp a b) = TApp (toNamelessTy a) (toNamelessTy b)
toNamelessTy (TForall n k t) = TForall n k $ toNamelessTy (closeTy n t)
toNamelessTy (TComp t) = TComp $ toNamelessTy t

toNamedTy :: Ty -> Ty
toNamedTy t@(TVar _) = t
toNamedTy (TApp a b) = TApp (toNamedTy a) (toNamedTy b)
toNamedTy (TForall n k t) = TForall n k $ toNamedTy (openTVar n t)
toNamedTy (TComp t) = TComp $ toNamedTy t

-- exprs
data Expr
  -- values
  = Var Var
  | Abs Name (Maybe Ty) Expr
  | AbsT Name Kind Expr
  | Anno Expr Ty
  -- computations
  | Return Expr
  | App Expr Expr
  | AppT Expr Ty
  | Do Name Expr Expr

instance Show Expr where
  show (Var x) = show x
  show (Abs x (Just t) b) = "(\\(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"
  show (Abs x Nothing b) = "(\\" ++ (show x) ++ ". " ++ (show b) ++ ")"
  show (AbsT x t b) = "(/\\(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"
  show (Anno b t) = "(" ++ (show b) ++ " : " ++ (show t) ++ ")"

  show (Return v) = "(return " ++ (show v) ++ ")"
  show (App a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (AppT a t) = "(" ++ (show a) ++ " [" ++ (show t) ++ "])"
  show (Do x a b) = "(" ++ (show x) ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"

instance Eq Expr where
  Var x == Var y = x == y
  Abs _ t1 e1 == Abs _ t2 e2 = t1 == t2 && e1 == e2
  AbsT _ t1 e1 == AbsT _ t2 e2 = t1 == t2 && e1 == e2
  Anno e1 t1 == Anno e2 t2 = e1 == e2 && t1 == t2

  Return e1 == Return e2 = e1 == e2
  App a1 b1 == App a2 b2 = a1 == a2 && b1 == b2
  AppT a1 b1 == AppT a2 b2 = a1 == a2 && b1 == b2
  Do _ a1 b1 == Do _ a2 b2 = a1 == a2 && b1 == b2

instance IsString Expr where
  fromString = Var . Free . Name

instance HasVar Expr where
  openR k u t@(Var (Bound m)) = if m == k then u else t
  openR k u t@(Var (Free _)) = t
  openR k u (Abs n t c) = Abs n t $ openR (k + 1) u c
  openR k u (AbsT n ki c) = AbsT n ki $ openR k u c
  openR k u t@(Anno e t') = Anno (openR k u e) t'

  openR k u (Return v) = Return (openR k u v)
  openR k u (App a b) = App (openR k u a) (openR k u b)
  openR k u (AppT a b) = AppT (openR k u a) b
  openR k u (Do n a b) = Do n (openR k u a) (openR (k + 1) u b)

  closeR _ _ t@(Var (Bound _)) = t
  closeR k x t@(Var (Free y)) = if x == y then Var (Bound k) else t
  closeR k x (Abs n t c) = Abs n t $ closeR (k + 1) x c
  closeR k x (AbsT n ki c) = AbsT n ki $ closeR k x c
  closeR k x t@(Anno e t') = Anno (closeR k x e) t'

  closeR k u (Return v) = Return (closeR k u v)
  closeR k u (App a b) = App (closeR k u a) (closeR k u b)
  closeR k u (AppT a b) = AppT (closeR k u a) b
  closeR k u (Do n a b) = Do n (closeR k u a) (closeR (k + 1) u b)

  isLocallyClosedR k (Var (Bound m)) = m < k
  isLocallyClosedR k (Var (Free _)) = True
  isLocallyClosedR k (Abs n t c) = isLocallyClosedR (k + 1) c
  isLocallyClosedR k (AbsT n ki c) = isLocallyClosedR k c
  isLocallyClosedR k (Anno e t') = isLocallyClosedR k e

  isLocallyClosedR k (Return v) = isLocallyClosedR k v
  isLocallyClosedR k (App a b) = isLocallyClosedR k a && isLocallyClosedR k b
  isLocallyClosedR k (AppT a b) = isLocallyClosedR k a
  isLocallyClosedR k (Do n a b) = isLocallyClosedR k a && isLocallyClosedR (k + 1) b

  freeVars (Var (Bound _)) = Set.empty
  freeVars (Var (Free x)) = Set.singleton x
  freeVars (Abs n t c) = freeVars c
  freeVars (AbsT n ki c) = freeVars c
  freeVars (Anno e t) = freeVars e

  freeVars (Return v) = freeVars v
  freeVars (App a b) = Set.union (freeVars a) (freeVars b)
  freeVars (AppT a b) = freeVars a
  freeVars (Do n a b) = Set.union (freeVars a) (freeVars b)

instance HasTVar Expr where
  openTyR k u t@(Var (Bound _)) = t
  openTyR k u t@(Var (Free _)) = t
  openTyR k u (Abs n t c) = Abs n (fmap (openTyR k u) t) (openTyR k u c)
  openTyR k u (AbsT n ki c) = AbsT n ki $ openTyR (k + 1) u c
  openTyR k u (Anno e t') = Anno (openTyR k u e) (openTyR k u t')

  openTyR k u (Return v) = Return (openTyR k u v)
  openTyR k u (App a b) = App (openTyR k u a) (openTyR k u b)
  openTyR k u (AppT a b) = AppT (openTyR k u a) (openTyR k u b)
  openTyR k u (Do n a b) = Do n (openTyR k u a) (openTyR k u b)

  closeTyR k x t@(Var (Bound _)) = t
  closeTyR k x t@(Var (Free _)) = t
  closeTyR k x (Abs n t c) = Abs n (fmap (closeTyR k x) t) (closeTyR k x c)
  closeTyR k x (AbsT n ki c) = AbsT n ki $ closeTyR (k + 1) x c
  closeTyR k x (Anno e t') = Anno (closeTyR k x e) (closeTyR k x t')

  closeTyR k u (Return v) = Return (closeTyR k u v)
  closeTyR k u (App a b) = App (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (AppT a b) = AppT (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (Do n a b) = Do n (closeTyR k u a) (closeTyR k u b)

  isLocallyClosedTyR k (Var (Bound _)) = True
  isLocallyClosedTyR k (Var (Free _)) = True
  isLocallyClosedTyR k (Abs n t c) = Maybe.maybe True (isLocallyClosedTyR k) t && isLocallyClosedTyR k c
  isLocallyClosedTyR k (AbsT n ki c) = isLocallyClosedTyR (k + 1) c
  isLocallyClosedTyR k (Anno e t') = isLocallyClosedTyR k e && isLocallyClosedTyR k t'

  isLocallyClosedTyR k (Return v) = isLocallyClosedTyR k v
  isLocallyClosedTyR k (App a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (AppT a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Do n a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b

  freeTVars (Var (Bound _)) = Set.empty
  freeTVars (Var (Free _)) = Set.empty
  freeTVars (Abs n t c) = Set.union (Maybe.maybe Set.empty freeTVars t) (freeTVars c)
  freeTVars (AbsT n ki c) = freeTVars c
  freeTVars (Anno e t) = Set.union (freeTVars e) (freeTVars t)

  freeTVars (Return v) = freeTVars v
  freeTVars (App a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (AppT a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Do n a b) = Set.union (freeTVars a) (freeTVars b)

toNameless :: Expr -> Expr
toNameless t@(Var _) = t
toNameless (Abs n t e) = Abs n (fmap toNamelessTy t) (toNameless $ close n e)
toNameless (AbsT n k e) = AbsT n k $ toNameless (closeTy n e)
toNameless (Anno e t) = Anno (toNameless e) (toNamelessTy t)
toNameless (Return e) = Return (toNameless e)
toNameless (App a b) = App (toNameless a) (toNameless b)
toNameless (AppT e t) = AppT (toNameless e) (toNamelessTy t)
toNameless (Do n a b) = Do n (toNameless a) (toNameless $ close n b)

toNamed :: Expr -> Expr
toNamed t@(Var _) = t
toNamed (Abs n t e) = Abs n (fmap toNamedTy t) (toNamed $ openVar n e)
toNamed (AbsT n k e) = AbsT n k $ toNamed (openTVar n e)
toNamed (Anno e t) = Anno (toNamed e) (toNamedTy t)
toNamed (Return e) = Return (toNamed e)
toNamed (App a b) = App (toNamed a) (toNamed b)
toNamed (AppT e t) = AppT (toNamed e) (toNamedTy t)
toNamed (Do n a b) = Do n (toNamed a) (toNamed $ openVar n b)

isVal :: Expr -> Bool
isVal (Var _) = True
isVal (Abs n t e) = True
isVal (AbsT n k e) = True
isVal (Anno e t) = isVal e
isVal (Return e) = False
isVal (App a b) = False
isVal (AppT e t) = False
isVal (Do n a b) = False

isComp :: Expr -> Bool
isComp = not . isVal

desugar :: Expr -> Expr
desugar t@(Var _) = t
desugar (Abs n t e) =
  let e' = desugar e in Abs n t (if isVal e' then Return e' else e')
desugar (AbsT n k e) =
  let e' = desugar e in AbsT n k (if isVal e' then Return e' else e')
desugar (Anno e t) = Anno (desugar e) t
desugar (Return e) =
  let e' = desugar e in
  if isVal e' then
    Return e'
  else
    let x = freshVar e' "d" in
    Do x e' $ Return (Var $ Free x)
desugar (App a b) =
  let a' = desugar a in
  let b' = desugar b in
  if isVal a' then
    if isVal b' then
      App a' b'
    else
      let x = freshName (Set.union (freeVars a') (freeVars b')) "d" in
      Do x b' $ App a' (Var $ Free x)
  else
    if isVal b' then
      let x = freshName (Set.union (freeVars a') (freeVars b')) "d" in
      Do x a' $ App (Var $ Free x) b'
    else
      let f = Set.union (freeVars a') (freeVars b') in
      let x = freshName f "d" in
      let y = freshName (Set.insert x f) "d" in
      Do x a' $ Do y b' $ App (Var $ Free x) (Var $ Free y)
desugar (AppT e t) =
  let e' = desugar e in
  if isVal e' then
    AppT e' t
  else
    let x = freshVar e' "d" in
    Do x e' $ AppT (Var $ Free x) t
desugar (Do n a b) =
  let a' = desugar a in
  let b' = desugar b in
  Do n (if isVal a' then Return a' else a') (if isVal b' then Return b' else b')

isFineGrained :: Expr -> Bool
isFineGrained (Var _) = True
isFineGrained (Abs n t e) = isComp e && isFineGrained e
isFineGrained (AbsT n k e) = isComp e && isFineGrained e
isFineGrained (Anno e t) = isFineGrained e
isFineGrained (Return e) = isVal e && isFineGrained e
isFineGrained (App a b) = isVal a && isVal b && isFineGrained a && isFineGrained b
isFineGrained (AppT e t) = isVal e && isFineGrained e
isFineGrained (Do n a b) = isComp a && isComp b && isFineGrained a && isFineGrained b

-- monad
type TC t = Either String t

err :: String -> TC t
err = Left

tcNot :: String -> TC t -> TC ()
tcNot msg (Left _) = return ()
tcNot msg (Right _) = Left msg

tcBool :: String -> Bool -> TC ()
tcBool msg True = return ()
tcBool msg False = Left msg

tcDrop :: TC t -> TC ()
tcDrop c = do
  c
  return ()

tcMaybe :: String -> Maybe t -> TC t
tcMaybe msg c = Maybe.maybe (Left msg) return c

-- context
data Elem
  = CKVar Name
  | CTVar Name Kind
  | CVar Name Ty
  deriving (Eq)

instance Show Elem where
  show (CKVar x) = "kind " ++ (show x)
  show (CTVar x t) = (show x) ++ " :k " ++ (show t)
  show (CVar x t) = (show x) ++ " : " ++ (show t)

data Context = Context [Elem]
  deriving (Eq)

instance Show Context where
  show (Context ctx) = show (reverse ctx)

context :: [Elem] -> Context
context = Context . reverse

add :: Context -> Elem -> Context
add (Context ctx) e = Context $ e : ctx

adds :: Context -> [Elem] -> Context
adds (Context ctx) es = Context $ (reverse es) ++ ctx

vars :: Context -> Set Name
vars (Context ctx) = Set.fromList $
  Maybe.mapMaybe (\e -> case e of { CVar x _ -> Just x; _ -> Nothing }) ctx

tvars :: Context -> Set Name
tvars (Context ctx) = Set.fromList $
  Maybe.mapMaybe (\e -> case e of { CTVar x _ -> Just x; _ -> Nothing }) ctx

kvars :: Context -> Set Name
kvars (Context ctx) = Set.fromList $
  Maybe.mapMaybe (\e -> case e of { CKVar x -> Just x; _ -> Nothing }) ctx

findElem :: Context -> (Elem -> Maybe t) -> String -> TC t
findElem (Context ctx) f msg = go ctx f msg
  where
    go [] f msg = err msg
    go (h : t) f msg =
      case f h of
        Just x -> return x
        Nothing -> go t f msg

findVar :: Context -> Name -> TC Ty
findVar ctx x = findElem ctx (\e -> case e of { CVar y t | x == y -> Just t; _ -> Nothing }) $ "undefined var " ++ (show x)

findTVar :: Context -> Name -> TC Kind
findTVar ctx x = findElem ctx (\e -> case e of { CTVar y t | x == y -> Just t; _ -> Nothing }) $ "undefined tvar " ++ (show x)

findKVar :: Context -> Name -> TC ()
findKVar ctx x = findElem ctx (\e -> case e of { CKVar y | x == y -> Just (); _ -> Nothing }) $ "undefined kvar " ++ (show x)

freshTVarInContext :: HasTVar t => Context -> t -> Name -> Name
freshTVarInContext ctx t x = freshName (Set.union (tvars ctx) (freeTVars t)) x

freshVarInContext :: HasVar t => Context -> t -> Name -> Name
freshVarInContext ctx t x = freshName (Set.union (vars ctx) (freeVars t)) x

-- initial context
kType :: Kind
kType = "Type"

kComp :: Kind
kComp = "Comp"

tArr :: Ty
tArr = "->"

tfun :: Ty -> Ty -> Ty
tfun a b = TApp (TApp tArr a) b

initialContext :: Context
initialContext = context
  [
    CKVar "Type",
    CKVar "Comp",

    CTVar "->" (KFun kType $ KFun kComp kType)
  ]

checkKind :: Kind -> Kind -> TC ()
checkKind k k' =
  if k == k' then
    return ()
  else
    err $ "expected " ++ (show k) ++ " but got " ++ (show k')

-- wf
wfKind :: Context -> Kind -> TC ()
wfKind ctx (KVar x) = findKVar ctx x
wfKind ctx (KFun a b) = do
  wfKind ctx a
  wfKind ctx b

wfTy :: Context -> Ty -> TC Kind
wfTy ctx t@(TVar (Bound i)) = err $ "not wellformed: " ++ (show t)
wfTy ctx (TVar (Free x)) = findTVar ctx x
wfTy ctx t@(TApp a b) = do
  k <- wfTy ctx a
  case k of
    KFun x y -> do
      k' <- wfTy ctx b
      tcBool ("invalid type application: " ++ (show t)) $ x == k'
      return y
    _ -> err $ "invalid type application: " ++ (show t)
wfTy ctx (TForall n k t) = do
  let x = freshTVarInContext ctx t n
  k <- wfTy (add ctx $ CTVar x k) $ openTVar x t
  checkKind kComp k
  return kType
wfTy ctx (TComp t) = do
  k <- wfTy ctx t
  checkKind kType k
  return kComp

wfElem :: Context -> Elem -> TC ()
wfElem ctx (CKVar x) = tcNot ("duplicate kvar " ++ (show x)) $ findKVar ctx x
wfElem ctx (CTVar x k) = do
  tcNot ("duplicate tvar " ++ (show x)) $ findKVar ctx x
  wfKind ctx k
wfElem ctx (CVar x t) = do
  tcNot ("duplicate var " ++ (show x)) $ findKVar ctx x
  k <- wfTy ctx t
  checkKind kType k

wfContext :: Context -> TC ()
wfContext (Context ctx) = go ctx
  where
    go [] = return ()
    go (h : t) = do
      go t
      wfElem (Context t) h

-- typechecking


  {-
  Var Var
  | Abs Name (Maybe Ty) Expr
  | AbsT Name Kind Expr
  | Anno Expr Ty
  -- computations
  | Return Expr
  | App Expr Expr
  | AppT Expr Ty
  | Do Name Expr Expr
  -}

synth :: Context -> Expr -> TC Ty
synth ctx e = do
  wfContext ctx
  case e of
    Var (Free x) -> findVar ctx x
    Abs n (Just t) e -> do
      k <- wfTy ctx t
      checkKind kType k
      let x = freshVarInContext ctx e n
      tr <- synth (add ctx $ CVar x t) $ openVar x e
      k' <- wfTy ctx tr
      checkKind kComp k'
      return $ tfun t tr
    AbsT n k e -> do
      wfKind ctx k
      let x = freshTVarInContext ctx e n
      let ctx' = add ctx $ CTVar x k
      tr <- synth ctx' $ openTVar x e
      k' <- wfTy ctx' tr
      checkKind kComp k'
      return $ TForall n k $ closeTy x tr
    Anno e t -> do
      check ctx e t
      return t

    Return v -> do
      t <- synth ctx v
      k <- wfTy ctx t
      checkKind kType k
      return $ TComp t
    App a b -> do
      ta <- synth ctx a
      ka <- wfTy ctx ta
      checkKind kType ka
      case ta of
        TApp (TApp c x) y | c == tArr -> do
          check ctx b x
          return y
        _ -> err $ "not a function in application: " ++ (show e)
    AppT a t -> do
      k <- wfTy ctx t
      ta <- synth ctx a
      ka <- wfTy ctx ta
      checkKind kType ka
      case ta of
        TForall n k' b -> do
          checkKind k' k
          return $ openTy t b
        _ -> err $ "not a forall in application: " ++ (show e)
    Do n a b -> do
      ta@(TComp tv) <- synth ctx a
      ka <- wfTy ctx ta
      checkKind kComp ka
      let x = freshVarInContext ctx b n
      tb <- synth (add ctx $ CVar x tv) $ openVar x b
      kb <- wfTy ctx tb
      checkKind kComp kb
      return tb

    _ -> err $ "cannot synth " ++ (show e)

check :: Context -> Expr -> Ty -> TC ()
check ctx e t = do
  wfContext ctx
  wfTy ctx t
  case (e, t) of
    (Abs n Nothing b, TApp (TApp c tx) ty) | c == tArr -> do
      let x = freshVarInContext ctx b n
      check (add ctx $ CVar x tx) (openVar x b) ty
    (e, t) -> do
      t' <- synth ctx e
      tcBool ("type mismatch: " ++ (show t) ++ " and " ++ (show t')) $ t == t'

infer :: Context -> Expr -> TC Ty
infer ctx e = do
  tcBool ("expression not locally closed: " ++ (show e)) $ isLocallyClosed e
  tcBool ("expression is not finegrained: " ++ (show e)) $ isFineGrained e
  wfContext ctx
  t <- synth ctx e
  wfTy ctx t
  return t

-- testing
ctx :: Context
ctx = adds initialContext
  [
    CTVar "Bool" "Type",
    CVar "True" "Bool",
    CVar "False" "Bool"
  ]

term :: Expr
term = Do "f" (AbsT "t" kType $ Abs "x" (Just "t") "x") (AppT "f" "Bool")

-- main
main :: IO ()
main = do
  putStrLn $ show term
  let d = desugar term
  putStrLn $ show d
  let n' = toNameless d
  putStrLn $ show n'
  let t = infer ctx n'
  case t of
    Left m -> putStrLn m
    Right t' -> do
      putStrLn $ show t'
      let nm' = toNamedTy t'
      putStrLn $ show nm'
