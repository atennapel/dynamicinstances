{--
TODO:
  - effects in context
  - operation calls
  - handle computation
--}
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
  openTyR :: Int -> ValTy -> t -> t
  closeTyR :: Int -> Name -> t -> t
  isLocallyClosedTyR :: Int -> t -> Bool
  freeTVars :: t -> Set Name

class NamelessTy t where
  toNamelessTy :: t -> t
  toNamedTy :: t -> t

openTy :: HasTVar t => ValTy -> t -> t
openTy = openTyR 0

closeTy :: HasTVar t => Name -> t -> t
closeTy = closeTyR 0

isLocallyClosedTy :: HasTVar t => t -> Bool
isLocallyClosedTy = isLocallyClosedTyR 0

openTVar :: HasTVar t => Name -> t -> t
openTVar x t = openTy (TVar $ Free x) t

substTVar :: HasTVar t => Name -> ValTy -> t -> t
substTVar x u = openTy u . closeTy x

isClosedTy :: HasTVar t => t -> Bool
isClosedTy = Set.null . freeTVars

freshInTy :: HasTVar t => Name -> t -> Bool
freshInTy x t = Set.notMember x $ freeTVars t

freshTVar :: HasTVar t => t -> Name -> Name
freshTVar t x = freshName (freeTVars t) x

-- HasVar
class HasVar t where
  openR :: Int -> Val -> t -> t
  closeR :: Int -> Name -> t -> t
  isLocallyClosedR :: Int -> t -> Bool
  freeVars :: t -> Set Name

class Nameless t where
  toNameless :: t -> t
  toNamed :: t -> t

open :: HasVar t => Val -> t -> t
open = openR 0

close :: HasVar t => Name -> t -> t
close = closeR 0

isLocallyClosed :: HasVar t => t -> Bool
isLocallyClosed = isLocallyClosedR 0

openVar :: HasVar t => Name -> t -> t
openVar x t = open (Var $ Free x) t

substVar :: HasVar t => Name -> Val -> t -> t
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

-- value types
type Label = String
data ValTy
  = TVar Var
  | TFun ValTy CompTy
  | TForall Name Kind CompTy
  | TEmpty
  | TExtend Label ValTy 

rowToLabels :: ValTy -> ([Label], ValTy)
rowToLabels (TExtend l r) =
  let (ls, r') = rowToLabels r in
  (l : ls, r')
rowToLabels t = ([], t)

instance Show ValTy where
  show (TVar x) = show x
  show (TFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"
  show (TForall x t b) = "(forall(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"
  show TEmpty = "{}"
  show t@(TExtend _ _) =
    let (ls, r) = rowToLabels t in
    case r of
      TEmpty -> "{" ++ (intercalate "," ls) ++ "}"
      _ -> "{" ++ (intercalate ", " ls) ++ " | " ++ (show r) ++ "}"

instance IsString ValTy where
  fromString = TVar . Free . Name

instance HasTVar ValTy where
  openTyR k u t@(TVar (Bound m)) = if m == k then u else t
  openTyR k u t@(TVar _) = t
  openTyR k u (TFun a b) = TFun (openTyR k u a) (openTyR k u b)
  openTyR k u (TForall n ki c) = TForall n ki $ openTyR (k + 1) u c
  openTyR k u t@TEmpty = t
  openTyR k u (TExtend l t) = TExtend l $ openTyR k u t

  closeTyR k x t@(TVar (Bound m)) = t
  closeTyR k x t@(TVar (Free y)) = if x == y then TVar (Bound k) else t
  closeTyR k x (TFun a b) = TFun (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (TForall n ki c) = TForall n ki $ closeTyR (k + 1) x c
  closeTyR k x t@TEmpty = t
  closeTyR k x (TExtend l t) = TExtend l $ closeTyR k x t

  isLocallyClosedTyR k (TVar (Bound m)) = m < k
  isLocallyClosedTyR k (TVar _) = True
  isLocallyClosedTyR k (TFun a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (TForall n ki c) = isLocallyClosedTyR (k + 1) c
  isLocallyClosedTyR k TEmpty = True
  isLocallyClosedTyR k (TExtend l t) = isLocallyClosedTyR k t

  freeTVars (TVar (Bound _)) = Set.empty
  freeTVars (TVar (Free x)) = Set.singleton x
  freeTVars (TFun a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (TForall n ki c) = freeTVars c
  freeTVars TEmpty = Set.empty
  freeTVars (TExtend l t) = freeTVars t

instance NamelessTy ValTy where
  toNamelessTy t@(TVar _) = t
  toNamelessTy (TFun a b) = TFun (toNamelessTy a) (toNamelessTy b)
  toNamelessTy (TForall n k t) = TForall n k $ toNamelessTy (closeTy n t)
  toNamelessTy t@TEmpty = t
  toNamelessTy (TExtend l t) = TExtend l $ toNamelessTy t

  toNamedTy t@(TVar _) = t
  toNamedTy (TFun a b) = TFun (toNamedTy a) (toNamedTy b)
  toNamedTy (TForall n k t) = TForall n k $ toNamedTy (openTVar n t)
  toNamedTy t@TEmpty = t
  toNamedTy (TExtend l t) = TExtend l $ toNamedTy t

-- computation types
data CompTy
  = TAnnot ValTy ValTy

instance Show CompTy where
  show (TAnnot t TEmpty) = show t
  show (TAnnot t r) = (show t) ++ "!" ++ (show r)

instance IsString CompTy where
  fromString x = TAnnot (TVar $ Free $ Name x) TEmpty

instance HasTVar CompTy where
  openTyR k u (TAnnot t r) = TAnnot (openTyR k u t) (openTyR k u r)

  closeTyR k x (TAnnot t r) = TAnnot (closeTyR k x t) (closeTyR k x r)

  isLocallyClosedTyR k (TAnnot t r) = isLocallyClosedTyR k t && isLocallyClosedTyR k r

  freeTVars (TAnnot t r) = Set.union (freeTVars t) (freeTVars r)

instance NamelessTy CompTy where
  toNamelessTy (TAnnot a b) = TAnnot (toNamelessTy a) (toNamelessTy b)

  toNamedTy (TAnnot a b) = TAnnot (toNamedTy a) (toNamedTy b)

-- values
data Val
  = Var Var
  | Abs Name ValTy Comp
  | AbsT Name Kind Comp
  | Open Comp

instance Show Val where
  show (Var x) = show x
  show (Abs x t b) = "(\\(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"
  show (AbsT x t b) = "(/\\(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"
  show (Open c) = "(open " ++ (show c) ++ ")"

instance IsString Val where
  fromString = Var . Free . Name

instance HasVar Val where
  openR k u t@(Var (Bound m)) = if m == k then u else t
  openR k u t@(Var (Free _)) = t
  openR k u (Abs n t c) = Abs n t $ openR (k + 1) u c
  openR k u (AbsT n ki c) = AbsT n ki $ openR k u c
  openR k u (Open c) = Open $ openR k u c

  closeR _ _ t@(Var (Bound _)) = t
  closeR k x t@(Var (Free y)) = if x == y then Var (Bound k) else t
  closeR k x (Abs n t c) = Abs n t $ closeR (k + 1) x c
  closeR k x (AbsT n ki c) = AbsT n ki $ closeR k x c
  closeR k u (Open c) = Open $ closeR k u c

  isLocallyClosedR k (Var (Bound m)) = m < k
  isLocallyClosedR k (Var (Free _)) = True
  isLocallyClosedR k (Abs n t c) = isLocallyClosedR (k + 1) c
  isLocallyClosedR k (AbsT n ki c) = isLocallyClosedR k c
  isLocallyClosedR k (Open c) = isLocallyClosedR k c

  freeVars (Var (Bound _)) = Set.empty
  freeVars (Var (Free x)) = Set.singleton x
  freeVars (Abs n t c) = freeVars c
  freeVars (AbsT n ki c) = freeVars c
  freeVars (Open c) = freeVars c

instance HasTVar Val where
  openTyR k u t@(Var (Bound _)) = t
  openTyR k u t@(Var (Free _)) = t
  openTyR k u (Abs n t c) = Abs n (openTyR k u t) (openTyR k u c)
  openTyR k u (AbsT n ki c) = AbsT n ki $ openTyR (k + 1) u c
  openTyR k u (Open c) = Open $ openTyR k u c

  closeTyR k x t@(Var (Bound _)) = t
  closeTyR k x t@(Var (Free _)) = t
  closeTyR k x (Abs n t c) = Abs n (closeTyR k x t) (closeTyR k x c)
  closeTyR k x (AbsT n ki c) = AbsT n ki $ closeTyR (k + 1) x c
  closeTyR k u (Open c) = Open $ closeTyR k u c

  isLocallyClosedTyR k (Var (Bound _)) = True
  isLocallyClosedTyR k (Var (Free _)) = True
  isLocallyClosedTyR k (Abs n t c) = isLocallyClosedTyR k t && isLocallyClosedTyR k c
  isLocallyClosedTyR k (AbsT n ki c) = isLocallyClosedTyR (k + 1) c
  isLocallyClosedTyR k (Open c) = isLocallyClosedTyR k c

  freeTVars (Var (Bound _)) = Set.empty
  freeTVars (Var (Free _)) = Set.empty
  freeTVars (Abs n t c) = Set.union (freeTVars t) (freeTVars c)
  freeTVars (AbsT n ki c) = freeTVars c
  freeTVars (Open c) = freeTVars c

instance Nameless Val where
  toNameless t@(Var _) = t
  toNameless (Abs n t e) = Abs n (toNamelessTy t) (toNameless $ close n e)
  toNameless (AbsT n k e) = AbsT n k $ toNameless (closeTy n e)
  toNameless (Open c) = Open $ toNameless c

  toNamed t@(Var _) = t
  toNamed (Abs n t e) = Abs n (toNamedTy t) (toNamed $ openVar n e)
  toNamed (AbsT n k e) = AbsT n k $ toNamed (openTVar n e)
  toNamed (Open c) = Open $ toNamed c

-- computations
data Comp
  = Return Val
  | App Val Val
  | AppT Val ValTy
  | Do Name Comp Comp

instance Show Comp where
  show (Return v) = "(return " ++ (show v) ++ ")"
  show (App a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (AppT a t) = "(" ++ (show a) ++ " [" ++ (show t) ++ "])"
  show (Do x a b) = "(" ++ (show x) ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"

instance IsString Comp where
  fromString = Return . Var . Free . Name

instance HasVar Comp where
  openR k u (Return v) = Return (openR k u v)
  openR k u (App a b) = App (openR k u a) (openR k u b)
  openR k u (AppT a b) = AppT (openR k u a) b
  openR k u (Do n a b) = Do n (openR k u a) (openR (k + 1) u b)

  closeR k u (Return v) = Return (closeR k u v)
  closeR k u (App a b) = App (closeR k u a) (closeR k u b)
  closeR k u (AppT a b) = AppT (closeR k u a) b
  closeR k u (Do n a b) = Do n (closeR k u a) (closeR (k + 1) u b)

  isLocallyClosedR k (Return v) = isLocallyClosedR k v
  isLocallyClosedR k (App a b) = isLocallyClosedR k a && isLocallyClosedR k b
  isLocallyClosedR k (AppT a b) = isLocallyClosedR k a
  isLocallyClosedR k (Do n a b) = isLocallyClosedR k a && isLocallyClosedR (k + 1) b

  freeVars (Return v) = freeVars v
  freeVars (App a b) = Set.union (freeVars a) (freeVars b)
  freeVars (AppT a b) = freeVars a
  freeVars (Do n a b) = Set.union (freeVars a) (freeVars b)

instance HasTVar Comp where
  openTyR k u (Return v) = Return (openTyR k u v)
  openTyR k u (App a b) = App (openTyR k u a) (openTyR k u b)
  openTyR k u (AppT a b) = AppT (openTyR k u a) (openTyR k u b)
  openTyR k u (Do n a b) = Do n (openTyR k u a) (openTyR k u b)

  closeTyR k u (Return v) = Return (closeTyR k u v)
  closeTyR k u (App a b) = App (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (AppT a b) = AppT (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (Do n a b) = Do n (closeTyR k u a) (closeTyR k u b)

  isLocallyClosedTyR k (Return v) = isLocallyClosedTyR k v
  isLocallyClosedTyR k (App a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (AppT a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Do n a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b

  freeTVars (Return v) = freeTVars v
  freeTVars (App a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (AppT a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Do n a b) = Set.union (freeTVars a) (freeTVars b)

instance Nameless Comp where
  toNameless (Return e) = Return (toNameless e)
  toNameless (App a b) = App (toNameless a) (toNameless b)
  toNameless (AppT e t) = AppT (toNameless e) (toNamelessTy t)
  toNameless (Do n a b) = Do n (toNameless a) (toNameless $ close n b)

  toNamed (Return e) = Return (toNamed e)
  toNamed (App a b) = App (toNamed a) (toNamed b)
  toNamed (AppT e t) = AppT (toNamed e) (toNamedTy t)
  toNamed (Do n a b) = Do n (toNamed a) (toNamed $ openVar n b)

-- type checking monad
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
  | CVar Name ValTy

instance Show Elem where
  show (CKVar x) = "kind " ++ (show x)
  show (CTVar x t) = (show x) ++ " :k " ++ (show t)
  show (CVar x t) = (show x) ++ " : " ++ (show t)

data Context = Context [Elem]

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

findVar :: Context -> Name -> TC ValTy
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

kEffs :: Kind
kEffs = "Effs"

initialContext :: Context
initialContext = context
  [
    CKVar "Type",
    CKVar "Effs"
  ]

-- util
checkKind :: Kind -> Kind -> String -> TC ()
checkKind k k' msg =
  if k == k' then
    return ()
  else
    err $ "kind mismatch: expected " ++ (show k) ++ " but got " ++ (show k') ++ " in " ++ msg
  
-- subtyping
rowToSet :: ValTy -> String -> TC (Set Label, ValTy)
rowToSet t@(TVar _) msg = return (Set.empty, t)
rowToSet t@TEmpty msg = return (Set.empty, t)
rowToSet (TExtend l r) msg = do
  (s, t) <- rowToSet r msg
  return (Set.insert l s, t)
rowToSet t msg = err $ "invalid type in rowToSet " ++ (show t) ++ " in " ++ msg

rowFromSet :: Foldable f => f Label -> ValTy -> ValTy
rowFromSet s r = foldr TExtend r s

eqValTy :: ValTy -> ValTy -> String -> TC ()
eqValTy (TVar v1) (TVar v2) msg | v1 == v2 = return ()
eqValTy (TFun a1 b1) (TFun a2 b2) msg = do
  eqValTy a1 a2 msg
  eqCompTy b1 b2 msg
eqValTy f1@(TForall n1 k1 t1) f2@(TForall n2 k2 t2) msg = do
  checkKind k1 k2 $ "kind mismatch in " ++ (show f1) ++ " <: " ++ (show f2) ++ " in " ++ msg
  let x = freshName (Set.union (freeTVars t1) (freeTVars t2)) n1
  eqCompTy (openTVar x t1) (openTVar x t2) msg
eqValTy TEmpty TEmpty msg = return ()
eqValTy t1@(TExtend _ _) t2@(TExtend _ _) msg = do
  (s1, r1) <- rowToSet t1 msg
  (s2, r2) <- rowToSet t2 msg
  tcBool ("type equality failed for effs: " ++ (show t1) ++ " and " ++ (show t2) ++ " in " ++ msg) $ s1 == s2
  eqValTy r1 r2 msg
eqValTy x y msg = err $ "type equality failed: expected " ++ (show x) ++ " but got " ++ (show y) ++ " in " ++ msg

eqCompTy :: CompTy -> CompTy -> String -> TC ()
eqCompTy (TAnnot t1 r1) (TAnnot t2 r2) msg = do
  eqValTy t1 t2 msg
  eqValTy r1 r2 msg

-- wf
wfKind :: Context -> Kind -> TC ()
wfKind ctx (KVar x) = findKVar ctx x
wfKind ctx (KFun a b) = do
  wfKind ctx a
  wfKind ctx b

wfValTy :: Context -> ValTy -> TC Kind
wfValTy ctx t@(TVar (Bound i)) = err $ "not wellformed: " ++ (show t)
wfValTy ctx (TVar (Free x)) = findTVar ctx x
wfValTy ctx t@(TFun a b) = do
  k1 <- wfValTy ctx a
  checkKind kType k1 $ "left side of function type " ++ (show t)
  k2 <- wfCompTy ctx b
  checkKind kType k2 $ "right side of function type " ++ (show t)
  return kType
wfValTy ctx (TForall n k t) = do
  let x = freshTVarInContext ctx t n
  wfCompTy (add ctx $ CTVar x k) $ openTVar x t
wfValTy ctx TEmpty = return kEffs
wfValTy ctx t@(TExtend l r) = do
  k <- wfValTy ctx r
  checkKind kEffs k $ "effects extend rest: " ++ (show t)
  return kEffs

wfCompTy :: Context -> CompTy -> TC Kind
wfCompTy ctx ct@(TAnnot t r) = do
  kt <- wfValTy ctx t
  kr <- wfValTy ctx r
  checkKind kEffs kr $ "effects of computation type " ++ (show ct)
  return kt

wfElem :: Context -> Elem -> TC ()
wfElem ctx (CKVar x) = tcNot ("duplicate kvar " ++ (show x)) $ findKVar ctx x
wfElem ctx (CTVar x k) = do
  tcNot ("duplicate tvar " ++ (show x)) $ findKVar ctx x
  wfKind ctx k
wfElem ctx e@(CVar x t) = do
  tcNot ("duplicate var " ++ (show x)) $ findKVar ctx x
  k <- wfValTy ctx t
  checkKind kType k $ "cvar in context " ++ (show e)

wfContext :: Context -> TC ()
wfContext (Context ctx) = go ctx
  where
    go [] = return ()
    go (h : t) = do
      go t
      wfElem (Context t) h

-- typechecking
typecheckVal :: Context -> Val -> TC ValTy
typecheckVal ctx v = do
  wfContext ctx
  case v of
    Var (Bound _) -> err $ "bound variable in typecheckVal: " ++ (show v)
    Var (Free x) -> findVar ctx x
    Abs n t e -> do
      k <- wfValTy ctx t
      checkKind kType k $ "abstraction argument type " ++ (show v)
      let x = freshVarInContext ctx e n
      tr <- typecheckComp (add ctx $ CVar x t) $ openVar x e
      return $ TFun t tr
    AbsT n k e -> do
      wfKind ctx k
      let x = freshTVarInContext ctx e n
      tr <- typecheckComp (add ctx $ CTVar x k) $ openTVar x e
      return $ TForall n k $ closeTy x tr
    Open c -> do
      tc@(TAnnot t r) <- typecheckComp ctx c
      case r of
        TEmpty -> return $ TForall "r" kEffs $ TAnnot t (TVar (Bound 0))
        _ -> err $ "closed type in " ++ (show v) ++ ": " ++ (show tc)
  
typecheckComp :: Context -> Comp -> TC CompTy
typecheckComp ctx c = do
  wfContext ctx
  case c of
    Return v -> do
      t <- typecheckVal ctx v
      return $ TAnnot t TEmpty
    App a b -> do
      ta <- typecheckVal ctx a
      case ta of
        TFun l r -> do
          tb <- typecheckVal ctx b
          eqValTy l tb $ "application " ++ (show c)
          return r
        _ -> err $ "not a function type in application: " ++ (show ta) ++ " in " ++ (show c)
    AppT a b -> do
      ta <- typecheckVal ctx a
      case ta of
        TForall n k t -> do
          k' <- wfValTy ctx b
          checkKind k k' $ "type application " ++ (show c)
          return $ openTy b t
        _ -> err $ "not a forall type in type application: " ++ (show ta) ++ " in " ++ (show c)
    Do n a b -> do
      TAnnot t r <- typecheckComp ctx a
      let x = freshVarInContext ctx b n
      tb@(TAnnot t' r') <- typecheckComp (add ctx $ CVar x t) $ openVar x b
      eqValTy r r' $ "do expression second computation: " ++ (show c)
      return tb

infer :: Context -> Comp -> TC CompTy
infer ctx e = do
  tcBool ("expression not locally closed: " ++ (show e)) $ isLocallyClosed e
  wfContext ctx
  t <- typecheckComp ctx e
  wfCompTy ctx t
  return t

-- semantics
reduce :: Comp -> Comp
reduce c@(Return _) = c
reduce (App (Abs x _ a) b) = reduce $ open b a
reduce (AppT (AbsT x _ a) t) = reduce $ openTy t a
reduce (AppT (Open c) t) = reduce c
reduce (Do x a b) =
  case reduce a of
    Return v -> reduce $ open v b
    a' -> Do x a' b
reduce c = c

-- testing
tpure :: ValTy -> CompTy
tpure t = TAnnot t TEmpty

tfunP :: ValTy -> ValTy -> ValTy
tfunP a b = TFun a $ tpure b

tforallP :: Name -> Kind -> ValTy -> ValTy
tforallP x k t = TForall x k $ tpure t

ctx :: Context
ctx = adds initialContext
  [
    CTVar "Void" "Type",

    CTVar "Unit" "Type",
    CVar "Unit" "Unit",

    CTVar "Bool" "Type",
    CVar "True" "Bool",
    CVar "False" "Bool",

    CVar "if" $ toNamelessTy $ tforallP "t" kType $ tfunP "Bool" $ tfunP "t" $ tfunP "t" "t",

    CVar "flip" $ toNamelessTy $ tforallP "e" kEffs $ TFun "Unit" $ TAnnot "Bool" $ TExtend "Flip" "e",
    CVar "log" $ toNamelessTy $ tforallP "e" kEffs $ TFun "Bool" $ TAnnot "Unit" $ TExtend "Log" "e"
  ]

opened :: Comp -> ValTy -> Comp
opened c e = AppT (Open c) e

eid :: Val
eid = AbsT "t" kType $ Return $ Abs "x" "t" "x"

term :: Comp
term =  
  Do "o" (AppT "flip" $ TExtend "Log" TEmpty) $
  Do "b" (App "o" "Unit") $
  Do "o'" (AppT "log" $ TExtend "Flip" TEmpty) $
  App "o'" "b"

main :: IO ()
main = do
  putStrLn $ show term
  let n = toNameless term
  -- putStrLn $ show n
  case infer ctx n of
    Left m -> putStrLn m
    Right t' -> do
      -- putStrLn $ show t'
      putStrLn $ show $ toNamedTy t'
      let r = reduce n
      -- putStrLn $ show r
      putStrLn $ show $ toNamed r
