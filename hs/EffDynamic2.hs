-- TODO:
--  dynamic instances

{-# LANGUAGE OverloadedStrings #-}

import GHC.Exts (IsString(..))
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

import Debug.Trace (traceShowId, traceShow, trace)

-- Names
type Name = String

freshName :: Set Name -> Name -> Name
freshName s x = if Set.member x s then freshName s (x ++ "'") else x

-- Kinds
data Kind
  = KTy
  | KCTy
  deriving (Eq)

instance Show Kind where
  show KTy = "Type"
  show KCTy = "Comp"

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
openTVar x t = openTy (TFree x) t

substTVar :: HasTVar t => Name -> Ty -> t -> t
substTVar x u = openTy u . closeTy x

isClosedTy :: HasTVar t => t -> Bool
isClosedTy = Set.null . freeTVars

freshInTy :: HasTVar t => Name -> t -> Bool
freshInTy x t = Set.notMember x $ freeTVars t

freshTVar :: HasTVar t => t -> Name -> Name
freshTVar t x = freshName (freeTVars t) x

-- Types
data Ty
  = TBound Int
  | TFree Name
  | TFun Ty CTy
  | TForall Kind CTy
  deriving (Eq)

instance Show Ty where
  show (TBound i) = "'" ++ (show i)
  show (TFree x) = x
  show (TFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"
  show (TForall k t) = "(forall " ++ (show k) ++ ". " ++ (show t) ++ ")"

instance IsString Ty where
  fromString = TFree

instance HasTVar Ty where
  openTyR k u t@(TBound m) = if m == k then u else t
  openTyR k u t@(TFree _) = t
  openTyR k u (TFun a b) = TFun (openTyR k u a) (openTyR k u b)
  openTyR k u (TForall ki c) = TForall ki $ openTyR (k + 1) u c

  closeTyR _ _ t@(TBound _) = t
  closeTyR k x t@(TFree y) = if x == y then TBound k else t
  closeTyR k x (TFun a b) = TFun (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (TForall ki c) = TForall ki $ closeTyR (k + 1) x c

  isLocallyClosedTyR k (TBound m) = m < k
  isLocallyClosedTyR _ (TFree _) = True
  isLocallyClosedTyR k (TFun a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (TForall ki c) = isLocallyClosedTyR (k + 1) c

  freeTVars (TBound _) = Set.empty
  freeTVars (TFree x) = Set.singleton x
  freeTVars (TFun a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (TForall ki c) = freeTVars c

type Effs = Set Name

data CTy
  = CTy Ty Effs
  deriving (Eq)

instance Show CTy where
  show (CTy t r) =
    if Set.null r then
      show t
    else
      (show t) ++ "!{" ++ (intercalate ", " $ Set.elems r) ++ "}"

instance IsString CTy where
  fromString x = CTy (TFree x) Set.empty

instance HasTVar CTy where
  openTyR k u (CTy t e) = CTy (openTyR k u t) e

  closeTyR k u (CTy t e) = CTy (closeTyR k u t) e

  isLocallyClosedTyR k (CTy t e) = isLocallyClosedTyR k t

  freeTVars (CTy t e) = freeTVars t

-- HasVar
class HasVar t where
  openR :: Int -> Val -> t -> t
  closeR :: Int -> Name -> t -> t
  isLocallyClosedR :: Int -> t -> Bool
  freeVars :: t -> Set Name

open :: HasVar t => Val -> t -> t
open = openR 0

close :: HasVar t => Name -> t -> t
close = closeR 0

isLocallyClosed :: HasVar t => t -> Bool
isLocallyClosed = isLocallyClosedR 0

openVar :: HasVar t => Name -> t -> t
openVar x t = open (Free x) t

substVar :: HasVar t => Name -> Val -> t -> t
substVar x u = open u . close x

isClosed :: HasVar t => t -> Bool
isClosed = Set.null . freeVars

freshIn :: HasVar t => Name -> t -> Bool
freshIn x t = Set.notMember x $ freeVars t

freshVar :: HasVar t => t -> Name -> Name
freshVar t x = freshName (freeVars t) x

-- AST
data Val
  = Bound Int
  | Free Name
  | Abs Ty Comp
  | AbsT Kind Comp
  deriving (Eq)

instance Show Val where
  show (Bound i) = "'" ++ (show i)
  show (Free x) = x
  show (Abs t b) = "(\\" ++ (show t) ++ " -> " ++ (show b) ++ ")"
  show (AbsT k b) = "(/\\" ++ (show k) ++ " -> " ++ (show b) ++ ")"

instance IsString Val where
  fromString = Free

instance HasVar Val where
  openR k u t@(Bound m) = if m == k then u else t
  openR k u t@(Free _) = t
  openR k u (Abs t c) = Abs t $ openR (k + 1) u c
  openR k u (AbsT ki c) = AbsT ki $ openR k u c

  closeR _ _ t@(Bound _) = t
  closeR k x t@(Free y) = if x == y then Bound k else t
  closeR k x (Abs t c) = Abs t $ closeR (k + 1) x c
  closeR k x (AbsT ki c) = AbsT ki $ closeR k x c

  isLocallyClosedR k (Bound m) = m < k
  isLocallyClosedR _ (Free _) = True
  isLocallyClosedR k (Abs t c) = isLocallyClosedR (k + 1) c
  isLocallyClosedR k (AbsT ki c) = isLocallyClosedR k c

  freeVars (Bound _) = Set.empty
  freeVars (Free x) = Set.singleton x
  freeVars (Abs t c) = freeVars c
  freeVars (AbsT ki c) = freeVars c

instance HasTVar Val where
  openTyR k u t@(Bound _) = t
  openTyR k u t@(Free _) = t
  openTyR k u (Abs t c) = Abs (openTyR k u t) (openTyR k u c)
  openTyR k u (AbsT ki c) = AbsT ki $ openTyR (k + 1) u c

  closeTyR k x t@(Bound _) = t
  closeTyR k x t@(Free _) = t
  closeTyR k x (Abs t c) = Abs (closeTyR k x t) (closeTyR k x c)
  closeTyR k x (AbsT ki c) = AbsT ki $ closeTyR (k + 1) x c

  isLocallyClosedTyR k (Bound _) = True
  isLocallyClosedTyR k (Free _) = True
  isLocallyClosedTyR k (Abs t c) = isLocallyClosedTyR k t && isLocallyClosedTyR k c
  isLocallyClosedTyR k (AbsT ki c) = isLocallyClosedTyR (k + 1) c

  freeTVars (Bound _) = Set.empty
  freeTVars (Free _) = Set.empty
  freeTVars (Abs t c) = Set.union (freeTVars t) (freeTVars c)
  freeTVars (AbsT ki c) = freeTVars c

data Comp
  = Return Val
  | App Val Val
  | AppT Val Ty
  | Do Comp Comp
  | Op Name Val
  | Handle Comp Comp (Map Name Comp)
  deriving (Eq)

instance Show Comp where
  show (Return v) = "return " ++ (show v)
  show (App a b) = (show a) ++ " " ++ (show b)
  show (AppT a b) = (show a) ++ " [" ++ (show b) ++ "]"
  show (Do a b) = (show a) ++ "; " ++ (show b)
  show (Op x v) = x ++ "(" ++ (show v) ++ ")"
  show (Handle c cr m) = "handle (" ++ (show c) ++ ") { return -> " ++ (show cr) ++ ", " ++
    (intercalate ", " $ map (\(op, c) -> op ++ " -> " ++ (show c)) $ Map.assocs m) ++ " }"

instance IsString Comp where
  fromString = Return . Free

instance HasVar Comp where
  openR k u (Return v) = Return $ openR k u v
  openR k u (App a b) = App (openR k u a) (openR k u b)
  openR k u (AppT a b) = AppT (openR k u a) b
  openR k u (Do a b) = Do (openR k u a) (openR (k + 1) u b)
  openR k u (Op x b) = Op x (openR k u b)
  openR k u (Handle c cr m) = Handle (openR k u c) (openR (k + 1) u cr) $ Map.map (openR (k + 2) u) m

  closeR k x (Return v) = Return $ closeR k x v
  closeR k x (App a b) = App (closeR k x a) (closeR k x b)
  closeR k x (AppT a b) = AppT (closeR k x a) b
  closeR k x (Do a b) = Do (closeR k x a) (closeR (k + 1) x b)
  closeR k x (Op o b) = Op o (closeR k x b)
  closeR k x (Handle c cr m) = Handle (closeR k x c) (closeR (k + 1) x cr) $ Map.map (closeR (k + 2) x) m

  isLocallyClosedR k (Return v) = isLocallyClosedR k v
  isLocallyClosedR k (App a b) = isLocallyClosedR k a && isLocallyClosedR k b
  isLocallyClosedR k (AppT a b) = isLocallyClosedR k a
  isLocallyClosedR k (Do a b) = isLocallyClosedR k a && isLocallyClosedR (k + 1) b
  isLocallyClosedR k (Op x b) = isLocallyClosedR k b
  isLocallyClosedR k (Handle c cr m) = isLocallyClosedR k c && isLocallyClosedR (k + 1) cr &&
    (all (isLocallyClosedR (k + 2)) $ Map.elems m)

  freeVars (Return v) = freeVars v
  freeVars (App a b) = Set.union (freeVars a) (freeVars b)
  freeVars (AppT a b) = freeVars a
  freeVars (Do a b) = Set.union (freeVars a) (freeVars b)
  freeVars (Op x b) = freeVars b
  freeVars (Handle c cr m) = Set.union (freeVars c) $
    Set.union (freeVars cr) $ foldr Set.union Set.empty $ map freeVars $ Map.elems m

instance HasTVar Comp where
  openTyR k u (Return v) = Return $ openTyR k u v
  openTyR k u (App a b) = App (openTyR k u a) (openTyR k u b)
  openTyR k u (AppT a b) = AppT (openTyR k u a) (openTyR k u b)
  openTyR k u (Do a b) = Do (openTyR k u a) (openTyR k u b)
  openTyR k u (Op x b) = Op x (openTyR k u b)
  openTyR k u (Handle c cr m) = Handle (openTyR k u c) (openTyR k u cr) $ Map.map (openTyR k u) m

  closeTyR k x (Return v) = Return $ closeTyR k x v
  closeTyR k x (App a b) = App (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (AppT a b) = AppT (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (Do a b) = Do (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (Op o b) = Op o (closeTyR k x b)
  closeTyR k x (Handle c cr m) = Handle (closeTyR k x c) (closeTyR k x cr) $ Map.map (closeTyR k x) m

  isLocallyClosedTyR k (Return v) = isLocallyClosedTyR k v
  isLocallyClosedTyR k (App a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (AppT a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Do a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Op x b) = isLocallyClosedTyR k b
  isLocallyClosedTyR k (Handle c cr m) = isLocallyClosedTyR k c && isLocallyClosedTyR k cr &&
    (all (isLocallyClosedTyR k) $ Map.elems m)

  freeTVars (Return v) = freeTVars v
  freeTVars (App a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (AppT a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Do a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Op x b) = freeTVars b
  freeTVars (Handle c cr m) = Set.union (freeTVars c) $
    Set.union (freeTVars cr) $ foldr Set.union Set.empty $ map freeTVars $ Map.elems m

-- TC
type TC t = Either String t

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

-- Context
data Elem
  = CEff Name
  | COp Name Name Ty Ty
  | CVar Name Ty
  | CTVar Name Kind
  deriving (Eq)

instance Show Elem where
  show (CEff e) = "effect " ++ e
  show (COp o e a b) = "op " ++ o ++ " of " ++ e ++ " : " ++ (show a) ++ " -> " ++ (show b)
  show (CVar x t) = x ++ " : " ++ (show t)
  show (CTVar x k) = x ++ " :k " ++ (show k)

type Context = [Elem]

context :: [Elem] -> Context
context = reverse

findEff :: Context -> Name -> TC ()
findEff [] x = Left $ "effect " ++ x ++ " not found"
findEff (CEff y : _) x | x == y = return ()
findEff (_ : r) x = findEff r x

findOp :: Context -> Name -> TC (Name, Ty, Ty)
findOp [] x = Left $ "op " ++ x ++ " not found"
findOp (COp y e a b : _) x | x == y = return (e, a, b)
findOp (_ : r) x = findOp r x

type Ops = Map Name (Ty, Ty)

findOps :: Context -> Name -> Ops
findOps [] e = Map.empty
findOps (COp o e' a b : r) e | e == e' = Map.insert o (a, b) $ findOps r e
findOps (_ : r) e = findOps r e

findOpNames :: Context -> Name -> Set Name
findOpNames ctx e = Map.keysSet $ findOps ctx e

findVar :: Context -> Name -> TC Ty
findVar [] x = Left $ "var " ++ x ++ " not found"
findVar (CVar y t : _) x | x == y = return t
findVar (_ : r) x = findVar r x

findTVar :: Context -> Name -> TC Kind
findTVar [] x = Left $ "tvar " ++ x ++ " not found"
findTVar (CTVar y k : _) x | x == y = return k
findTVar (_ : r) x = findTVar r x

vars :: Context -> Set Name
vars ctx = Set.fromList $
  Maybe.mapMaybe (\e -> case e of { CVar x _ -> Just x; _ -> Nothing }) ctx

tvars :: Context -> Set Name
tvars ctx = Set.fromList $
  Maybe.mapMaybe (\e -> case e of { CTVar x _ -> Just x; _ -> Nothing }) ctx

freshTVarInContext :: HasTVar t => Context -> t -> Name -> Name
freshTVarInContext ctx t x = freshName (Set.union (freeTVars t) (tvars ctx)) x

freshVarInContext :: HasVar t => Context -> t -> Name -> Name
freshVarInContext ctx t x = freshName (Set.union (freeVars t) (vars ctx)) x

-- Wellformedness
checkKind :: String -> Kind -> Kind -> TC ()
checkKind msg k k' | k == k' = return ()
checkKind msg k k' = Left $ "expected " ++ (show k) ++ " but got " ++ (show k') ++ ": " ++ msg

wfTy :: Context -> Ty -> TC Kind
wfTy ctx t =
  case t of
    TBound k -> Left $ "bound type variable found in wfTy"
    TFree x -> findTVar ctx x
    TFun a b -> do
      k <- wfTy ctx a
      checkKind "wfTy1" KTy k
      k' <- wfCTy ctx b
      checkKind "wfTy2" KCTy k'
      return KTy
    TForall k b -> do
      let x = freshTVarInContext ctx b "t"
      wfCTy (CTVar x k : ctx) $ openTVar x b

wfCTy :: Context -> CTy -> TC Kind
wfCTy ctx ct =
  case ct of
    CTy t r -> do
      mapM_ (findEff ctx) $ Set.elems r
      k <- wfTy ctx t
      checkKind "wfCTy" KTy k
      return KCTy

wfElem :: Context -> Elem -> TC ()
wfElem ctx (CEff e) = do
  tcNot ("duplicate eff " ++ e) $ findEff ctx e
wfElem ctx (COp o e a b) = do
  findEff ctx e
  tcNot ("duplicate op " ++ o) $ findOp ctx o
  k <- wfTy ctx a
  checkKind "wfElem1" KTy k
  k' <- wfTy ctx b
  checkKind "wfElem2" KTy k'
wfElem ctx (CVar x t) = do
  tcNot ("duplicate var " ++ x) $ findVar ctx x
  tcDrop $ wfTy ctx t
wfElem ctx (CTVar x k) = do
  tcNot ("duplicate tvar " ++ x) $ findTVar ctx x

wfContext :: Context -> TC ()
wfContext [] = return ()
wfContext (e : r) = do
  wfContext r
  wfElem r e

-- Subtyping
subTy :: Ty -> Ty -> TC ()
subTy t@(TBound a) t'@(TBound b) = tcBool ("subTy failed " ++ (show t) ++ " <: " ++ (show t')) $ a == b
subTy t@(TFree a) t'@(TFree b) = tcBool ("subTy failed " ++ (show t) ++ " <: " ++ (show t')) $ a == b
subTy (TFun x y) (TFun x' y') = do
  subTy x' x
  subCTy y y'
subTy (TForall ki a) (TForall ki' b) = do
  checkKind "subTy" ki ki'
  subCTy a b

subCTy :: CTy -> CTy -> TC ()
subCTy a@(CTy t r) b@(CTy t' r') = do
  subTy t t'
  tcBool ("effect sets are not a subset " ++ (show a) ++ " <: " ++ (show b)) $ Set.isSubsetOf r r'

-- Typechecking
typecheckVal :: Context -> Val -> TC Ty
typecheckVal ctx v = do
  wfContext ctx
  case v of
    Bound i -> Left $ "unable to typecheck bound variable " ++ (show i)
    Free x -> findVar ctx x
    Abs t c -> do
      wfTy ctx t
      let x = freshVarInContext ctx c "x"
      t' <- typecheckComp (CVar x t : ctx) (openVar x c)
      return $ TFun t t'
    AbsT k c -> do
      let x = freshTVarInContext ctx c "t"
      t' <- typecheckComp (CTVar x k : ctx) (openTVar x c)
      return $ TForall k $ closeTy x t'

typecheckHandleCase :: Context -> Ty -> Effs -> (Name, Comp) -> TC (Name, Name, Effs)
typecheckHandleCase ctx t r (o, c) = do
  (e, a, b) <- findOp ctx o
  let x = freshVarInContext ctx c "x"
  let k = freshVarInContext ctx c "k"
  CTy t' r' <- typecheckComp (CVar x a : CVar k (TFun b $ CTy t r) : ctx) (openVar x $ openVar k c)
  subTy t' t
  return (e, o, r')

typecheckHandler :: Context -> Map Name Comp -> Ty -> Effs -> TC (Set Name, Set Name, Set Name)
typecheckHandler ctx m t r = do
  rs <- mapM (typecheckHandleCase ctx t r) $ Map.assocs m
  return $ foldr (\(a, b, e) (a', b', e') -> (Set.insert a a', Set.insert b b', Set.union e e')) (Set.empty, Set.empty, Set.empty) rs

typecheckComp :: Context -> Comp -> TC CTy
typecheckComp ctx c = do
  wfContext ctx
  case c of
    Return v -> do
      t <- typecheckVal ctx v
      return $ CTy t Set.empty
    e@(App a b) -> do
      ft <- typecheckVal ctx a
      case ft of
        TFun ta tb -> do
          at <- typecheckVal ctx b
          subTy at ta
          return tb
        _ -> Left $ "not a function in application " ++ (show ft) ++ " in " ++ (show e)
    e@(AppT a b) -> do
      ft <- typecheckVal ctx a
      case ft of
        TForall k t -> do
          k' <- wfTy ctx b
          checkKind "tycheckComp1" k k'
          return $ openTy b t
        _ -> Left $ "not a forall in type application " ++ (show ft) ++ " in " ++ (show e)
    Do a b -> do
      CTy t r <- typecheckComp ctx a
      let x = freshVarInContext ctx b "x"
      CTy t' r' <- typecheckComp (CVar x t : ctx) (openVar x b)
      return $ CTy t' (Set.union r r')
    Op o v -> do
      (e, a, b) <- findOp ctx o
      t <- typecheckVal ctx v
      subTy t a
      return $ CTy b $ Set.singleton e
    Handle c cr m -> do
      CTy t r <- typecheckComp ctx c
      let x = freshVarInContext ctx cr "x"
      CTy t' r' <- typecheckComp (CVar x t : ctx) (openVar x cr)
      (es, os, rs) <- typecheckHandler ctx m t' r'
      let handledEs = Set.fromList $ Maybe.mapMaybe (\e -> if Set.isSubsetOf (findOpNames ctx e) os then Just e else Nothing) $ Set.elems es
      return $ CTy t' $ Set.union (Set.difference r handledEs) rs

inferVal :: Context -> Val -> TC Ty
inferVal ctx v = do
  wfContext ctx
  t <- typecheckVal ctx v
  k <- wfTy ctx t
  checkKind "inferVal" KTy k
  return t

inferComp :: Context -> Comp -> TC CTy
inferComp ctx c = do
  wfContext ctx
  t <- typecheckComp ctx c
  k <- wfCTy ctx t
  checkKind "inferComp" KCTy k
  return t

-- Reduce
reduceComp :: Comp -> Comp
reduceComp t@(Return _) = t
reduceComp (App (Abs t a) b) = reduceComp $ open b a
reduceComp (AppT (AbsT k a) t) = reduceComp $ openTy t a
reduceComp (Do a b) =
  case reduceComp a of
    Return v -> reduceComp $ open v b
    a' -> Do a' b
reduceComp (Handle c cr m) =
  case reduceComp c of
    Return v -> reduceComp $ open v cr
    op@(Op o v) -> Maybe.maybe op (\c -> reduceComp $ open (Abs "_" $ Return (Bound 0)) $ open v c) $ Map.lookup o m
    Do (Op o v) b ->
      case Map.lookup o m of
        Just c ->
          reduceComp $ open (Abs "_" (Handle b cr m)) $ open v c
        Nothing ->
          Do (Op o v) (Handle b cr m)
    c' -> c'
reduceComp c = c

-- User AST
data TyExpr
  = TEVar Name
  | TEFun TyExpr TyExpr
  | TEForall Name Kind TyExpr
  | TEComp TyExpr Effs
  deriving (Eq)

instance Show TyExpr where
  show (TEVar x) = x
  show (TEFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"
  show (TEForall x k b) = "(forall(" ++ x ++ ":" ++ (show k) ++ "). " ++ (show b) ++ ")"
  show (TEComp t r) = (show t) ++ "!{" ++ (intercalate ", " $ Set.elems r) ++ "}"

instance IsString TyExpr where
  fromString = TEVar

toNamelessTyR :: Int -> Map Name Int -> TyExpr -> Either String Ty
toNamelessTyR k m (TEVar x) =
  return $ Maybe.maybe (TFree x) (\i -> TBound $ k - i - 1) $ Map.lookup x m
toNamelessTyR k m (TEFun a b) = do
  a' <- toNamelessTyR k m a
  b' <- toNamelessCTyR k m b
  return $ TFun a' b'
toNamelessTyR k m (TEForall x ki t) = do
  t' <- toNamelessCTyR (k + 1) (Map.insert x k m) t
  return $ TForall ki t'
toNamelessTyR k m t@(TEComp _ _) =
  Left $ "computation type in value type position: " ++ (show t)

toNamelessCTyR :: Int -> Map Name Int -> TyExpr -> Either String CTy
toNamelessCTyR k m t@(TEVar _) = do
  t' <- toNamelessTyR k m t
  return $ CTy t' Set.empty
toNamelessCTyR k m t@(TEFun _ _) = do
  t' <- toNamelessTyR k m t
  return $ CTy t' Set.empty
toNamelessCTyR k m t@(TEForall _ _ _) = do
  t' <- toNamelessTyR k m t
  return $ CTy t' Set.empty
toNamelessCTyR k m (TEComp t r) = do
  t' <- toNamelessTyR k m t
  return $ CTy t' r

toNamelessCTy :: TyExpr -> Either String CTy
toNamelessCTy = toNamelessCTyR 0 Map.empty

toNamelessTy :: TyExpr -> Either String Ty
toNamelessTy = toNamelessTyR 0 Map.empty

data EHandlerCase
  = ERet Name Expr EHandlerCase
  | ECase Name Name Name Expr EHandlerCase
  | End
  deriving (Eq)

data Expr
  = EVar Name
  | EAbs Name TyExpr Expr
  | EAbsT Name Kind Expr
  | EApp Expr Expr
  | EAppT Expr TyExpr
  | EDo Name Expr Expr
  | EOp Name Expr
  | EHandle Expr EHandlerCase
  deriving (Eq)

instance Show EHandlerCase where
  show (ERet x e r) = "return " ++ x ++ " -> " ++ (show e) ++ ", " ++ (show r)
  show (ECase o x k e r) = o ++ " " ++ x ++ " " ++ k ++ " -> " ++ (show e) ++ ", " ++ (show r)
  show End = ""

instance Show Expr where
  show (EVar x) = x
  show (EAbs x t e) = "(\\(" ++ x ++ ":" ++ (show t) ++ ") -> " ++ (show e) ++ ")"
  show (EAbsT x k e) = "(/\\(" ++ x ++ ":" ++ (show k) ++ ") -> " ++ (show e) ++ ")"
  show (EApp a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (EAppT a b) = "(" ++ (show a) ++ " [" ++ (show b) ++ "])"
  show (EDo x a b) = "(" ++ x ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"
  show (EOp op v) = op ++ "(" ++ (show v) ++ ")"
  show (EHandle e h) = "handle (" ++ (show e) ++ ") { " ++ (show h) ++ "}"

instance IsString Expr where
  fromString = EVar

freeVarsInExpr :: Expr -> Set Name
freeVarsInExpr (EVar x) = Set.singleton x
freeVarsInExpr (EAbs x t b) = Set.delete x $ freeVarsInExpr b 
freeVarsInExpr (EAbsT x k b) = freeVarsInExpr b
freeVarsInExpr (EApp a b) = Set.union (freeVarsInExpr a) (freeVarsInExpr b)
freeVarsInExpr (EAppT a b) = freeVarsInExpr a
freeVarsInExpr (EDo x a b) = Set.union (freeVarsInExpr a) (Set.delete x $ freeVarsInExpr b)
freeVarsInExpr (EOp op v) = freeVarsInExpr v
freeVarsInExpr (EHandle e h) = Set.union (freeVarsInExpr e) (freeVarsInHandler h)
  where
    freeVarsInHandler (ERet x e r) = Set.union (Set.delete x $ freeVarsInExpr e) (freeVarsInHandler r)
    freeVarsInHandler (ECase o x k e r) = Set.union (Set.delete x $ Set.delete k $ freeVarsInExpr e) (freeVarsInHandler r)
    freeVarsInHandler End = Set.empty

exprIsVal :: Expr -> Bool
exprIsVal (EVar _) = True
exprIsVal (EAbs _ _ _) = True
exprIsVal (EAbsT _ _ _) = True
exprIsVal (EApp _ _) = False
exprIsVal (EAppT _ _) = False
exprIsVal (EDo _ _ _) = False
exprIsVal (EOp _ _) = False
exprIsVal (EHandle _ _) = False

exprIsComp :: Expr -> Bool
exprIsComp = not . exprIsVal

toNamelessValR :: (Int, Map Name Int) -> (Int, Map Name Int) -> Expr -> Either String Val
toNamelessValR (kt, mt) (ke, me) (EVar x) =
  return $ Maybe.maybe (Free x) (\i -> Bound $ ke - i - 1) $ Map.lookup x me
toNamelessValR (kt, mt) (ke, me) (EAbs x t b) = do
  t' <- toNamelessTyR kt mt t
  b' <- toNamelessCompR (kt, mt) (ke + 1, Map.insert x ke me) b
  return $ Abs t' b'
toNamelessValR (kt, mt) (ke, me) (EAbsT x k b) = do
  b' <- toNamelessCompR (kt + 1, Map.insert x kt mt) (ke, me) b
  return $ AbsT k b'
toNamelessValR (kt, mt) (ke, me) e = Left $ "computation in value position: " ++ (show e)

toNamelessHandlerR :: (Int, Map Name Int) -> (Int, Map Name Int) -> EHandlerCase -> Either String (Comp, Map Name Comp)
toNamelessHandlerR (kt, mt) (ke, me) (ERet x e r) = do
  e' <- toNamelessCompR (kt, mt) (ke + 1, Map.insert x ke me) e
  (cr, m) <- toNamelessHandlerR (kt, mt) (ke, me) r
  return (e', m)
toNamelessHandlerR (kt, mt) (ke, me) (ECase o x k e r) = do
  e' <- toNamelessCompR (kt, mt) (ke + 2, Map.insert k (ke + 1) $ Map.insert x ke me) e
  (cr, m) <- toNamelessHandlerR (kt, mt) (ke, me) r
  return (cr, Map.insert o e' m)
toNamelessHandlerR (kt, mt) (ke, me) End = return (Return (Bound 0), Map.empty)

toNamelessCompR :: (Int, Map Name Int) -> (Int, Map Name Int) -> Expr -> Either String Comp
toNamelessCompR (kt, mt) (ke, me) e@(EApp a b) =
  if exprIsComp a then
    if exprIsComp b then
      let x = freshName (freeVarsInExpr b) "x" in
      let y = freshName (freeVarsInExpr b) "y" in
      toNamelessCompR (kt, mt) (ke, me) $ EDo x a $ EDo y b $ EApp (EVar x) (EVar y)
    else
      let x = freshName (freeVarsInExpr b) "x" in
      toNamelessCompR (kt, mt) (ke, me) $ EDo x a $ EApp (EVar x) b
  else if exprIsComp b then
    let x = freshName (freeVarsInExpr a) "x" in
    toNamelessCompR (kt, mt) (ke, me) $ EDo x b $ EApp a (EVar x)
  else do
    a' <- toNamelessValR (kt, mt) (ke, me) a
    b' <- toNamelessValR (kt, mt) (ke, me) b
    return $ App a' b'
toNamelessCompR (kt, mt) (ke, me) e@(EAppT a b) =
  if exprIsComp a then
    toNamelessCompR (kt, mt) (ke, me) $ EDo "x" a $ EAppT "x" b
  else do
    a' <- toNamelessValR (kt, mt) (ke, me) a
    b' <- toNamelessTyR kt mt b
    return $ AppT a' b'
toNamelessCompR (kt, mt) (ke, me) e@(EDo x a b) = do
  a' <- toNamelessCompR (kt, mt) (ke, me) a
  b' <- toNamelessCompR (kt, mt) (ke + 1, Map.insert x ke me) b
  return $ Do a' b'
toNamelessCompR (kt, mt) (ke, me) e@(EOp op v) =
  if exprIsComp v then
    toNamelessCompR (kt, mt) (ke, me) $ EDo "x" v $ EOp op "x"
  else do
    v' <- toNamelessValR (kt, mt) (ke, me) v
    return $ Op op v'
toNamelessCompR (kt, mt) (ke, me) (EHandle c h) = do
  c' <- toNamelessCompR (kt, mt) (ke, me) c
  (cr, m) <- toNamelessHandlerR (kt, mt) (ke, me) h
  return $ Handle c' cr m
toNamelessCompR (kt, mt) (ke, me) t = do
  t' <- toNamelessValR (kt, mt) (ke, me) t
  return $ Return t'

toNamelessVal :: Expr -> Either String Val
toNamelessVal = toNamelessValR (0, Map.empty) (0, Map.empty)

toNamelessComp :: Expr -> Either String Comp
toNamelessComp = toNamelessCompR (0, Map.empty) (0, Map.empty)

-- Testing
showEither :: Show t => Either String t -> String
showEither (Right x) = show x
showEither (Left m) = m

ctx :: Context
ctx = context
  [
    CTVar "Unit" KTy,
    CVar "Unit" "Unit",

    CTVar "Bool" KTy,
    CVar "True" "Bool",
    CVar "False" "Bool",

    CEff "Fail",
    COp "fail" "Fail" "Unit" "Unit",

    CEff "State",
    COp "get" "State" "Unit" "Bool",
    COp "put" "State" "Bool" "Unit"
  ]

failH :: Expr -> Expr
failH c = EHandle c $ ECase "fail" "x" "k" "Unit" End

term :: Expr
term = failH $ EOp "fail" "Unit"

main :: IO ()
main = do
  putStrLn $ show term
  let t = toNamelessComp term
  putStrLn $ showEither t
  case t of
    Right c -> do
      putStrLn $ showEither $ inferComp ctx c
      putStrLn $ show $ reduceComp c
    Left _ -> return ()
