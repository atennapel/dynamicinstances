{-
TODO:
bug with duplicate type variables
Polymorphic effects
Polymorphic operations
-}

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

-- Names
type Name = String

freshName :: Set Name -> Name -> Name
freshName s x = if Set.member x s then freshName s (x ++ "'") else x

-- Kinds
data Kind
  = KTy
  | KCTy
  | KInst Name
  deriving (Eq, Ord)

instance Show Kind where
  show KTy = "Type"
  show KCTy = "Comp"
  show (KInst e) = "(Inst " ++ e ++ ")"

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
  deriving (Eq, Ord)

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

type Effs = Set Ty

data CTy
  = CTy Ty Effs
  | CExists Kind CTy
  deriving (Eq, Ord)

instance Show CTy where
  show (CTy t r) =
    if Set.null r then
      show t
    else
      (show t) ++ "!{" ++ (intercalate ", " $ map show $ Set.elems r) ++ "}"
  show (CExists k t) = "exists " ++ (show k) ++ ". " ++ (show t)

instance IsString CTy where
  fromString x = CTy (TFree x) Set.empty

instance HasTVar CTy where
  openTyR k u (CTy t e) = CTy (openTyR k u t) (Set.map (openTyR k u) e)
  openTyR k u (CExists ki t) = CExists ki $ openTyR (k + 1) u t

  closeTyR k u (CTy t e) = CTy (closeTyR k u t) (Set.map (closeTyR k u) e)
  closeTyR k u (CExists ki t) = CExists ki $ closeTyR (k + 1) u t

  isLocallyClosedTyR k (CTy t e) = isLocallyClosedTyR k t && (all (isLocallyClosedTyR k) $ Set.elems e)
  isLocallyClosedTyR k (CExists ki t) = isLocallyClosedTyR (k + 1) t

  freeTVars (CTy t e) = Set.union (freeTVars t) (foldr Set.union Set.empty $ map freeTVars $ Set.elems e)
  freeTVars (CExists k t) = freeTVars t

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
  | Inst Int
  deriving (Eq)

instance Show Val where
  show (Bound i) = "'" ++ (show i)
  show (Free x) = x
  show (Abs t b) = "(\\" ++ (show t) ++ " -> " ++ (show b) ++ ")"
  show (AbsT k b) = "(/\\" ++ (show k) ++ " -> " ++ (show b) ++ ")"
  show (Inst i) = "@" ++ (show i)

instance IsString Val where
  fromString = Free

instance HasVar Val where
  openR k u t@(Bound m) = if m == k then u else t
  openR k u t@(Free _) = t
  openR k u (Abs t c) = Abs t $ openR (k + 1) u c
  openR k u (AbsT ki c) = AbsT ki $ openR k u c
  openR k u t@(Inst _) = t

  closeR _ _ t@(Bound _) = t
  closeR k x t@(Free y) = if x == y then Bound k else t
  closeR k x (Abs t c) = Abs t $ closeR (k + 1) x c
  closeR k x (AbsT ki c) = AbsT ki $ closeR k x c
  closeR k x t@(Inst _) = t

  isLocallyClosedR k (Bound m) = m < k
  isLocallyClosedR k (Free _) = True
  isLocallyClosedR k (Abs t c) = isLocallyClosedR (k + 1) c
  isLocallyClosedR k (AbsT ki c) = isLocallyClosedR k c
  isLocallyClosedR k (Inst _) = True

  freeVars (Bound _) = Set.empty
  freeVars (Free x) = Set.singleton x
  freeVars (Abs t c) = freeVars c
  freeVars (AbsT ki c) = freeVars c
  freeVars (Inst _) = Set.empty

instance HasTVar Val where
  openTyR k u t@(Bound _) = t
  openTyR k u t@(Free _) = t
  openTyR k u (Abs t c) = Abs (openTyR k u t) (openTyR k u c)
  openTyR k u (AbsT ki c) = AbsT ki $ openTyR (k + 1) u c
  openTyR k u t@(Inst _) = t

  closeTyR k x t@(Bound _) = t
  closeTyR k x t@(Free _) = t
  closeTyR k x (Abs t c) = Abs (closeTyR k x t) (closeTyR k x c)
  closeTyR k x (AbsT ki c) = AbsT ki $ closeTyR (k + 1) x c
  closeTyR k x t@(Inst _) = t

  isLocallyClosedTyR k (Bound _) = True
  isLocallyClosedTyR k (Free _) = True
  isLocallyClosedTyR k (Abs t c) = isLocallyClosedTyR k t && isLocallyClosedTyR k c
  isLocallyClosedTyR k (AbsT ki c) = isLocallyClosedTyR (k + 1) c
  isLocallyClosedTyR k (Inst _) = True

  freeTVars (Bound _) = Set.empty
  freeTVars (Free _) = Set.empty
  freeTVars (Abs t c) = Set.union (freeTVars t) (freeTVars c)
  freeTVars (AbsT ki c) = freeTVars c
  freeTVars (Inst _) = Set.empty

data Comp
  = Return Val
  | App Val Val
  | AppT Val Ty
  | Do Comp Comp
  | Op Val Name Val
  | Handle Comp Comp [(Val, Name, Comp)]
  | Unpack Comp Comp
  | New Name
  deriving (Eq)

instance Show Comp where
  show (Return v) = "return " ++ (show v)
  show (App a b) = (show a) ++ " " ++ (show b)
  show (AppT a b) = (show a) ++ " [" ++ (show b) ++ "]"
  show (Do a b) = (show a) ++ "; " ++ (show b)
  show (Op i x v) = (show i) ++ "#" ++ x ++ "(" ++ (show v) ++ ")"
  show (Handle c cr m) = "handle (" ++ (show c) ++ ") { return -> " ++ (show cr) ++ ", " ++
    (intercalate ", " $ map (\(i, o, c) -> (show i) ++ "#" ++ o ++ " -> " ++ (show c)) m) ++ " }"
  show (Unpack a b) = "unpack " ++ (show a) ++ "; " ++ (show b)
  show (New e) = "new " ++ e

instance IsString Comp where
  fromString = Return . Free

instance HasVar Comp where
  openR k u (Return v) = Return $ openR k u v
  openR k u (App a b) = App (openR k u a) (openR k u b)
  openR k u (AppT a b) = AppT (openR k u a) b
  openR k u (Do a b) = Do (openR k u a) (openR (k + 1) u b)
  openR k u (Op i x b) = Op (openR k u i) x (openR k u b)
  openR k u (Handle c cr m) = Handle (openR k u c) (openR (k + 1) u cr) $ map (\(i, o, c) -> (openR k u i, o, openR (k + 2) u c)) m
  openR k u (Unpack a b) = Unpack (openR k u a) (openR (k + 1) u b)
  openR k u c@(New _) = c

  closeR k x (Return v) = Return $ closeR k x v
  closeR k x (App a b) = App (closeR k x a) (closeR k x b)
  closeR k x (AppT a b) = AppT (closeR k x a) b
  closeR k x (Do a b) = Do (closeR k x a) (closeR (k + 1) x b)
  closeR k x (Op i o b) = Op (closeR k x i) o (closeR k x b)
  closeR k x (Handle c cr m) = Handle (closeR k x c) (closeR (k + 1) x cr) $ map (\(i, o, c) -> (closeR k x i, o, closeR (k + 2) x c)) m
  closeR k x (Unpack a b) = Unpack (closeR k x a) (closeR (k + 1) x b)
  closeR k x c@(New _) = c

  isLocallyClosedR k (Return v) = isLocallyClosedR k v
  isLocallyClosedR k (App a b) = isLocallyClosedR k a && isLocallyClosedR k b
  isLocallyClosedR k (AppT a b) = isLocallyClosedR k a
  isLocallyClosedR k (Do a b) = isLocallyClosedR k a && isLocallyClosedR (k + 1) b
  isLocallyClosedR k (Op i x b) = isLocallyClosedR k i && isLocallyClosedR k b
  isLocallyClosedR k (Handle c cr m) = isLocallyClosedR k c && isLocallyClosedR (k + 1) cr &&
    (all (\(i, o, c) -> isLocallyClosedR k i && isLocallyClosedR (k + 2) c) m)
  isLocallyClosedR k (Unpack a b) = isLocallyClosedR k a && isLocallyClosedR (k + 1) b
  isLocallyClosedR k (New e) = True

  freeVars (Return v) = freeVars v
  freeVars (App a b) = Set.union (freeVars a) (freeVars b)
  freeVars (AppT a b) = freeVars a
  freeVars (Do a b) = Set.union (freeVars a) (freeVars b)
  freeVars (Op i x b) = Set.union (freeVars i) (freeVars b)
  freeVars (Handle c cr m) = Set.union (freeVars c) $
    Set.union (freeVars cr) $ foldr Set.union Set.empty $ map (\(i, o, c) -> Set.union (freeVars i) (freeVars c)) m
  freeVars (Unpack a b) = Set.union (freeVars a) (freeVars b)
  freeVars (New e) = Set.empty

instance HasTVar Comp where
  openTyR k u (Return v) = Return $ openTyR k u v
  openTyR k u (App a b) = App (openTyR k u a) (openTyR k u b)
  openTyR k u (AppT a b) = AppT (openTyR k u a) (openTyR k u b)
  openTyR k u (Do a b) = Do (openTyR k u a) (openTyR k u b)
  openTyR k u (Op i x b) = Op (openTyR k u i) x (openTyR k u b)
  openTyR k u (Handle c cr m) = Handle (openTyR k u c) (openTyR k u cr) $ map (\(i, o, c) -> (openTyR k u i, o, openTyR k u c)) m
  openTyR k u (Unpack a b) = Unpack (openTyR k u a) (openTyR (k + 1) u b)
  openTyR k u c@(New _) = c

  closeTyR k x (Return v) = Return $ closeTyR k x v
  closeTyR k x (App a b) = App (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (AppT a b) = AppT (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (Do a b) = Do (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (Op i o b) = Op (closeTyR k x i) o (closeTyR k x b)
  closeTyR k x (Handle c cr m) = Handle (closeTyR k x c) (closeTyR k x cr) $ map (\(i, o, c) -> (closeTyR k x i, o, closeTyR k x c)) m
  closeTyR k x (Unpack a b) = Unpack (closeTyR k x a) (closeTyR (k + 1) x b)
  closeTyR k x c@(New _) = c

  isLocallyClosedTyR k (Return v) = isLocallyClosedTyR k v
  isLocallyClosedTyR k (App a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (AppT a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Do a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Op i x b) = isLocallyClosedTyR k i && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Handle c cr m) = isLocallyClosedTyR k c && isLocallyClosedTyR k cr &&
    (all (\(i, o, c) -> isLocallyClosedTyR k i && isLocallyClosedTyR k c) m)
  isLocallyClosedTyR k (Unpack a b) = isLocallyClosedTyR k a && isLocallyClosedTyR (k + 1) b
  isLocallyClosedTyR k (New e) = True

  freeTVars (Return v) = freeTVars v
  freeTVars (App a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (AppT a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Do a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Op i x b) = Set.union (freeTVars i) (freeTVars b)
  freeTVars (Handle c cr m) = Set.union (freeTVars c) $
    Set.union (freeTVars cr) $ foldr Set.union Set.empty $ map (\(i, o, c) -> Set.union (freeTVars i) (freeTVars c)) m
  freeTVars (Unpack a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (New e) = Set.empty

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

checkKindInst :: Kind -> TC Name
checkKindInst (KInst x) = return x
checkKindInst k = Left $ "instance kind expected but got: " ++ (show k)

wfTy :: Context -> Ty -> TC Kind
wfTy ctx t =
  case t of
    TBound k -> Left $ "bound type variable found in wfTy: " ++ (show t)
    TFree x -> findTVar ctx x
    TFun a b -> do
      k <- wfTy ctx a
      --checkKind "wfTy1" KTy k
      k' <- wfCTy ctx b
      --checkKind "wfTy2" KCTy k'
      return KTy
    TForall k b -> do
      let x = freshTVarInContext ctx b "t"
      wfCTy (CTVar x k : ctx) $ openTVar x b

wfInstVar :: Context -> Ty -> TC ()
wfInstVar ctx (TFree x) = do
  k <- findTVar ctx x
  tcDrop $ checkKindInst k
wfInstVar ctx t = Left $ "invalid type in effect set: " ++ (show t)

wfCTy :: Context -> CTy -> TC Kind
wfCTy ctx ct =
  case ct of
    CTy t r -> do
      mapM (wfInstVar ctx) $ Set.elems r
      k <- wfTy ctx t
      -- checkKind "wfCTy" KTy k
      return KCTy
    CExists k t -> do
      let x = freshTVarInContext ctx t "t"
      wfCTy (CTVar x k : ctx) $ openTVar x t

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
subTy a b = Left $ "subTy failed: " ++ (show a) ++ " <: " ++ (show b)

subCTy :: CTy -> CTy -> TC ()
subCTy a@(CTy t r) b@(CTy t' r') = do
  subTy t t'
  tcBool ("effect sets are not a subset " ++ (show a) ++ " <: " ++ (show b)) $ Set.isSubsetOf r r'
subCTy a@(CExists k t) b@(CExists k' t') = do
  checkKind "subCTy" k k'
  subCTy t t'

-- Typechecking
typecheckVal :: Context -> Val -> TC Ty
typecheckVal ctx v = do
  wfContext ctx
  case trace ("typecheckVal " ++ (show v)) v of
    Bound i -> Left $ "unable to typecheck bound variable " ++ (show v)
    Inst i -> Left $ "unable to typecheck inst " ++ (show v)
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

checkCTy :: CTy -> TC (Ty, Effs)
checkCTy (CTy t e) = return (t, e)
checkCTy t = Left $ "unexpected cty: " ++ (show t)

typecheckHandleCase :: Context -> Ty -> Effs -> (Val, Name, Comp) -> TC (Ty, Name, Effs)
typecheckHandleCase ctx t r (i, o, c) = do
  ti <- typecheckVal ctx i
  ki <- wfTy ctx ti
  e <- checkKindInst ki
  (e', a, b) <- findOp ctx o
  when (e /= e') (Left $ "instance and operation do not match in: " ++ (show i) ++ "#" ++ o)
  let x = freshVarInContext ctx c "x"
  let k = freshVarInContext ctx c "k"
  tc <- typecheckComp (CVar x a : CVar k (TFun b $ CTy t r) : ctx) (openR 1 (Free x) $ openVar k c)
  (t', r') <- checkCTy tc
  subTy t' t
  return (ti, o, r')

typecheckHandler :: Context -> [(Val, Name, Comp)] -> Ty -> Effs -> TC (Effs, Set Name, Effs)
typecheckHandler ctx m t r = do
  rs <- mapM (typecheckHandleCase ctx t r) m
  return $ foldr (\(a, b, e) (a', b', e') -> (Set.insert a a', Set.insert b b', Set.union e e')) (Set.empty, Set.empty, Set.empty) rs

checkInstanceHandled :: Context -> Set Name -> Ty -> TC (Maybe Ty)
checkInstanceHandled ctx os i = do
  k <- wfTy ctx i
  e <- checkKindInst k
  if Set.isSubsetOf (findOpNames ctx e) os then
    return $ Just i
  else
    return $ Nothing

typecheckComp :: Context -> Comp -> TC CTy
typecheckComp ctx c = do
  wfContext ctx
  case trace ("typecheckComp " ++ (show c)) c of
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
      ta <- typecheckComp ctx a
      (t, r) <- checkCTy ta
      let x = freshVarInContext ctx b "x"
      tb <- typecheckComp (CVar x t : ctx) (openVar x b)
      (t', r') <- checkCTy tb
      return $ CTy t' (Set.union r r')
    Op i o v -> do
      ti <- typecheckVal ctx i
      kti <- wfTy ctx ti
      e <- checkKindInst kti
      (e', a, b) <- findOp ctx o
      when (e /= e') (Left $ "effect and operation do not match in: " ++ (show c))
      t <- typecheckVal ctx v
      subTy t a
      return $ CTy b $ Set.singleton ti
    Handle c cr m -> do
      tc <- typecheckComp ctx c
      (t, r) <- checkCTy tc
      let x = freshVarInContext ctx cr "x"
      tcr <- typecheckComp (CVar x t : ctx) (openVar x cr)
      (t', r') <- checkCTy tcr
      (is, os, rs) <- typecheckHandler ctx m t' r'
      hs <- mapM (checkInstanceHandled ctx os) $ Set.elems is
      let handled = Set.fromList $ Maybe.mapMaybe id hs
      return $ CTy t' $ Set.union (Set.difference r handled) $ Set.union r' rs
    Unpack a b -> do
      ta <- typecheckComp ctx a
      case ta of
        CExists k te -> do
          let vx = freshVarInContext ctx b "x"
          let vt = freshVarInContext ctx b "t"
          tr <- typecheckComp (CVar vx (TFun "Unit" $ openTVar vt te) : CTVar vt k : ctx) (openTVar vt $ openVar vx b)
          if Set.member vt $ freeTVars tr then
            return $ CExists k $ closeTy vt tr
          else
            return tr
        _ -> Left $ "expected existential but got " ++ (show ta)
    New e -> do
      findEff ctx e
      return $ CExists (KInst e) $ CTy (TBound 0) Set.empty

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
  -- checkKind "inferComp" KCTy k
  return t

-- Reduce
findOpInHandler :: [(Val, Name, Comp)] -> Val -> Name -> Maybe Comp
findOpInHandler [] i o = Nothing
findOpInHandler ((i', o', c) : r) i o | i == i' && o == o' = Just c
findOpInHandler (_ : r) i o = findOpInHandler r i o

reduceComp :: Comp -> State Int Comp
reduceComp c =
  case {- trace ("reduceComp " ++ (show c)) -} c of
    t@(Return _) -> return t
    App (Abs t a) b -> reduceComp $ open b a
    AppT (AbsT k a) t -> reduceComp $ openTy t a
    New _ -> do
      i <- get
      put (i + 1)
      return $ Return $ Inst i
    Do a b -> do
      a' <- reduceComp a
      case a' of
        Return v -> reduceComp $ open v b
        Do a' b' -> return $ Do a' $ Do b' b
        Unpack a' b' -> return $ Unpack a' $ Do b' b
        a' -> return $ Do a' b
    Unpack a b -> do
      a' <- reduceComp a
      reduceComp $ open (Abs "Unit" a') b
    Handle c cr m -> do
      c' <- reduceComp c
      case c' of
        Return v -> reduceComp $ open v cr
        op@(Op i o v) -> Maybe.maybe (return op) (\c -> reduceComp $ openR 1 v $ open (Abs "_" cr) c) $ findOpInHandler m i o
        Do (Op i o v) b ->
          case findOpInHandler m i o of
            Just c ->
              reduceComp $ open v $ open (Abs "_" (Handle b cr m)) c
            Nothing ->
              return $ Do (Op i o v) (Handle b cr m)
        c' -> return $ Handle c' cr m
    c -> return c

reduce :: Comp -> Comp
reduce c = evalState (reduceComp c) 0

-- User AST
type EffsExpr = Set TyExpr
data TyExpr
  = TEVar Name
  | TEFun TyExpr TyExpr
  | TEForall Name Kind TyExpr
  | TEComp TyExpr EffsExpr
  | TEExists Name Kind TyExpr
  deriving (Eq)

instance Show TyExpr where
  show (TEVar x) = x
  show (TEFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"
  show (TEForall x k b) = "(forall(" ++ x ++ ":" ++ (show k) ++ "). " ++ (show b) ++ ")"
  show (TEComp t r) = (show t) ++ "!{" ++ (intercalate ", " $ map show $ Set.elems r) ++ "}"
  show (TEExists x k b) = "(exists(" ++ x ++ ":" ++ (show k) ++ "). " ++ (show b) ++ ")"

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
  r' <- mapM (toNamelessTyR k m) $ Set.elems r
  return $ CTy t' $ Set.fromList r'
toNamelessCTyR k m (TEExists x ki t) = do
  t' <- toNamelessCTyR (k + 1) (Map.insert x k m) t
  return $ CExists ki t'

toNamelessCTy :: TyExpr -> Either String CTy
toNamelessCTy = toNamelessCTyR 0 Map.empty

toNamelessTy :: TyExpr -> Either String Ty
toNamelessTy = toNamelessTyR 0 Map.empty

data EHandlerCase
  = ERet Name Expr EHandlerCase
  | ECase Expr Name Name Name Expr EHandlerCase
  | End
  deriving (Eq)

data Expr
  = EVar Name
  | EAbs Name TyExpr Expr
  | EAbsT Name Kind Expr
  | EApp Expr Expr
  | EAppT Expr TyExpr
  | EDo Name Expr Expr
  | EOp Expr Name Expr
  | EHandle Expr EHandlerCase
  | ENew Name
  | EUnpack Name Name Expr Expr
  deriving (Eq)

instance Show EHandlerCase where
  show (ERet x e r) = "return " ++ x ++ " -> " ++ (show e) ++ ", " ++ (show r)
  show (ECase i o x k e r) = (show i) ++ "#" ++ o ++ " " ++ x ++ " " ++ k ++ " -> " ++ (show e) ++ ", " ++ (show r)
  show End = ""

instance Show Expr where
  show (EVar x) = x
  show (EAbs x t e) = "(\\(" ++ x ++ ":" ++ (show t) ++ ") -> " ++ (show e) ++ ")"
  show (EAbsT x k e) = "(/\\(" ++ x ++ ":" ++ (show k) ++ ") -> " ++ (show e) ++ ")"
  show (EApp a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (EAppT a b) = "(" ++ (show a) ++ " [" ++ (show b) ++ "])"
  show (EDo x a b) = "(" ++ x ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"
  show (EOp i op v) = (show i) ++ "#" ++ op ++ "(" ++ (show v) ++ ")"
  show (EHandle e h) = "handle (" ++ (show e) ++ ") { " ++ (show h) ++ "}"
  show (ENew e) = "(new " ++ e ++ ")"
  show (EUnpack t x a b) = "((" ++ t ++ ", " ++ x ++ ") <- " ++ (show a) ++ "; " ++ (show b) ++ ")"

instance IsString Expr where
  fromString = EVar

freeVarsInExpr :: Expr -> Set Name
freeVarsInExpr (EVar x) = Set.singleton x
freeVarsInExpr (EAbs x t b) = Set.delete x $ freeVarsInExpr b 
freeVarsInExpr (EAbsT x k b) = freeVarsInExpr b
freeVarsInExpr (EApp a b) = Set.union (freeVarsInExpr a) (freeVarsInExpr b)
freeVarsInExpr (EAppT a b) = freeVarsInExpr a
freeVarsInExpr (EDo x a b) = Set.union (freeVarsInExpr a) (Set.delete x $ freeVarsInExpr b)
freeVarsInExpr (EUnpack t x a b) = Set.union (freeVarsInExpr a) (Set.delete x $ freeVarsInExpr b)
freeVarsInExpr (EOp i op v) = Set.union (freeVarsInExpr i) (freeVarsInExpr v)
freeVarsInExpr (ENew e) = Set.empty
freeVarsInExpr (EHandle e h) = Set.union (freeVarsInExpr e) (freeVarsInHandler h)
  where
    freeVarsInHandler (ERet x e r) = Set.union (Set.delete x $ freeVarsInExpr e) (freeVarsInHandler r)
    freeVarsInHandler (ECase i o x k e r) = Set.union (freeVarsInExpr i) $ Set.union (Set.delete x $ Set.delete k $ freeVarsInExpr e) (freeVarsInHandler r)
    freeVarsInHandler End = Set.empty

exprIsVal :: Expr -> Bool
exprIsVal (EVar _) = True
exprIsVal (EAbs _ _ _) = True
exprIsVal (EAbsT _ _ _) = True
exprIsVal (EApp _ _) = False
exprIsVal (EAppT _ _) = False
exprIsVal (EDo _ _ _) = False
exprIsVal (EOp _ _ _) = False
exprIsVal (EHandle _ _) = False
exprIsVal (ENew _) = False
exprIsVal (EUnpack _ _ _ _) = False

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

toNamelessHandlerR :: (Int, Map Name Int) -> (Int, Map Name Int) -> EHandlerCase -> Either String (Comp, [(Val, Name, Comp)])
toNamelessHandlerR (kt, mt) (ke, me) (ERet x e r) = do
  e' <- toNamelessCompR (kt, mt) (ke + 1, Map.insert x ke me) e
  (cr, m) <- toNamelessHandlerR (kt, mt) (ke, me) r
  return (e', m)
toNamelessHandlerR (kt, mt) (ke, me) (ECase i o x k e r) = do
  i' <- toNamelessValR (kt, mt) (ke, me) i
  e' <- toNamelessCompR (kt, mt) (ke + 2, Map.insert k (ke + 1) $ Map.insert x ke me) e
  (cr, m) <- toNamelessHandlerR (kt, mt) (ke, me) r
  return (cr, (i', o, e') : m)
toNamelessHandlerR (kt, mt) (ke, me) End = return (Return (Bound 0), [])

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
toNamelessCompR (kt, mt) (ke, me) e@(EUnpack t x a b) = do
  a' <- toNamelessCompR (kt, mt) (ke, me) a
  b' <- toNamelessCompR (kt + 1, Map.insert t kt mt) (ke + 1, Map.insert x ke me) b
  return $ Unpack a' b'
toNamelessCompR (kt, mt) (ke, me) e@(EOp i op v) =
  if exprIsComp i then
    if exprIsComp v then
      let x = freshName (Set.union (freeVarsInExpr v) (freeVarsInExpr i)) "x" in
      let y = freshName (Set.union (freeVarsInExpr v) (freeVarsInExpr i)) "y" in
      toNamelessCompR (kt, mt) (ke, me) $ EDo x i $ EDo y v $ EOp (EVar x) op (EVar y)
    else
      let x = freshName (freeVarsInExpr v) "x" in
      toNamelessCompR (kt, mt) (ke, me) $ EDo x i $ EOp (EVar x) op v
  else
    if exprIsComp v then
      let x = freshName (freeVarsInExpr i) "x" in
      toNamelessCompR (kt, mt) (ke, me) $ EDo x v $ EOp i op (EVar x)
    else do
      i' <- toNamelessValR (kt, mt) (ke, me) i
      v' <- toNamelessValR (kt, mt) (ke, me) v
      return $ Op i' op v'
toNamelessCompR (kt, mt) (ke, me) (EHandle c h) = do
  c' <- toNamelessCompR (kt, mt) (ke, me) c
  (cr, m) <- toNamelessHandlerR (kt, mt) (ke, me) h
  return $ Handle c' cr m
toNamelessCompR (kt, mt) (ke, me) (ENew e) = return $ New e
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
    COp "put" "State" "Bool" "Unit",

    CEff "Flip",
    COp "flip" "Flip" "Unit" "Bool",

    CTVar "i" $ KInst "Flip",
    CVar "i" "i"
  ]

eapps :: Expr -> [Expr] -> Expr
eapps f [] = EApp f "Unit"
eapps f [x] = EApp f x
eapps f (x : xs) = eapps (EApp f x) xs

force :: Expr -> Expr
force c = EApp c "Unit"

flipH :: Expr -> Expr -> Expr
flipH i c = EHandle c $
  ECase i "flip" "x" "k" (EApp "k" "False") $
  End

stateH :: Expr -> Expr -> Expr
stateH i c = EHandle c $
  ERet "x" (EAbs "s" "Bool" "x") $
  ECase i "get" "x" "k" (EAbs "s" "Bool" $ eapps "k" ["s", "s"]) $
  ECase i "put" "s" "k" (EAbs "_" "Bool" $ eapps "k" ["Unit", "s"]) $
  End
  
stateF :: Expr -> Expr -> Expr -> Expr
stateF i v c = EApp (stateH i c) v

refH :: Expr -> Expr -> Expr
refH v a = EUnpack "tj" "ji" (ENew "State") $ EDo "j" (EApp "ji" "Unit") $ stateF "j" v $ EApp (EAppT a "tj") "j"

term :: Expr
term =
    refH "True" $ EAbsT "tr" (KInst "State") $ EAbs "r" "tr" $ "r"

main :: IO ()
main = do
  putStrLn $ show term
  let t = toNamelessComp term
  putStrLn $ showEither t
  case t of
    Right c -> do
      putStrLn $ showEither $ inferComp ctx c
      putStrLn $ show $ reduce c
    Left _ -> return ()
