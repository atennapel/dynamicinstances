{--
TODO:
  - polymorphic effects
  - polymorphic operations
  - subtyping/ascription
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

type InstId = Int

initialInstId :: InstId
initialInstId = 0

nextInstId :: InstId -> InstId
nextInstId = (+ 1)

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
  deriving (Eq, Ord)

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
  | TInst ValTy Name
  deriving (Eq, Ord)

instance Show ValTy where
  show (TVar x) = show x
  show (TFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"
  show (TForall x t b) = "(forall(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"
  show (TInst a b) = "(Inst " ++ (show a) ++ " " ++ (show b) ++ ")"

instance IsString ValTy where
  fromString = TVar . Free . Name

instance HasTVar ValTy where
  openTyR k u t@(TVar (Bound m)) = if m == k then u else t
  openTyR k u t@(TVar _) = t
  openTyR k u (TFun a b) = TFun (openTyR k u a) (openTyR k u b)
  openTyR k u (TForall n ki c) = TForall n ki $ openTyR (k + 1) u c
  openTyR k u (TInst a b) = TInst (openTyR k u a) b

  closeTyR k x t@(TVar (Bound m)) = t
  closeTyR k x t@(TVar (Free y)) = if x == y then TVar (Bound k) else t
  closeTyR k x (TFun a b) = TFun (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (TForall n ki c) = TForall n ki $ closeTyR (k + 1) x c
  closeTyR k u (TInst a b) = TInst (closeTyR k u a) b

  isLocallyClosedTyR k (TVar (Bound m)) = m < k
  isLocallyClosedTyR k (TVar _) = True
  isLocallyClosedTyR k (TFun a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (TForall n ki c) = isLocallyClosedTyR (k + 1) c
  isLocallyClosedTyR k (TInst a b) = isLocallyClosedTyR k a

  freeTVars (TVar (Bound _)) = Set.empty
  freeTVars (TVar (Free x)) = Set.singleton x
  freeTVars (TFun a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (TForall n ki c) = freeTVars c
  freeTVars (TInst c b) = freeTVars c

instance NamelessTy ValTy where
  toNamelessTy t@(TVar _) = t
  toNamelessTy (TFun a b) = TFun (toNamelessTy a) (toNamelessTy b)
  toNamelessTy (TForall n k t) = TForall n k $ toNamelessTy (closeTy n t)
  toNamelessTy (TInst a b) = TInst (toNamelessTy a) b

  toNamedTy t@(TVar _) = t
  toNamedTy (TFun a b) = TFun (toNamedTy a) (toNamedTy b)
  toNamedTy (TForall n k t) = TForall n k $ toNamedTy (openTVar n t)
  toNamedTy (TInst a b) = TInst (toNamedTy a) b

-- computation types
type Eff = (ValTy, Name)
newtype Effs = Effs (Set Eff)
  deriving (Eq, Ord)

showEff :: Eff -> String
showEff (i, e) = (show i) ++ "#" ++ (show e)

instance Show Effs where
  show (Effs r) = "{" ++ (intercalate ", " $ map showEff $ Set.elems r) ++ "}"

instance (HasTVar a) => HasTVar (a, b) where
  openTyR k u (a, b) = (openTyR k u a, b)

  closeTyR k u (a, b) = (closeTyR k u a, b)

  isLocallyClosedTyR k (a, b) = isLocallyClosedTyR k a

  freeTVars (a, b) = freeTVars a

instance (NamelessTy a) => NamelessTy (a, b) where
  toNamelessTy (a, b) = (toNamelessTy a, b)

  toNamedTy (a, b) = (toNamedTy a, b)

instance HasTVar Effs where
  openTyR k u (Effs r) = Effs $ Set.map (openTyR k u) r

  closeTyR k u (Effs r) = Effs $ Set.map (closeTyR k u) r

  isLocallyClosedTyR k (Effs r) = all (isLocallyClosedTyR k) $ Set.elems r
  
  freeTVars (Effs r) = Set.unions $ map freeTVars $ Set.elems r

instance NamelessTy Effs where
  toNamelessTy (Effs r) = Effs $ Set.map toNamelessTy r

  toNamedTy (Effs r) = Effs $ Set.map toNamedTy r

emptyEffs :: Effs
emptyEffs = Effs $ Set.empty

singletonEffs :: Eff -> Effs
singletonEffs t = Effs $ Set.singleton t

liftEffs :: (Set Eff -> Set Eff -> t) -> Effs -> Effs -> t
liftEffs f (Effs a) (Effs b) = f a b

liftEffsFull :: (Set Eff -> Set Eff -> Set Eff) -> Effs -> Effs -> Effs
liftEffsFull f a b = Effs $ liftEffs f a b

insertEffs :: Eff -> Effs -> Effs
insertEffs e (Effs es) = Effs $ Set.insert e es 

unionEffs :: Effs -> Effs -> Effs
unionEffs = liftEffsFull Set.union

isSubsetOfEffs :: Effs -> Effs -> Bool
isSubsetOfEffs = liftEffs Set.isSubsetOf

differenceEffs :: Effs -> Effs -> Effs
differenceEffs = liftEffsFull Set.difference

data CompTy
  = TAnnot ValTy Effs
  deriving (Eq, Ord)

instance Show CompTy where
  show (TAnnot t (Effs r)) | Set.null r = show t
  show (TAnnot t r) = (show t) ++ "!" ++ (show r)

instance IsString CompTy where
  fromString x = TAnnot (TVar $ Free $ Name x) emptyEffs

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
  | Inst InstId
  deriving (Eq)

instance Show Val where
  show (Var x) = show x
  show (Abs x t b) = "(\\(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"
  show (AbsT x t b) = "(/\\(" ++ (show x) ++ " : " ++ (show t) ++ "). " ++ (show b) ++ ")"
  show (Inst id) = "(inst " ++ (show id) ++ ")"

instance IsString Val where
  fromString = Var . Free . Name

instance HasVar Val where
  openR k u t@(Var (Bound m)) = if m == k then u else t
  openR k u t@(Var (Free _)) = t
  openR k u (Abs n t c) = Abs n t $ openR (k + 1) u c
  openR k u (AbsT n ki c) = AbsT n ki $ openR k u c
  openR k u i@(Inst _) = i

  closeR _ _ t@(Var (Bound _)) = t
  closeR k x t@(Var (Free y)) = if x == y then Var (Bound k) else t
  closeR k x (Abs n t c) = Abs n t $ closeR (k + 1) x c
  closeR k x (AbsT n ki c) = AbsT n ki $ closeR k x c
  closeR k u i@(Inst _) = i

  isLocallyClosedR k (Var (Bound m)) = m < k
  isLocallyClosedR k (Var (Free _)) = True
  isLocallyClosedR k (Abs n t c) = isLocallyClosedR (k + 1) c
  isLocallyClosedR k (AbsT n ki c) = isLocallyClosedR k c
  isLocallyClosedR k i@(Inst _) = True

  freeVars (Var (Bound _)) = Set.empty
  freeVars (Var (Free x)) = Set.singleton x
  freeVars (Abs n t c) = freeVars c
  freeVars (AbsT n ki c) = freeVars c
  freeVars (Inst _) = Set.empty

instance HasTVar Val where
  openTyR k u t@(Var (Bound _)) = t
  openTyR k u t@(Var (Free _)) = t
  openTyR k u (Abs n t c) = Abs n (openTyR k u t) (openTyR k u c)
  openTyR k u (AbsT n ki c) = AbsT n ki $ openTyR (k + 1) u c
  openTyR k u i@(Inst _) = i

  closeTyR k x t@(Var (Bound _)) = t
  closeTyR k x t@(Var (Free _)) = t
  closeTyR k x (Abs n t c) = Abs n (closeTyR k x t) (closeTyR k x c)
  closeTyR k x (AbsT n ki c) = AbsT n ki $ closeTyR (k + 1) x c
  closeTyR k u i@(Inst _) = i

  isLocallyClosedTyR k (Var (Bound _)) = True
  isLocallyClosedTyR k (Var (Free _)) = True
  isLocallyClosedTyR k (Abs n t c) = isLocallyClosedTyR k t && isLocallyClosedTyR k c
  isLocallyClosedTyR k (AbsT n ki c) = isLocallyClosedTyR (k + 1) c
  isLocallyClosedTyR k i@(Inst _) = True

  freeTVars (Var (Bound _)) = Set.empty
  freeTVars (Var (Free _)) = Set.empty
  freeTVars (Abs n t c) = Set.union (freeTVars t) (freeTVars c)
  freeTVars (AbsT n ki c) = freeTVars c
  freeTVars (Inst _) = Set.empty

instance Nameless Val where
  toNameless t@(Var _) = t
  toNameless (Abs n t e) = Abs n (toNamelessTy t) (toNameless $ close n e)
  toNameless (AbsT n k e) = AbsT n k $ toNameless (closeTy n e)
  toNameless i@(Inst _) = i

  toNamed t@(Var _) = t
  toNamed (Abs n t e) = Abs n (toNamedTy t) (toNamed $ openVar n e)
  toNamed (AbsT n k e) = AbsT n k $ toNamed (openTVar n e)
  toNamed i@(Inst _) = i

-- computations
data Handler
  = HReturn Name Comp
  | HOp Val Name Name Name Comp Handler
  deriving (Eq)

instance Show Handler where
  show (HReturn x c) = "return " ++ (show x) ++ " -> " ++ (show c)
  show (HOp i o x k c r) = (show i) ++ "#" ++ (show o) ++ " " ++ (show x) ++ " " ++ (show k) ++ " -> " ++ (show c) ++ ", " ++ (show r)

instance HasVar Handler where
  openR k u (HReturn x v) = HReturn x (openR (k + 1) u v)
  openR k u (HOp i o x k' c r) = HOp (openR k u i) o x k' (openR (k + 2) u c) (openR k u r)

  closeR k u (HReturn x v) = HReturn x (closeR (k + 1) u v)
  closeR k u (HOp i o x k' c r) = HOp (closeR k u i) o x k' (closeR (k + 2) u c) (closeR k u r)

  isLocallyClosedR k (HReturn x v) = isLocallyClosedR (k + 1) v
  isLocallyClosedR k (HOp i o x k' c r) = isLocallyClosedR k i && isLocallyClosedR (k + 2) c && isLocallyClosedR k r

  freeVars (HReturn x v) = freeVars v
  freeVars (HOp i o x k c r) = Set.union (freeVars i) $ Set.union (freeVars c) (freeVars r)

instance HasTVar Handler where
  openTyR k u (HReturn x v) = HReturn x (openTyR k u v)
  openTyR k u (HOp i o x k' c r) = HOp (openTyR k u i) o x k' (openTyR k u c) (openTyR k u r)

  closeTyR k u (HReturn x v) = HReturn x (closeTyR k u v)
  closeTyR k u (HOp i o x k' c r) = HOp (closeTyR k u i) o x k' (closeTyR k u c) (closeTyR k u r)

  isLocallyClosedTyR k (HReturn x v) = isLocallyClosedTyR k v
  isLocallyClosedTyR k (HOp i o x k' c r) = isLocallyClosedTyR k i && isLocallyClosedTyR k c && isLocallyClosedTyR k r

  freeTVars (HReturn x v) = freeTVars v
  freeTVars (HOp i o x k' c r) = Set.union (freeTVars i) $ Set.union (freeTVars c) (freeTVars r)

instance Nameless Handler where
  toNameless (HReturn x v) = HReturn x (toNameless $ close x v)
  toNameless (HOp i o x k c r) = HOp (toNameless i) o x k (toNameless $ closeR 1 x $ close k c) (toNameless r)

  toNamed (HReturn x v) = HReturn x (toNamed $ openVar x v)
  toNamed (HOp i o x k c r) = HOp (toNamed i) o x k (toNamed $ openR 1 (Var $ Free x) $ openVar k c) (toNamed r)

opsFromHandler :: Handler -> [Name]
opsFromHandler (HReturn _ _) = []
opsFromHandler (HOp _ o _ _ _ r) = o : opsFromHandler r

findOpInHandler :: Name -> Handler -> Maybe (Val, Name, Name, Comp)
findOpInHandler o (HReturn _ _) = Nothing
findOpInHandler o (HOp i o' x k c _) | o == o' = Just (i, x, k, c)
findOpInHandler o (HOp _ _ _ _ _ r) = findOpInHandler o r

findEffInHandler :: Val -> Name -> Handler -> Maybe (Name, Name, Comp)
findEffInHandler i o (HReturn _ _) = Nothing
findEffInHandler i o (HOp i' o' x k c _) | i == i' && o == o' = Just (x, k, c)
findEffInHandler i o (HOp _ _ _ _ _ r) = findEffInHandler i o r

getReturnInHandler :: Handler -> (Name, Comp)
getReturnInHandler (HReturn x v) = (x, v)
getReturnInHandler (HOp _ _ _ _ _ r) = getReturnInHandler r

data Comp
  = Return Val
  | App Val Val
  | AppT Val ValTy
  | Do Name Comp Comp
  | Weaken Comp Effs
  | Op Val Name Val
  | Handle Comp Handler
  | Fresh Name Comp
  | New ValTy Name
  deriving (Eq)

instance Show Comp where
  show (Return v) = "(return " ++ (show v) ++ ")"
  show (App a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (AppT a t) = "(" ++ (show a) ++ " [" ++ (show t) ++ "])"
  show (Do x a b) = "(" ++ (show x) ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"
  show (Weaken c (Effs r)) | Set.null r = "(weaken " ++ (show c) ++ " {})"
  show (Weaken c r) = "(weaken " ++ (show c) ++ " " ++ (show r) ++ ")"
  show (Op i o v) = (show i) ++ "#" ++ (show o) ++ "(" ++ (show v) ++ ")"
  show (Handle c h) = "handle(" ++ (show c) ++ ") { " ++ (show h) ++ " }"
  show (Fresh x c) = "(fresh " ++ (show x) ++ "; " ++ (show c) ++ ")"
  show (New t e) = "(new " ++ (show t) ++ "@" ++ (show e) ++ ")"

instance IsString Comp where
  fromString = Return . Var . Free . Name

instance HasVar Comp where
  openR k u (Return v) = Return (openR k u v)
  openR k u (App a b) = App (openR k u a) (openR k u b)
  openR k u (AppT a b) = AppT (openR k u a) b
  openR k u (Do n a b) = Do n (openR k u a) (openR (k + 1) u b)
  openR k u (Weaken c r) = Weaken (openR k u c) r
  openR k u (Op i o b) = Op (openR k u i) o (openR k u b)
  openR k u (Handle c r) = Handle (openR k u c) (openR k u r)
  openR k u (Fresh x c) = Fresh x (openR k u c)
  openR k u (New t e) = New t e

  closeR k u (Return v) = Return (closeR k u v)
  closeR k u (App a b) = App (closeR k u a) (closeR k u b)
  closeR k u (AppT a b) = AppT (closeR k u a) b
  closeR k u (Do n a b) = Do n (closeR k u a) (closeR (k + 1) u b)
  closeR k u (Weaken c r) = Weaken (closeR k u c) r
  closeR k u (Op i o b) = Op (closeR k u i) o (closeR k u b)
  closeR k u (Handle c r) = Handle (closeR k u c) (closeR k u r)
  closeR k u (Fresh x c) = Fresh x (closeR k u c)
  closeR k u (New t e) = New t e

  isLocallyClosedR k (Return v) = isLocallyClosedR k v
  isLocallyClosedR k (App a b) = isLocallyClosedR k a && isLocallyClosedR k b
  isLocallyClosedR k (AppT a b) = isLocallyClosedR k a
  isLocallyClosedR k (Do n a b) = isLocallyClosedR k a && isLocallyClosedR (k + 1) b
  isLocallyClosedR k (Weaken c r) = isLocallyClosedR k c
  isLocallyClosedR k (Op i o b) = isLocallyClosedR k i && isLocallyClosedR k b
  isLocallyClosedR k (Handle a b) = isLocallyClosedR k a && isLocallyClosedR k b
  isLocallyClosedR k (Fresh o b) = isLocallyClosedR k b
  isLocallyClosedR k (New _ _) = True

  freeVars (Return v) = freeVars v
  freeVars (App a b) = Set.union (freeVars a) (freeVars b)
  freeVars (AppT a b) = freeVars a
  freeVars (Do n a b) = Set.union (freeVars a) (freeVars b)
  freeVars (Weaken c r) = freeVars c
  freeVars (Op i o a) = Set.union (freeVars i) (freeVars a)
  freeVars (Handle a b) = Set.union (freeVars a) (freeVars b)
  freeVars (Fresh o a) = freeVars a
  freeVars (New _ _) = Set.empty

instance HasTVar Comp where
  openTyR k u (Return v) = Return (openTyR k u v)
  openTyR k u (App a b) = App (openTyR k u a) (openTyR k u b)
  openTyR k u (AppT a b) = AppT (openTyR k u a) (openTyR k u b)
  openTyR k u (Do n a b) = Do n (openTyR k u a) (openTyR k u b)
  openTyR k u (Weaken c r) = Weaken (openTyR k u c) r
  openTyR k u (Op i o b) = Op (openTyR k u i) o (openTyR k u b)
  openTyR k u (Handle a b) = Handle (openTyR k u a) (openTyR k u b)
  openTyR k u (Fresh o b) = Fresh o (openTyR (k + 1) u b)
  openTyR k u (New t e) = New (openTyR k u t) e

  closeTyR k u (Return v) = Return (closeTyR k u v)
  closeTyR k u (App a b) = App (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (AppT a b) = AppT (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (Do n a b) = Do n (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (Weaken c r) = Weaken (closeTyR k u c) r
  closeTyR k u (Op i o b) = Op (closeTyR k u i) o (closeTyR k u b)
  closeTyR k u (Handle a b) = Handle (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (Fresh o b) = Fresh o (closeTyR (k + 1) u b)
  closeTyR k u (New t e) = New (closeTyR k u t) e

  isLocallyClosedTyR k (Return v) = isLocallyClosedTyR k v
  isLocallyClosedTyR k (App a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (AppT a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Do n a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Weaken c r) = isLocallyClosedTyR k c
  isLocallyClosedTyR k (Op i o v) = isLocallyClosedTyR k i && isLocallyClosedTyR k v
  isLocallyClosedTyR k (Handle a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Fresh o v) = isLocallyClosedTyR (k + 1) v
  isLocallyClosedTyR k (New t e) = isLocallyClosedTyR k t

  freeTVars (Return v) = freeTVars v
  freeTVars (App a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (AppT a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Do n a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Weaken c r) = freeTVars c
  freeTVars (Op i o v) = Set.union (freeTVars i) (freeTVars v)
  freeTVars (Handle a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Fresh o v) = freeTVars v
  freeTVars (New t e) = freeTVars t

instance Nameless Comp where
  toNameless (Return e) = Return (toNameless e)
  toNameless (App a b) = App (toNameless a) (toNameless b)
  toNameless (AppT e t) = AppT (toNameless e) (toNamelessTy t)
  toNameless (Do n a b) = Do n (toNameless a) (toNameless $ close n b)
  toNameless (Weaken c r) = Weaken (toNameless c) r
  toNameless (Op i o e) = Op (toNameless i) o (toNameless e)
  toNameless (Handle a b) = Handle (toNameless a) (toNameless b)
  toNameless (Fresh x e) = Fresh x (toNameless $ closeTy x e)
  toNameless (New t e) = New (toNamelessTy t) e

  toNamed (Return e) = Return (toNamed e)
  toNamed (App a b) = App (toNamed a) (toNamed b)
  toNamed (AppT e t) = AppT (toNamed e) (toNamedTy t)
  toNamed (Do n a b) = Do n (toNamed a) (toNamed $ openVar n b)
  toNamed (Weaken c r) = Weaken (toNamed c) r
  toNamed (Op i o e) = Op (toNamed i) o (toNamed e)
  toNamed (Handle a b) = Handle (toNamed a) (toNamed b)
  toNamed (Fresh x e) = Fresh x (toNamed $ openTVar x e)
  toNamed (New t e) = New (toNamedTy t) e

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
  | CEff Name
  | COp Name Name ValTy ValTy

instance Show Elem where
  show (CKVar x) = "kind " ++ (show x)
  show (CTVar x t) = (show x) ++ " :k " ++ (show t)
  show (CVar x t) = (show x) ++ " : " ++ (show t)
  show (CEff x) = "effect " ++ (show x)
  show (COp o e pt rt) = "op " ++ (show o) ++ " of " ++ (show e) ++ " : " ++ (show pt) ++ " -> " ++ (show rt)

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

effs :: Context -> Set Name
effs (Context ctx) = Set.fromList $
  Maybe.mapMaybe (\e -> case e of { CEff x -> Just x; _ -> Nothing }) ctx

ops :: Context -> Name -> Set Name
ops (Context ctx) x = Set.fromList $
  Maybe.mapMaybe (\e -> case e of { COp o x' _ _ | x == x' -> Just o; _ -> Nothing }) ctx

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

findEff :: Context -> Name -> TC ()
findEff ctx x = findElem ctx (\e -> case e of { CEff y | x == y -> Just (); _ -> Nothing }) $ "undefined eff " ++ (show x)

findOp :: Context -> Name -> TC (Name, ValTy, ValTy)
findOp ctx x = findElem ctx (\e -> case e of { COp y e pt rt | x == y -> Just (e, pt, rt); _ -> Nothing }) $ "undefined op " ++ (show x)

freshTVarInContext :: HasTVar t => Context -> t -> Name -> Name
freshTVarInContext ctx t x = freshName (Set.union (tvars ctx) (freeTVars t)) x

freshVarInContext :: HasVar t => Context -> t -> Name -> Name
freshVarInContext ctx t x = freshName (Set.union (vars ctx) (freeVars t)) x

-- initial context
kType :: Kind
kType = "Type"

kName :: Kind
kName = "Name"

initialContext :: Context
initialContext = context
  [
    CKVar "Type",
    CKVar "Name"
  ]

-- util
checkKind :: Kind -> Kind -> String -> TC ()
checkKind k k' msg =
  if k == k' then
    return ()
  else
    err $ "kind mismatch: expected " ++ (show k) ++ " but got " ++ (show k') ++ " in " ++ msg
  
-- subtyping
eqValTy :: ValTy -> ValTy -> String -> TC ()
eqValTy (TVar v1) (TVar v2) msg | v1 == v2 = return ()
eqValTy (TFun a1 b1) (TFun a2 b2) msg = do
  eqValTy a1 a2 msg
  eqCompTy b1 b2 msg
eqValTy f1@(TForall n1 k1 t1) f2@(TForall n2 k2 t2) msg = do
  checkKind k1 k2 $ "kind mismatch in " ++ (show f1) ++ " <: " ++ (show f2) ++ " in " ++ msg
  let x = freshName (Set.union (freeTVars t1) (freeTVars t2)) n1
  eqCompTy (openTVar x t1) (openTVar x t2) msg
eqValTy (TInst a e) (TInst b e') msg | e == e' = eqValTy a b msg
eqValTy x y msg = err $ "type equality failed: expected " ++ (show x) ++ " but got " ++ (show y) ++ " in " ++ msg

eqCompTy :: CompTy -> CompTy -> String -> TC ()
eqCompTy tr1@(TAnnot t1 r1) tr2@(TAnnot t2 r2) msg = do
  eqValTy t1 t2 msg
  tcBool ("effects not equal " ++ (show tr1) ++ " and " ++ (show tr2) ++ " in " ++ msg) $ r1 == r2

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
wfValTy ctx t@(TInst n e) = do
  findEff ctx e
  k <- wfValTy ctx n
  checkKind kName k $ "instance type " ++ (show t)
  return kType

wfEff :: Context -> Eff -> TC ()
wfEff ctx eff@(v, e) = do
  k <- wfValTy ctx v
  checkKind kName k $ "type annotation: " ++ (showEff eff)
  findEff ctx e
  return ()

wfEffs :: Context -> Effs -> TC ()
wfEffs ctx (Effs r) = mapM_ (wfEff ctx) r

wfCompTy :: Context -> CompTy -> TC Kind
wfCompTy ctx ct@(TAnnot t r) = do
  kt <- wfValTy ctx t
  wfEffs ctx r
  return kt

wfElem :: Context -> Elem -> TC ()
wfElem ctx (CKVar x) = tcNot ("duplicate kvar " ++ (show x)) $ findKVar ctx x
wfElem ctx (CEff x) = tcNot ("duplicate effect " ++ (show x)) $ findEff ctx x
wfElem ctx (CTVar x k) = do
  tcNot ("duplicate tvar " ++ (show x)) $ findKVar ctx x
  wfKind ctx k
wfElem ctx e@(CVar x t) = do
  tcNot ("duplicate var " ++ (show x)) $ findKVar ctx x
  k <- wfValTy ctx t
  checkKind kType k $ "cvar in context " ++ (show e)
wfElem ctx (COp o e a b) = do
  findEff ctx e
  tcNot ("duplicate operation " ++ (show o)) $ findOp ctx o
  let n = freshName (Set.union (tvars ctx) $ Set.union (freeTVars a) (freeTVars b)) "n"
  let ctx' = add ctx (CTVar n kName)
  k <- wfValTy ctx' (openTVar n a)
  checkKind kType k $ "parameter type of operation " ++ (show o)
  k <- wfValTy ctx' (openTVar n a)
  checkKind kType k $ "return type of operation " ++ (show o)

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
    Inst _ ->
      err $ "cannot type instance " ++ (show v)

typecheckInst :: Context -> Val -> TC (ValTy, Name)
typecheckInst ctx v = do
  t <- typecheckVal ctx v
  case t of
    TInst n e -> return (n, e)
    _ -> err $ "expected instance type but got " ++ (show t) ++ " in " ++ (show v)

typecheckHandler :: Context -> ValTy -> Handler -> TC (Effs, CompTy)
typecheckHandler ctx rt (HReturn x c) = do
  t <- typecheckComp (add ctx $ CVar x rt) $ openVar x c
  return (emptyEffs, t)
typecheckHandler ctx rt (HOp i o x k c r) = do
  (n, e) <- typecheckInst ctx i
  (e', a, b) <- findOp ctx o
  tcBool ("effect mismatch in handler case: " ++ (show i) ++ "#" ++ (show o)) $ e == e'
  (es, ret) <- typecheckHandler ctx rt r
  ret' <- typecheckComp (adds ctx [CVar x (openTy n a), CVar k (TFun (openTy n b) ret)]) $ openR 1 (Var $ Free x) $ openVar k c
  eqCompTy ret ret' $ "handler case: " ++ (show i) ++ "#" ++ (show o) ++ " " ++ (show x) ++ " " ++ (show k) ++ " -> " ++ (show c)
  return (insertEffs (n, e) es, ret)

typecheckComp :: Context -> Comp -> TC CompTy
typecheckComp ctx c = do
  wfContext ctx
  case c of
    Return v -> do
      t <- typecheckVal ctx v
      return $ TAnnot t emptyEffs
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
      -- tcBool ("effect mismatch, do expression second computation: " ++ (show c)) $ r == r'
      -- return tb
      return $ TAnnot t' (unionEffs r r')
    Weaken c' r -> do
      wfEffs ctx r
      tr@(TAnnot t r') <- typecheckComp ctx c'
      tcBool ("cannot weaken from " ++ (show tr) ++ " in " ++ (show c)) $ isSubsetOfEffs r' r
      return $ TAnnot t r
    Op i o v -> do
      (n, e) <- typecheckInst ctx i
      (e', a, b) <- findOp ctx o
      tcBool ("effect mismatch in operation call: " ++ (show c)) $ e == e'
      t <- typecheckVal ctx v
      eqValTy (openTy n a) t $ "operation call " ++ (show c)
      return $ TAnnot (openTy n b) $ singletonEffs (n, e)
    Handle c' h -> do
      TAnnot t r <- typecheckComp ctx c'
      (es, rt@(TAnnot t' r')) <- typecheckHandler ctx t h
      trace (show (r, r', es, unionEffs r' $ differenceEffs r es, rt)) $ return ()
      return $ rt --TAnnot t' (unionEffs r' $ differenceEffs r es)
    Fresh x c' -> do
      let x' = freshTVarInContext ctx c' x
      tr <- typecheckComp (add ctx $ CTVar x' kName) $ openTVar x' c'
      tcBool ("name " ++ (show x') ++ " escaped its scope in " ++ (show tr) ++ " in " ++ (show c)) $ not $ Set.member x' (freeTVars tr)
      return tr
    New t e -> do
      k <- wfValTy ctx t
      checkKind kName k (show t)
      findEff ctx e
      return $ TAnnot (TInst t e) emptyEffs

infer :: Context -> Comp -> TC CompTy
infer ctx e = do
  tcBool ("expression not locally closed: " ++ (show e)) $ isLocallyClosed e
  wfContext ctx
  t <- typecheckComp ctx e
  trace (show t) $ return ()
  k <- wfCompTy ctx t
  checkKind kType k $ "infer: " ++ (show t)
  return t

-- semantics
incInstId :: State InstId InstId
incInstId = do
  x <- get
  put (nextInstId x)
  return x

reduceR :: Comp -> State InstId Comp
reduceR co =
  case co of
    c@(Return _) -> return c
    c@(Op _ _ _) -> return c
    Weaken c _ -> reduceR c
    App (Abs x _ a) b -> reduceR $ open b a
    AppT (AbsT x _ a) t -> reduceR $ openTy t a
    Do x a b -> do
      c <- reduceR a
      case c of
        Return v -> reduceR $ open v b
        Do x' a' b' -> reduceR $ Do x' a' $ Do x b' b
        a' -> return $ Do x a' b
    Handle c h -> do
      c' <- reduceR c
      case c' of
        Return v ->
          let (x, b) = getReturnInHandler h in reduceR $ open v b
        c'@(Op i o v) ->
          case findEffInHandler i o h of
            Just (x, _, b) ->
              reduceR $ openR 1 v $ open (Abs x "_" $ Handle (Return $ Var $ Bound 0) h) b
            Nothing -> return $ Do "x" c' $ Handle (Return $ Var $ Bound 0) h
        c'@(Do x (Op i o v) b) ->
          case findEffInHandler i o h of
            Just (x, _, b') ->
              reduceR $ openR 1 v $ open (Abs x "_" $ Handle b h) b'
            Nothing -> return $ Do x (Op i o v) $ Handle b h
        c' -> return $ Handle c' h
    Fresh x c -> reduceR $ openTVar x c
    c@(New t e) -> do
      i <- incInstId
      return $ Return (Inst i)
    c -> return c

reduce :: Comp -> Comp
reduce c = evalState (reduceR c) initialInstId

-- testing
tpure :: ValTy -> CompTy
tpure t = TAnnot t emptyEffs

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

    CEff "Flip",
    COp "flip" "Flip" "Unit" "Bool",

    CEff "State",
    COp "get" "State" "Unit" "Bool",
    COp "put" "State" "Bool" "Unit",

    CEff "Heap",
    COp "ref" "Heap" "Bool" (TInst (TVar $ Bound 0) "State")
  ]

eid :: Val
eid = AbsT "t" kType $ Return $ Abs "x" "t" "x"

flipH :: Val -> Comp -> Comp
flipH i c = Handle c $
  HOp i "flip" "x" "k" (App "k" "True") $
  HReturn "x" "x"

stateH :: Val -> Comp -> Comp
stateH i c = Handle c $
  HOp i "get" "x" "k" (Return $ Abs "s" "Bool" $ Do "f" (App "k" "s") $ App "f" "s") $
  HOp i "put" "s" "k" (Return $ Abs "_" "Bool" $ Do "f" (App "k" "Unit") $ App "f" "s") $
  HReturn "x" (Return $ Abs "s" "Bool" "x")

stateF :: Val -> Val -> Comp -> Comp
stateF i v c = Do "f" (stateH i c) $ App "f" v

heapH :: ValTy -> Val -> Comp -> Comp
heapH h i c = Handle c $
  HOp i "ref" "v" "kh" (
    Do "r" (New h "State") $
    stateF "r" "v" (App "kh" "r")
  ) $
  HReturn "x" "x"

term :: Comp
term =
  Fresh "n" $
  Do "r1" (New "n" "State") $
  stateF "r1" "True" $
  Do "r2" (New "n" "State") $
  Do "_" (Op "r2" "get" "Unit") $
  Op "r1" "get" "Unit"

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
