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
  show (TInst a n) = "(Inst " ++ (show a) ++ " " ++ (show n) ++ ")"

instance IsString ValTy where
  fromString = TVar . Free . Name

instance HasTVar ValTy where
  openTyR k u t@(TVar (Bound m)) = if m == k then u else t
  openTyR k u t@(TVar _) = t
  openTyR k u (TFun a b) = TFun (openTyR k u a) (openTyR k u b)
  openTyR k u (TForall n ki c) = TForall n ki $ openTyR (k + 1) u c
  openTyR k u (TInst a n) = TInst (openTyR k u a) n

  closeTyR k x t@(TVar (Bound m)) = t
  closeTyR k x t@(TVar (Free y)) = if x == y then TVar (Bound k) else t
  closeTyR k x (TFun a b) = TFun (closeTyR k x a) (closeTyR k x b)
  closeTyR k x (TForall n ki c) = TForall n ki $ closeTyR (k + 1) x c
  closeTyR k u (TInst a n) = TInst (closeTyR k u a) n

  isLocallyClosedTyR k (TVar (Bound m)) = m < k
  isLocallyClosedTyR k (TVar _) = True
  isLocallyClosedTyR k (TFun a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (TForall n ki c) = isLocallyClosedTyR (k + 1) c
  isLocallyClosedTyR k (TInst a e) = isLocallyClosedTyR k a

  freeTVars (TVar (Bound _)) = Set.empty
  freeTVars (TVar (Free x)) = Set.singleton x
  freeTVars (TFun a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (TForall n ki c) = freeTVars c
  freeTVars (TInst c e) = freeTVars c

instance NamelessTy ValTy where
  toNamelessTy t@(TVar _) = t
  toNamelessTy (TFun a b) = TFun (toNamelessTy a) (toNamelessTy b)
  toNamelessTy (TForall n k t) = TForall n k $ toNamelessTy (closeTy n t)
  toNamelessTy (TInst a n) = TInst (toNamelessTy a) n

  toNamedTy t@(TVar _) = t
  toNamedTy (TFun a b) = TFun (toNamedTy a) (toNamedTy b)
  toNamedTy (TForall n k t) = TForall n k (openTVar n $ toNamedTy t)
  toNamedTy (TInst a n) = TInst (toNamedTy a) n

-- computation types
data Eff = Eff Name ValTy
  deriving (Eq, Ord)

effHasLabel :: ValTy -> Eff -> Bool
effHasLabel l (Eff _ l') = l == l'

instance Show Eff where
  show (Eff e s) = (show e) ++ "@" ++ (show s)

instance HasTVar Eff where
  openTyR k u (Eff e s) = Eff e (openTyR k u s)

  closeTyR k u (Eff e s) = Eff e (closeTyR k u s)

  isLocallyClosedTyR k (Eff e s) = isLocallyClosedTyR k s
  
  freeTVars (Eff e s) = freeTVars s

instance NamelessTy Eff where
  toNamelessTy (Eff e s) = Eff e $ toNamelessTy s

  toNamedTy (Eff e s) = Eff e $ toNamedTy s

newtype Effs = Effs (Set Eff)
  deriving (Eq, Ord)

instance Show Effs where
  show (Effs r) = "{" ++ (intercalate ", " $ map show $ Set.elems r) ++ "}"

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

removeEffsWithLabel :: ValTy -> Effs -> Effs
removeEffsWithLabel l (Effs es) = Effs $ Set.filter (not . effHasLabel l) es

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

tpure :: ValTy -> CompTy
tpure t = TAnnot t emptyEffs

tfunP :: ValTy -> ValTy -> ValTy
tfunP a b = TFun a $ tpure b

tforallP :: Name -> Kind -> ValTy -> ValTy
tforallP x k t = TForall x k $ tpure t

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
  toNameless (Abs n t e) = Abs n (toNamelessTy t) (close n $ toNameless e)
  toNameless (AbsT n k e) = AbsT n k (closeTy n $ toNameless e)
  toNameless i@(Inst _) = i

  toNamed t@(Var _) = t
  toNamed (Abs n t e) = Abs n (toNamedTy t) (openVar n $ toNamed e)
  toNamed (AbsT n k e) = AbsT n k (openTVar n $ toNamed e)
  toNamed i@(Inst _) = i

-- computations
data Handler
  = HReturn Name Comp Name Comp
  | HOp Name Name Name Comp Handler
  deriving (Eq)

instance Show Handler where
  show (HReturn x c y c') = "return " ++ (show x) ++ " -> " ++ (show c) ++ "; " ++ "finally " ++ (show y) ++ " -> " ++ (show c')
  show (HOp o x k c r) = (show o) ++ " " ++ (show x) ++ " " ++ (show k) ++ " -> " ++ (show c) ++ ", " ++ (show r)

instance HasVar Handler where
  openR k u (HReturn x v y v') = HReturn x (openR (k + 1) u v) y (openR (k + 1) u v')
  openR k u (HOp o x k' c r) = HOp o x k' (openR (k + 2) u c) (openR k u r)

  closeR k u (HReturn x v y v') = HReturn x (closeR (k + 1) u v) y (closeR (k + 1) u v')
  closeR k u (HOp o x k' c r) = HOp o x k' (closeR (k + 2) u c) (closeR k u r)

  isLocallyClosedR k (HReturn x v y v') = isLocallyClosedR (k + 1) v && isLocallyClosedR (k + 1) v'
  isLocallyClosedR k (HOp o x k' c r) = isLocallyClosedR (k + 2) c && isLocallyClosedR k r

  freeVars (HReturn x v y v') = Set.union (freeVars v) (freeVars v')
  freeVars (HOp o x k c r) = Set.union (freeVars c) (freeVars r)

instance HasTVar Handler where
  openTyR k u (HReturn x v y v') = HReturn x (openTyR k u v) y (openTyR k u v')
  openTyR k u (HOp o x k' c r) = HOp o x k' (openTyR k u c) (openTyR k u r)

  closeTyR k u (HReturn x v y v') = HReturn x (closeTyR k u v) y (closeTyR k u v')
  closeTyR k u (HOp o x k' c r) = HOp o x k' (closeTyR k u c) (closeTyR k u r)

  isLocallyClosedTyR k (HReturn x v y v') = isLocallyClosedTyR k v && isLocallyClosedTyR k v'
  isLocallyClosedTyR k (HOp o x k' c r) = isLocallyClosedTyR k c && isLocallyClosedTyR k r

  freeTVars (HReturn x v y v') = Set.union (freeTVars v) (freeTVars v')
  freeTVars (HOp o x k' c r) = Set.union (freeTVars c) (freeTVars r)

instance Nameless Handler where
  toNameless (HReturn x v y v') = HReturn x (close x $ toNameless v) y (close y $ toNameless v')
  toNameless (HOp o x k c r) = HOp o x k (closeR 1 x $ close k $ toNameless c) (toNameless r)

  toNamed (HReturn x v y v') = HReturn x (toNamed $ openVar x v) y (toNamed $ openVar y v')
  toNamed (HOp o x k c r) = HOp o x k (openR 1 (Var $ Free x) $ openVar k $ toNamed c) (toNamed r)

opsFromHandler :: Handler -> [Name]
opsFromHandler (HReturn _ _ _ _) = []
opsFromHandler (HOp o _ _ _ r) = o : opsFromHandler r

opsFromHandlerSet :: Handler -> Set Name
opsFromHandlerSet = Set.fromList . opsFromHandler

findOpInHandler :: Name -> Handler -> Maybe (Name, Name, Comp)
findOpInHandler o (HReturn _ _ _ _) = Nothing
findOpInHandler o (HOp o' x k c _) | o == o' = Just (x, k, c)
findOpInHandler o (HOp _ _ _ _ r) = findOpInHandler o r

getReturnInHandler :: Handler -> (Name, Comp)
getReturnInHandler (HReturn x v _ _) = (x, v)
getReturnInHandler (HOp _ _ _ _ r) = getReturnInHandler r

getFinallyInHandler :: Handler -> (Name, Comp)
getFinallyInHandler (HReturn _ _ x v) = (x, v)
getFinallyInHandler (HOp _ _ _ _ r) = getFinallyInHandler r

data Comp
  = Return Val
  | App Val Val
  | AppT Val ValTy
  | Do Name Comp Comp
  | Op Val Name Val
  -- new E@s { h } as x in c
  | New Name ValTy Handler Name Comp
  -- handle(v)
  | Handle Val
  -- handle^s(c)
  | HandleS ValTy Comp
  -- handle^l{h}(c)
  | HandleI InstId Handler Comp
  deriving (Eq)

instance Show Comp where
  show (Return v) = "(return " ++ (show v) ++ ")"
  show (App a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (AppT a t) = "(" ++ (show a) ++ " [" ++ (show t) ++ "])"
  show (Do x a b) = "(" ++ (show x) ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"
  show (Op i o v) = (show i) ++ "#" ++ (show o) ++ "(" ++ (show v) ++ ")"
  show (New e s h x c) = "(new " ++ (show e) ++ "@" ++ (show s) ++ "{" ++ (show h) ++ "}" ++ " as " ++ (show x) ++ " in " ++ (show c) ++ ")"
  show (Handle v) = "handle(" ++ (show v) ++ ")"
  show (HandleS s v) = "handle^" ++ (show s) ++ "(" ++ (show v) ++ ")"
  show (HandleI l h v) = "handle^" ++ (show l) ++ "{" ++ (show h) ++ "}(" ++ (show v) ++ ")"
  
instance IsString Comp where
  fromString = Return . Var . Free . Name

instance HasVar Comp where
  openR k u (Return v) = Return (openR k u v)
  openR k u (App a b) = App (openR k u a) (openR k u b)
  openR k u (AppT a b) = AppT (openR k u a) b
  openR k u (Do n a b) = Do n (openR k u a) (openR (k + 1) u b)
  openR k u (Op i o b) = Op (openR k u i) o (openR k u b)
  openR k u (New e s h x c) = New e s (openR k u h) x (openR (k + 1) u c)
  openR k u (Handle v) = Handle (openR k u v)
  openR k u (HandleS s v) = HandleS s (openR k u v)
  openR k u (HandleI l h v) = HandleI l (openR k u h) (openR k u v)

  closeR k u (Return v) = Return (closeR k u v)
  closeR k u (App a b) = App (closeR k u a) (closeR k u b)
  closeR k u (AppT a b) = AppT (closeR k u a) b
  closeR k u (Do n a b) = Do n (closeR k u a) (closeR (k + 1) u b)
  closeR k u (Op i o b) = Op (closeR k u i) o (closeR k u b)
  closeR k u (New e s h x c) = New e s (closeR k u h) x (closeR (k + 1) u c)
  closeR k u (Handle v) = Handle (closeR k u v)
  closeR k u (HandleS s v) = HandleS s (closeR k u v)
  closeR k u (HandleI l h v) = HandleI l (closeR k u h) (closeR k u v)

  isLocallyClosedR k (Return v) = isLocallyClosedR k v
  isLocallyClosedR k (App a b) = isLocallyClosedR k a && isLocallyClosedR k b
  isLocallyClosedR k (AppT a b) = isLocallyClosedR k a
  isLocallyClosedR k (Do n a b) = isLocallyClosedR k a && isLocallyClosedR (k + 1) b
  isLocallyClosedR k (Op i o b) = isLocallyClosedR k i && isLocallyClosedR k b
  isLocallyClosedR k (New e s h x c) = isLocallyClosedR k h && isLocallyClosedR (k + 1) c
  isLocallyClosedR k (Handle v) = isLocallyClosedR k v
  isLocallyClosedR k (HandleS s v) = isLocallyClosedR k v
  isLocallyClosedR k (HandleI l h v) = isLocallyClosedR k h && isLocallyClosedR k v

  freeVars (Return v) = freeVars v
  freeVars (App a b) = Set.union (freeVars a) (freeVars b)
  freeVars (AppT a b) = freeVars a
  freeVars (Do n a b) = Set.union (freeVars a) (freeVars b)
  freeVars (Op i o a) = Set.union (freeVars i) (freeVars a)
  freeVars (New e s h x c) = Set.union (freeVars h) (freeVars c)
  freeVars (Handle v) = freeVars v
  freeVars (HandleS s v) = freeVars v
  freeVars (HandleI l h v) = Set.union (freeVars h) (freeVars v)

instance HasTVar Comp where
  openTyR k u (Return v) = Return (openTyR k u v)
  openTyR k u (App a b) = App (openTyR k u a) (openTyR k u b)
  openTyR k u (AppT a b) = AppT (openTyR k u a) (openTyR k u b)
  openTyR k u (Do n a b) = Do n (openTyR k u a) (openTyR k u b)
  openTyR k u (Op i o b) = Op (openTyR k u i) o (openTyR k u b)
  openTyR k u (New e s h x c) = New e (openTyR k u s) (openTyR k u h) x (openTyR k u c)
  openTyR k u (Handle a) = Handle (openTyR k u a)
  openTyR k u (HandleS s a) = HandleS (openTyR k u s) (openTyR k u a)
  openTyR k u (HandleI l s a) = HandleI l (openTyR k u s) (openTyR k u a)

  closeTyR k u (Return v) = Return (closeTyR k u v)
  closeTyR k u (App a b) = App (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (AppT a b) = AppT (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (Do n a b) = Do n (closeTyR k u a) (closeTyR k u b)
  closeTyR k u (Op i o b) = Op (closeTyR k u i) o (closeTyR k u b)
  closeTyR k u (New e s h x c) = New e (closeTyR k u s) (closeTyR k u h) x (closeTyR k u c)
  closeTyR k u (Handle a) = Handle (closeTyR k u a)
  closeTyR k u (HandleS s a) = HandleS (closeTyR k u s) (closeTyR k u a)
  closeTyR k u (HandleI l s a) = HandleI l (closeTyR k u s) (closeTyR k u a)

  isLocallyClosedTyR k (Return v) = isLocallyClosedTyR k v
  isLocallyClosedTyR k (App a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (AppT a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Do n a b) = isLocallyClosedTyR k a && isLocallyClosedTyR k b
  isLocallyClosedTyR k (Op i o v) = isLocallyClosedTyR k i && isLocallyClosedTyR k v
  isLocallyClosedTyR k (New e s h x c) = isLocallyClosedTyR k s && isLocallyClosedTyR k h && isLocallyClosedTyR k c
  isLocallyClosedTyR k (Handle a) = isLocallyClosedTyR k a
  isLocallyClosedTyR k (HandleS s a) = isLocallyClosedTyR k s && isLocallyClosedTyR k a
  isLocallyClosedTyR k (HandleI l s a) = isLocallyClosedTyR k s && isLocallyClosedTyR k a

  freeTVars (Return v) = freeTVars v
  freeTVars (App a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (AppT a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Do n a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Op i o v) = Set.union (freeTVars i) (freeTVars v)
  freeTVars (New e s h x c) = Set.union (freeTVars s) $ Set.union (freeTVars h) (freeTVars c)
  freeTVars (Handle a) = freeTVars a
  freeTVars (HandleS s a) = Set.union (freeTVars s) (freeTVars a)
  freeTVars (HandleI l s a) = Set.union (freeTVars s) (freeTVars a)

instance Nameless Comp where
  toNameless (Return e) = Return (toNameless e)
  toNameless (App a b) = App (toNameless a) (toNameless b)
  toNameless (AppT e t) = AppT (toNameless e) (toNamelessTy t)
  toNameless (Do n a b) = Do n (toNameless a) (close n $ toNameless b)
  toNameless (Op i o e) = Op (toNameless i) o (toNameless e)
  toNameless (New e s h x c) = New e (toNamelessTy s) (toNameless h) x (close x $ toNameless c)
  toNameless (Handle a) = Handle (toNameless a)
  toNameless (HandleS s a) = HandleS (toNamelessTy s) (toNameless a)
  toNameless (HandleI l s a) = HandleI l (toNameless s) (toNameless a)

  toNamed (Return e) = Return (toNamed e)
  toNamed (App a b) = App (toNamed a) (toNamed b)
  toNamed (AppT e t) = AppT (toNamed e) (toNamedTy t)
  toNamed (Do n a b) = Do n (toNamed a) (openVar n $ toNamed b)
  toNamed (Op i o e) = Op (toNamed i) o (toNamed e)
  toNamed (New e s h x c) = New e (toNamedTy s) (toNamed h) x (openVar x $ toNamed c)
  toNamed (Handle a) = Handle (toNamed a)
  toNamed (HandleS s a) = HandleS (toNamedTy s) (toNamed a)
  toNamed (HandleI l s a) = HandleI l (toNamed s) (toNamed a)

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

kLabel :: Kind
kLabel = "Label"

initialContext :: Context
initialContext = context
  [
    CKVar "Type",
    CKVar "Label"
  ]

-- util
checkKind :: Kind -> Kind -> String -> TC ()
checkKind k k' msg =
  if k == k' then
    return ()
  else
    err $ "kind mismatch: expected " ++ (show k) ++ " but got " ++ (show k') ++ " in " ++ msg
  
-- type equality
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

-- subtyping
subValTy :: ValTy -> ValTy -> String -> TC ()
subValTy (TVar v1) (TVar v2) msg | v1 == v2 = return ()
subValTy (TFun a1 b1) (TFun a2 b2) msg = do
  subValTy a2 a1 msg
  subCompTy b1 b2 msg
subValTy f1@(TForall n1 k1 t1) f2@(TForall n2 k2 t2) msg = do
  checkKind k1 k2 $ "kind mismatch in " ++ (show f1) ++ " <: " ++ (show f2) ++ " in " ++ msg
  let x = freshName (Set.union (freeTVars t1) (freeTVars t2)) n1
  subCompTy (openTVar x t1) (openTVar x t2) msg
subValTy (TInst a e) (TInst b e') msg | e == e' = subValTy a b msg
subValTy x y msg = err $ "subtyping failed: expected " ++ (show x) ++ " but got " ++ (show y) ++ " in " ++ msg

subCompTy :: CompTy -> CompTy -> String -> TC ()
subCompTy tr1@(TAnnot t1 r1) tr2@(TAnnot t2 r2) msg = do
  subValTy t1 t2 msg
  tcBool ("mismatched effects in subtyping " ++ (show tr1) ++ " and " ++ (show tr2) ++ " in " ++ msg) $ isSubsetOfEffs r1 r2

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
  checkKind kLabel k $ "instance type " ++ (show t)
  return kType

wfEff :: Context -> Eff -> TC ()
wfEff ctx (Eff e v) = do
  findEff ctx e
  k <- wfValTy ctx v
  checkKind kLabel k $ "instance type in annotation: " ++ (show v)

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
  let ctx' = add ctx (CTVar n kLabel)
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
    _ ->
      err $ "cannot type value: " ++ (show v)

typecheckInst :: Context -> Val -> TC (ValTy, Name)
typecheckInst ctx v = do
  t <- typecheckVal ctx v
  case t of
    TInst n e -> return (n, e)
    _ -> err $ "expected instance type but got " ++ (show t) ++ " in " ++ (show v)

typecheckLabel :: Context -> ValTy -> TC Name
typecheckLabel ctx t = do
  k <- wfValTy ctx t
  checkKind kLabel k $ "expected label but got " ++ (show t)
  case t of
    TVar (Free x) -> return x
    _ -> err $ "expected label but got " ++ (show t)

typecheckHandler :: Context -> ValTy -> ValTy -> Handler -> TC (CompTy, CompTy)
typecheckHandler ctx s t1 (HReturn xr cr xf cf) = do
  let xr' = freshVarInContext ctx cr xr
  TAnnot t2 r2 <- typecheckComp (add ctx $ CVar xr' t1) $ openVar xr' cr
  let xf' = freshVarInContext ctx cf xf
  --trace (show $ cf) $ return ()
  t3 <- typecheckComp (add ctx $ CVar xf' t2) $ openVar xf' cf
  return (TAnnot t2 r2, t3)
typecheckHandler ctx s t1 (HOp o x' k' c r) = do
  (e', a, b) <- findOp ctx o
  (TAnnot t2 r2, t3) <- typecheckHandler ctx s t1 r
  let x = freshVarInContext ctx c x'
  let k = freshVarInContext (add ctx $ CVar x t2) c k'
  TAnnot t2' r2' <- typecheckComp (adds ctx [CVar x (openTy s a), CVar k (TFun (openTy s b) (TAnnot t2 r2))]) $ openR 1 (Var $ Free x) $ openVar k c
  eqValTy t2 t2' $ "handler case: " ++ (show o)
  tcBool ("effect mismatch in handler case: " ++ (show o) ++ ", " ++ (show r2) ++ " and " ++ (show r2')) $ r2 == r2'
  return (TAnnot t2 r2, t3)

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
          --trace (show (l, tb)) $ return ()
          subValTy l tb $ "application " ++ (show c)
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
    Op i o v -> do
      (n, e) <- typecheckInst ctx i
      (e', a, b) <- findOp ctx o
      tcBool ("effect mismatch in operation call: " ++ (show c)) $ e == e'
      t <- typecheckVal ctx v
      subValTy (openTy n a) t $ "operation call " ++ (show c)
      return $ TAnnot (openTy n b) $ singletonEffs (Eff e n)
    Handle v -> do
      ta <- typecheckVal ctx v
      case ta of
        TForall n k (TAnnot t r) -> do
          checkKind kLabel k $ "handle: " ++ (show c)
          tcBool ((show n) ++ " escapes its scope in " ++ (show ta) ++ " in " ++ (show c)) $ isLocallyClosedTy t
          return $ TAnnot t (removeEffsWithLabel (TVar $ Bound 0) r)
        _ -> err $ "not a forall type in handle: " ++ (show ta) ++ " in " ++ (show c)
    New e s h x c' -> do
      findEff ctx e
      l <- typecheckLabel ctx s
      let os = ops ctx e
      tcBool ("ops do not match in " ++ (show c)) $ os == opsFromHandlerSet h
      let x' = freshVarInContext ctx c x
      TAnnot t1 r1 <- typecheckComp (add ctx $ CVar x' (TInst s e)) (openVar x' c')
      tra@(TAnnot t2 r2, TAnnot t3 r3) <- typecheckHandler ctx s t1 h
      let r3' = insertEffs (Eff e s) r3
      -- trace (show (r1, r3')) $ return ()
      -- tcBool ("not a subset in new: " ++ (show c) ++ ", " ++ (show r1) ++ " and " ++ (show r3')) $ isSubsetOfEffs r1 r3'
      return $ TAnnot t3 (unionEffs r3' r1)
    _ ->
      err $ "cannot type comp: " ++ (show c)

infer :: Context -> Comp -> TC CompTy
infer ctx e = do
  tcBool ("expression not locally closed: " ++ (show e)) $ isLocallyClosed e
  wfContext ctx
  t <- typecheckComp ctx e
  -- trace (show t) $ return ()
  k <- wfCompTy ctx t
  checkKind kType k $ "infer: " ++ (show t)
  return t

-- semantics
reduceR :: Comp -> State InstId Comp
reduceR co =
  case co of
    c@(Return _) -> return c
    c@(Op _ _ _) -> return c

    App (Abs x _ a) b -> reduceR $ open b a
    AppT (AbsT x _ a) t -> reduceR $ openTy t a

    Do x a b -> do
      c <- reduceR a
      case c of
        Return v -> reduceR $ open v b
        Do x' a' b' -> reduceR $ Do x' a' $ Do x b' b
        New e s h y c' -> return $ New e s h y (Do x c' b)
        a' -> return $ Do x a' b

    Handle (AbsT x _ a) -> reduceR $ HandleS (TVar $ Free x) (openTVar x a)

    HandleS s a -> do
      c <- reduceR a
      case c of
        Return v -> return c
        Op i o v -> return c
        Do x a' b -> return $ Do x a' (HandleS s b)
        New e s' h x c' ->
          if s == s' then do
            let (xf, cf) = getFinallyInHandler h
            i <- get
            put (nextInstId i)
            reduceR $ HandleS s (Do xf (HandleI i h (open (Inst i) c')) cf)
          else
            return $ New e s' h x (HandleS s c')

    HandleI i h a -> do
      c <- reduceR a
      case c of
        New e s h' x c' -> reduceR $ New e s h' x (HandleI i h c')
        Return v -> do
          let (xr, cr) = getReturnInHandler h
          reduceR $ open v cr
        Op i' o v -> reduceR $ HandleI i h (Do "x" c (Return $ Var $ Bound 0))
        Do x (Op (Inst i') o v) c' ->
          if i == i' then
            case findOpInHandler o h of
              Just (x', _, b) ->
                reduceR $ openR 1 v $ open (Abs x' "_" $ HandleI i h c') b
          else
            return $ Do x (Op (Inst i') o v) (HandleI i h c')

    c -> return c

reduce :: Comp -> Comp
reduce c = evalState (reduceR c) initialInstId

-- testing
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

eid = AbsT "t" kType $ Return $ Abs "x" "t" "x"

newFlip s x b c =
  New "Flip" s (
    HOp "flip" "x" "k" (App "k" b) $
    HReturn "x" "x"
    {- finally -}  "y" "y"
  ) x c

newState s x v c =
  New "State" s (
    HOp "get" "_" "k" (Return $ Abs "st" "Bool" $ Do "f" (App "k" "st") $ App "f" "st") $
    HOp "put" "st'" "k" (Return $ Abs "st" "Bool" $ Do "f" (App "k" "Unit") $ App "f" "st'") $
    HReturn "x" (Return $ Abs "st" "Bool" "x")
    {- finally -}  "y" (App "y" v)
  ) x c

newStateBroken s x v c =
  New "State" s (
    HOp "get" "_" "k" (Return $ Abs "st" "Bool" $ newState s x v $ Op (Var $ Free x) "get" "Unit") $
    HOp "put" "st'" "k" (Return $ Abs "st" "Bool" $ newState s x v $ Op (Var $ Free x) "get" "Unit") $
    HReturn "x" (Return $ Abs "st" "Bool" $ newState s x v $ Op (Var $ Free x) "get" "Unit")
    {- finally -}  "y" (App "y" v)
  ) x c

term :: Comp
term =
  Handle $
    AbsT "s" "Label" $
      newFlip "s" "f" "True" $
      newState "s" "r" "False" $
      Do "_" (Op "r" "put" "True") $
      newStateBroken "s" "r2" "False" $
      Do "b" (Op "f" "flip" "Unit") $
      Do "_" (Op "r2" "put" "b") $
      Op "r2" "get" "Unit"

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
