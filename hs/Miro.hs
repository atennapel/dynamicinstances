{-# LANGUAGE OverloadedStrings #-}
import GHC.Exts (IsString(..))

import qualified Data.Set as Set
import qualified Data.List as List

import Debug.Trace (trace, traceShow, traceShowId)

-- Effects
type Eff = String
type Op = String

-- AST
type SVar = String
type SLoc = Int

data Scope = SVar SVar | SLoc SLoc
  deriving (Eq, Ord)

instance IsString Scope where
  fromString = SVar

instance Show Scope where
  show (SVar s) = s
  show (SLoc l) = "'" ++ (show l)

type TCon = String

data Type
  = TCon TCon
  | TInst Scope Eff
  | TFun Type CType
  | TForall SVar CType
  | TPair Type Type
  deriving (Eq)

instance IsString Type where
  fromString = TCon

instance Show Type where
  show (TCon x) = x
  show (TInst s e) = "Inst " ++ (show s) ++ " " ++ e
  show (TFun a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"
  show (TForall x b) = "(forall " ++ x ++ ". " ++ (show b) ++ ")"
  show (TPair a b) = "(" ++ (show a) ++ ", " ++ (show b) ++ ")"

type Ann = Set.Set Scope

showAnn :: Ann -> String
showAnn r = "{" ++ (List.intercalate ", " (map show $ Set.toList r)) ++ "}"

data CType = CType Type Ann
  deriving (Eq)

purety :: Type -> CType
purety t = CType t Set.empty

instance IsString CType where
  fromString x = purety (TCon x)

instance Show CType where
  show (CType t r) = show t ++ (if Set.null r then "" else "!" ++ (showAnn r))

substScope :: SVar -> Scope -> Scope -> Scope
substScope x s (SVar x') | x == x' = s
substScope _ _ s = s

substScopeType :: SVar -> Scope -> Type -> Type
substScopeType x s (TInst s' e) = TInst (substScope x s s') e
substScopeType x s (TFun a b) = TFun (substScopeType x s a) (substScopeCType x s b)
substScopeType x s (TForall x' b) | x /= x' = TForall x' (substScopeCType x s b)
substScopeType x s (TPair a b) = TPair (substScopeType x s a) (substScopeType x s b)
substScopeType _ _ t = t

substScopeCType :: SVar -> Scope -> CType -> CType
substScopeCType x s (CType t a) = CType (substScopeType x s t) (Set.map (substScope x s) a)

containsScopeType :: Scope -> Type -> Bool
containsScopeType s (TInst s' _) = s == s'
containsScopeType s (TFun a b) = containsScopeType s a || containsScopeCType s b
containsScopeType s (TForall s' t) | s /= SVar s' = containsScopeCType s t
containsScopeType s (TPair a b) = containsScopeType s a || containsScopeType s b
containsScopeType _ _ = False

containsScopeCType :: Scope -> CType -> Bool
containsScopeCType s (CType t a) = Set.member s a || containsScopeType s t

type Var = String

type Loc = Int

data Val
  = Var Var
  | Inst Loc
  | Abs Var Comp
  | SAbs SVar Comp
  | VAnn Val Type
  | Pair Val Val
  deriving (Eq)

instance IsString Val where
  fromString = Var

instance Show Val where
  show (Var x) = x
  show (Inst l) = "inst($" ++ (show l) ++ ")"
  show (Abs x b) = "(\\" ++ x ++ " -> " ++ (show b) ++ ")"
  show (SAbs x b) = "(/\\" ++ x ++ " -> " ++ (show b) ++ ")"
  show (VAnn v t) = "(" ++ (show v) ++ " : " ++ (show t) ++ ")"
  show (Pair a b) = "(" ++ (show a) ++ ", " ++ (show b) ++ ")"

data Comp
  = Return Val
  | App Val Val
  | Seq Var Comp Comp
  | OpCall Val Op Val
  | SApp Val Scope
  | New Eff Scope Handler Finally Var Comp
  | Runscope SVar Comp
  | RunscopeLoc SLoc (Set.Set Loc) Comp
  | Runinst Loc SLoc Eff Handler Comp
  | CAnn Comp CType
  deriving (Eq)

instance IsString Comp where
  fromString x = Return (Var x)

instance Show Comp where
  show (Return v) = "return " ++ (show v)
  show (App a b) = (show a) ++ " " ++ (show b)
  show (Seq x a b) = "(" ++ x ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"
  show (OpCall v1 op v2) = (show v1) ++ "#" ++ op ++ "(" ++ (show v2) ++ ")"
  show (SApp a b) = (show a) ++ " [" ++ (show b) ++ "]"
  show (New e s h f x c) = "new " ++ e ++ "@" ++ (show s) ++ " {" {-++ (show h) ++ "; " ++ (show f) ++-}++"..."++ "} as " ++ x ++ " in " ++ (show c)
  show (Runscope s c) = "runscope(" ++ s ++ " -> " ++ (show c) ++ ")"
  show (RunscopeLoc s ls c) = "runscope'" ++ (show s) ++ "[" ++ (List.intercalate ", " $ map show $ Set.toList ls) ++ "](" ++ (show c) ++ ")"
  show (Runinst l sl e h c) = "runinst$" ++ (show l) ++ "['" ++ (show sl) ++ "," ++ e ++ "]{" {-++ (show h) ++-}++"..."++ "}(" ++ (show c) ++ ")"
  show (CAnn c t) = "(" ++ (show c) ++ " : " ++ (show t) ++ ")"

data Finally = Finally Var Comp
  deriving (Eq)

instance Show Finally where
  show (Finally x c) = "finally " ++ x ++ " -> " ++ (show c)

data Handler
  = HOp Op Var Var Comp Handler
  | HReturn Var Comp
  deriving (Eq)

instance Show Handler where
  show (HOp op x k c h) = op ++ " " ++ x ++ " " ++ k ++ " -> " ++ (show c) ++ "; " ++ (show h)
  show (HReturn x c) = "return " ++ x ++ " -> " ++ (show c)

substVarVal :: Var -> Val -> Val -> Val
substVarVal x s v@(Var y) = if x == y then s else v
substVarVal x s v@(Abs y b) = if x == y then v else Abs y (substVarComp x s b)
substVarVal x s (SAbs y b) = SAbs y (substVarComp x s b)
substVarVal x s (VAnn v y) = VAnn (substVarVal x s v) y
substVarVal x s (Pair a b) = Pair (substVarVal x s a) (substVarVal x s b)
substVarVal _ _ v = v

substVarComp :: Var -> Val -> Comp -> Comp
substVarComp x s (Return v) = Return (substVarVal x s v)
substVarComp x s (App a b) = App (substVarVal x s a) (substVarVal x s b)
substVarComp x s (Seq y a b) = Seq y (substVarComp x s a) (if x == y then b else substVarComp x s b)
substVarComp x s (OpCall v1 op v2) = OpCall (substVarVal x s v1) op (substVarVal x s v2)
substVarComp x s (SApp v y) = SApp (substVarVal x s v) y
substVarComp x s (New s' e h (Finally y c') z c) =
  New s' e (substVarHandler x s h) (Finally y (if x == y then c' else substVarComp x s c')) z (if x == z then c else substVarComp x s c) 
substVarComp x s (Runscope l c) = Runscope l (substVarComp x s c)
substVarComp x s (RunscopeLoc l ls c) = RunscopeLoc l ls (substVarComp x s c)
substVarComp x s (Runinst l sl e h c) = Runinst l sl e (substVarHandler x s h) (substVarComp x s c)
substVarComp x s (CAnn c t) = CAnn (substVarComp x s c) t

substVarHandler :: Var -> Val -> Handler -> Handler
substVarHandler x s (HOp op y k c h) = HOp op y k (if x == y || x == k then c else substVarComp x s c) (substVarHandler x s h)
substVarHandler x s h@(HReturn y c) = if x == y then h else HReturn y (substVarComp x s c)

substScopeVal :: SVar -> Scope -> Val -> Val
substScopeVal x s (Abs y b) = Abs y (substScopeComp x s b)
substScopeVal x s v@(SAbs y b) = if x == y then v else SAbs y (substScopeComp x s b)
substScopeVal x s (VAnn v y) = VAnn (substScopeVal x s v) (substScopeType x s y)
substScopeVal x s (Pair a b) = Pair (substScopeVal x s a) (substScopeVal x s b)
substScopeVal _ _ v = v

substScopeComp :: SVar -> Scope -> Comp -> Comp
substScopeComp x s (Return v) = Return (substScopeVal x s v)
substScopeComp x s (App a b) = App (substScopeVal x s a) (substScopeVal x s b)
substScopeComp x s (Seq y a b) = Seq y (substScopeComp x s a) (substScopeComp x s b)
substScopeComp x s (OpCall v1 op v2) = OpCall (substScopeVal x s v1) op (substScopeVal x s v2)
substScopeComp x s (SApp v y) = SApp (substScopeVal x s v) (substScope x s y)
substScopeComp x s (New e s' h (Finally y c') z c) =
  New e (substScope x s s') (substScopeHandler x s h) (Finally y (substScopeComp x s c')) z (substScopeComp x s c) 
substScopeComp x s v@(Runscope l c) = if x == l then v else Runscope l (substScopeComp x s c)
substScopeComp x s (RunscopeLoc l ls c) = RunscopeLoc l ls (substScopeComp x s c)
substScopeComp x s (Runinst l sl e h c) = Runinst l sl e (substScopeHandler x s h) (substScopeComp x s c)
substScopeComp x s (CAnn c t) = CAnn (substScopeComp x s c) (substScopeCType x s t)

substScopeHandler :: SVar -> Scope -> Handler -> Handler
substScopeHandler x s (HOp op y k c h) = HOp op y k (substScopeComp x s c) (substScopeHandler x s h)
substScopeHandler x s (HReturn y c) = HReturn y (substScopeComp x s c)

freshVar2 :: Var -> Val -> Val -> Var
freshVar2 x a b = go x (Set.union (varsVal a) (varsVal b))
  where
    go x' s | Set.member x' s = go (x' ++ "'") s
    go x' _ = x'

varsVal :: Val -> Set.Set Var
varsVal (Var x) = Set.singleton x
varsVal (Abs x b) = Set.union (Set.singleton x) (varsComp b)
varsVal (SAbs _ b) = varsComp b
varsVal (VAnn v _) = varsVal v
varsVal (Pair a b) = Set.union (varsVal a) (varsVal b)
varsVal _ = Set.empty

varsComp :: Comp -> Set.Set Var
varsComp (Return v) = varsVal v
varsComp (App a b) = Set.union (varsVal a) (varsVal b)
varsComp (Seq x a b) = Set.union (Set.singleton x) (Set.union (varsComp a) (varsComp b))
varsComp (OpCall v1 _ v2) = Set.union (varsVal v1) (varsVal v2)
varsComp (SApp v _) = varsVal v
varsComp (New _ _ h (Finally y c') x c) =
  Set.unions [varsHandler h, Set.singleton y, varsComp c', Set.singleton x, varsComp c]
varsComp (Runscope _ c) = varsComp c
varsComp (RunscopeLoc _ _ c) = varsComp c
varsComp (Runinst _ _ _ h c) = Set.union (varsHandler h) (varsComp c)
varsComp (CAnn c _) = varsComp c

varsHandler :: Handler -> Set.Set Var
varsHandler (HOp _ x k c h) =
  Set.unions [Set.fromList [x, k], varsComp c, varsHandler h]
varsHandler (HReturn x c) = Set.union (Set.singleton x) (varsComp c)

removeAnnotsVal :: Val -> Val
removeAnnotsVal (Abs x b) = Abs x (removeAnnotsComp b)
removeAnnotsVal (SAbs x b) = SAbs x (removeAnnotsComp b)
removeAnnotsVal (VAnn v _) = removeAnnotsVal v
removeAnnotsVal (Pair a b) = Pair (removeAnnotsVal a) (removeAnnotsVal b)
removeAnnotsVal v = v

removeAnnotsComp :: Comp -> Comp
removeAnnotsComp (Return v) = Return (removeAnnotsVal v)
removeAnnotsComp (App a b) = App (removeAnnotsVal a) (removeAnnotsVal b)
removeAnnotsComp (Seq x a b) = Seq x (removeAnnotsComp a) (removeAnnotsComp b)
removeAnnotsComp (OpCall v1 op v2) = OpCall (removeAnnotsVal v1) op (removeAnnotsVal v2)
removeAnnotsComp (SApp v s) = SApp (removeAnnotsVal v) s
removeAnnotsComp (New e s h (Finally y c') x c) =
  New e s (removeAnnotsHandler h) (Finally y (removeAnnotsComp c')) x (removeAnnotsComp c)
removeAnnotsComp (Runscope x c) = Runscope x (removeAnnotsComp c)
removeAnnotsComp (RunscopeLoc x ls c) = RunscopeLoc x ls (removeAnnotsComp c)
removeAnnotsComp (Runinst l sl e h c) = Runinst l sl e (removeAnnotsHandler h) (removeAnnotsComp c)
removeAnnotsComp (CAnn c _) = removeAnnotsComp c

removeAnnotsHandler :: Handler -> Handler
removeAnnotsHandler (HOp op x k c h) =
  HOp op x k (removeAnnotsComp c) (removeAnnotsHandler h)
removeAnnotsHandler (HReturn x c) = HReturn x (removeAnnotsComp c)

-- environments
data Gamma = GEmpty | GVar Gamma Var Type
  deriving (Show)
data Delta = DEmpty | DSVar Delta SVar | DSLoc Delta SLoc | DLoc Delta Loc SLoc Eff
  deriving (Show)
data Sigma = SgEmpty | SgSLoc Sigma SLoc | SgLoc Sigma Loc
  deriving (Show)

sigmaMaxSLoc :: Sigma -> Int
sigmaMaxSLoc (SgSLoc r l) = max (sigmaMaxSLoc r) l
sigmaMaxSLoc (SgLoc r _) = sigmaMaxSLoc r
sigmaMaxSLoc _ = -1

sigmaMaxLoc :: Sigma -> Int
sigmaMaxLoc (SgLoc r l) = max (sigmaMaxLoc r) l
sigmaMaxLoc (SgSLoc r _) = sigmaMaxLoc r
sigmaMaxLoc _ = -1

freshSLoc :: Sigma -> SLoc
freshSLoc s = (sigmaMaxSLoc s) + 1

freshLoc :: Sigma -> Loc
freshLoc s = (sigmaMaxLoc s) + 1

freshLocIn :: Loc -> Set.Set Loc -> Loc
freshLocIn l s = if Set.member l s then freshLocIn (l + 1) s else l

-- judgments
type Err t = Either String t

check :: Bool -> String -> Err ()
check True _ = return ()
check False msg = Left msg

fails :: Err t -> String -> Err ()
fails (Left _) _ = return () 
fails (Right _) msg = Left msg

sub :: Type -> Type -> Err ()
sub (TCon x) (TCon y) | x == y = return ()
-- Sub-Inst
sub (TInst s1 e1) (TInst s2 e2) | s1 == s2 && e1 == e2 = return ()
-- Sub-Arr
sub (TFun a1 b1) (TFun a2 b2) = do
  sub a2 a1
  subComp b1 b2
-- Sub-Forall
sub (TForall _ t1) (TForall _ t2) = subComp t1 t2
sub (TPair a1 b1) (TPair a2 b2) = do
  sub a1 a2
  sub b1 b2
sub a b = Left $ "subtyping failed: " ++ (show a) ++ " <: " ++ (show b)

subComp :: CType -> CType -> Err ()
-- Sub-Annot
subComp a@(CType t1 r1) b@(CType t2 r2) = do
  sub t1 t2
  check (Set.isSubsetOf r1 r2) $ "subtyping failed: " ++ (show a) ++ " <: " ++ (show b)

deltaScope :: Delta -> Scope -> Err ()
deltaScope DEmpty s = Left $ "undefined " ++ (show s)
deltaScope (DSVar _ x) (SVar y) | x == y = return ()
deltaScope (DSVar r _) s = deltaScope r s
deltaScope (DSLoc _ x) (SLoc y) | x == y = return ()
deltaScope (DSLoc r _) s = deltaScope r s
deltaScope (DLoc r _ _ _) s = deltaScope r s

deltaLoc :: Delta -> Loc -> Err (SLoc, Eff)
deltaLoc DEmpty l = Left $ "undefined loc " ++ (show l)
deltaLoc (DSVar r _) l = deltaLoc r l
deltaLoc (DSLoc r _) l = deltaLoc r l
deltaLoc (DLoc _ x s e) y | x == y = return (s, e)
deltaLoc (DLoc r _ _ _) l = deltaLoc r l 

wfDelta :: Delta -> Err ()
-- WFD-Empty
wfDelta DEmpty = return ()
-- WFD-ScopeVar
wfDelta (DSVar r s) = do
  wfDelta r
  fails (deltaScope r (SVar s)) $ "duplicate svar " ++ (show s)
-- WFD-ScopeLoc
wfDelta (DSLoc r s) = do
  wfDelta r
  fails (deltaScope r (SLoc s)) $ "duplicate sloc " ++ (show s)
-- WFD-InstanceLoc
wfDelta (DLoc r l s _) = do
  wfDelta r
  fails (deltaLoc r l) $ "duplicate loc " ++ (show l)
  deltaScope r (SLoc s)

wfScope :: Delta -> Scope -> Err ()
-- WF-SVar
wfScope d sv@(SVar _) = do
  wfDelta d
  deltaScope d sv
-- WF-SLoc
wfScope d sl@(SLoc _) = do
  wfDelta d
  deltaScope d sl

wfType :: Delta -> Type -> Err ()
wfType _ (TCon _) = return ()
-- WF-Inst
wfType d (TInst s _) = wfScope d s
-- WF-Arr
wfType d (TFun a b) = do
  wfType d a
  wfCType d b
-- WF-Forall
wfType d (TForall s t) = wfCType (DSVar d s) t
wfType d (TPair a b) = do
  wfType d a
  wfType d b

wfCType :: Delta -> CType -> Err ()
-- WF-Annot
wfCType d (CType t r) = do
  wfType d t
  mapM_ (wfScope d) (Set.elems r)

-- typing rules
gammaLookup :: Gamma -> Var -> Err Type
gammaLookup GEmpty x = Left $ "undefined var " ++ (show x)
gammaLookup (GVar _ x t) y | x == y = return t
gammaLookup (GVar g _ _) x = gammaLookup g x

tcVal :: Delta -> Gamma -> Val -> Err Type
-- T-Var
tcVal d g (Var x) = do
  wfDelta d
  gammaLookup g x
-- T-Inst
tcVal d _ (Inst l) = do
  wfDelta d
  (sloc, eff) <- deltaLoc d l
  return $ TInst (SLoc sloc) eff
-- T-Abs
tcVal d g (SAbs s c) = do
  t <- tcComp (DSVar d s) g c
  return $ TForall s t
-- T-SubVal
tcVal d g (VAnn v t) = do
  wfType d t
  checkVal d g v t
  return t
tcVal d g (Pair a b) = do
  t1 <- tcVal d g a
  t2 <- tcVal d g b
  return $ TPair t1 t2
tcVal _ _ v = Left $ "cannot synth " ++ (show v)

checkVal :: Delta -> Gamma -> Val -> Type -> Err ()
checkVal d g (Abs x c) (TFun a b) = checkComp d (GVar g x a) c b
checkVal d g (SAbs s c) (TForall s' t) | s == s' = checkComp (DSVar d s) g c t
checkVal d g (Pair a b) (TPair ta tb) = do
  checkVal d g a ta
  checkVal d g b tb
checkVal d g v t = do
  t' <- tcVal d g v
  sub t' t

tcComp :: Delta -> Gamma -> Comp -> Err CType
-- T-Return
tcComp d g (Return v) = do
  t <- tcVal d g v
  return $ CType t Set.empty
-- T-App
tcComp d g v@(App v1 v2) = do
  t <- tcVal d g v1
  case t of
    TFun a b -> do
      checkVal d g v2 a
      return b
    _ -> Left $ "expected function but got " ++ (show t) ++ " in " ++ (show v)
-- T-SApp
tcComp d g v@(SApp v1 s) = do
  wfScope d s
  t <- tcVal d g v1
  case t of
    TForall x b -> return $ substScopeCType x s b
    _ -> Left $ "expected forall but got " ++ (show t) ++ " in " ++ (show v)
-- T-Seq
tcComp d g (Seq x a b) = do
  CType t r <- tcComp d g a
  CType t' r' <- tcComp d (GVar g x t) b
  return $ CType t' (Set.union r r')
-- T-Op
tcComp d g v@(OpCall v1 op v2) = do
  t <- tcVal d g v1
  case t of
    TInst s e -> do
      checkOp e op
      (t1, t2) <- opTypes op
      checkVal d g v2 t1
      return $ CType t2 (Set.singleton s)
    _ -> Left $ "expected instance but got " ++ (show t) ++ " in " ++ (show v)
-- T-New
tcComp d g (New e s h (Finally y c') x c) = do
  wfScope d s
  CType t1 r1 <- tcComp d (GVar g x (TInst s e)) c
  CType t2 r2 <- tcHandler d g t1 h
  check (Set.isSubsetOf r2 r1) $ "cannot have extra effects in handler"
  checkComp d (GVar g y t2) c' (CType t1 r1)
  return $ CType t1 (Set.unions [r1, Set.singleton s])
-- T-Handle
tcComp d g (Runscope s c) = do
  CType t r <- tcComp (DSVar d s) g c
  check (not $ containsScopeType (SVar s) t) $ "scope " ++ (show s) ++ " escaping " ++ (show t)
  return $ CType t (Set.delete (SVar s) r)
-- T-HandleScope
tcComp d g (RunscopeLoc s _ c) = do
  fails (deltaScope d (SLoc s)) $ "duplicate SLoc " ++ (show s)
  CType t r <- tcComp (DSLoc d s) g c
  check (not $ containsScopeType (SLoc s) t) $ "scope " ++ (show s) ++ " escaping " ++ (show t)
  return $ CType t (Set.delete (SLoc s) r)
-- T-HandleInst
tcComp d g (Runinst l s e h c) = do
  wfScope d (SLoc s)
  fails (deltaLoc d l) $ "duplicate Loc " ++ (show l)
  CType t1 r1 <- tcComp (DLoc d l s e) g c
  CType t2 r2 <- tcHandler d g t1 h
  return $ CType t2 (Set.union r1 r2)
-- T-SubComp
tcComp d g (CAnn c t) = do
  wfCType d t
  checkComp d g c t
  return t

checkComp :: Delta -> Gamma -> Comp -> CType -> Err ()
checkComp d g (Return v) (CType t _) = checkVal d g v t
checkComp d g c t = do
  t' <- tcComp d g c
  subComp t' t

tcHandler :: Delta -> Gamma -> Type -> Handler -> Err CType
-- T-HandlerOp
tcHandler d g t1 (HOp op x k c h) = do
  (tpar, tret) <- opTypes op
  tr <- tcHandler d g t1 h
  checkComp d (GVar (GVar g x tpar) k (TFun tret tr)) c tr
  return $ tr
-- T-HandlerReturn
tcHandler d g t1 (HReturn x c) = tcComp d (GVar g x t1) c

-- semantics
findOp :: Op -> Handler -> Maybe (Var, Var, Comp)
findOp op (HOp op' x k c _) | op == op' = return (x, k, c)
findOp op (HOp _ _ _ _ h) = findOp op h
findOp _ (HReturn _ _) = Nothing

findReturn :: Handler -> (Var, Comp)
findReturn (HOp _ _ _ _ h) = findReturn h
findReturn (HReturn x c) = (x, c)

step :: Sigma -> Comp -> Maybe Comp
-- S-App
step _ (App (Abs x c) v) = return $ substVarComp x v c
-- S-SApp
step _ (SApp (SAbs s c) s') = return $ substScopeComp s s' c
-- S-SeqReturn
step _ (Seq x (Return v) c) = return $ substVarComp x v c
-- S-Flatten
step _ (Seq y (Seq x c1 c2) c3) = return $ Seq x c1 (Seq y c2 c3)
-- S-LiftNew
step _ (Seq x (New e s h f y c1) c2) = return $ New e s h f y (Seq x c1 c2)
-- S-Seq
step s (Seq x c1 c2) = do
  c1' <- step s c1
  return $ Seq x c1' c2
-- S-RunScope
step s (Runscope sv c) =
  let sl = freshSLoc s in
  return $ RunscopeLoc sl Set.empty (substScopeComp sv (SLoc sl) c)
-- S-RunScopeReturn
step _ (RunscopeLoc _ _ (Return v)) = return $ Return v
-- S-RunScopeOp
step _ (RunscopeLoc _ _ (OpCall v1 op v2)) = return $ OpCall v1 op v2
-- S-RunScopeSeqOp
step _ (RunscopeLoc sl ls (Seq x (OpCall v1 op v2) c)) =
  return $ Seq x (OpCall v1 op v2) (RunscopeLoc sl ls c)
-- S-RunScopeNew
step s (RunscopeLoc sl ls (New e sl' h (Finally y c') x c)) | (SLoc sl) == sl' =
  let l = freshLocIn (freshLoc s) ls in
  return $ RunscopeLoc sl (Set.insert l ls) (Seq y (Runinst l sl e h (substVarComp x (Inst l) c)) c')
-- S-RunScopeNewSkip
step _ (RunscopeLoc sl ls (New e sl' h f x c)) =
  return $ New e sl' h f x (RunscopeLoc sl ls c)
-- S-RunScopeCong
step s (RunscopeLoc sl ls c) = do
  c' <- step (SgSLoc s sl) c
  return $ RunscopeLoc sl ls c'
-- S-RunInstNew
step _ (Runinst l sl e h (New e' s h' f x c)) =
  return $ New e' s h' f x (Runinst l sl e h c)
-- S-RunInstOpPrepare
step _ (Runinst l sl e h (OpCall v1 op v2)) =
  let x = freshVar2 "x" v1 v2 in
  return $ Runinst l sl e h (Seq x (OpCall v1 op v2) (Return (Var x)))
-- S-RunInstOp
step _ (Runinst l sl e h (Seq y (OpCall (Inst l') op v) c)) | l == l' = do
  (x, k, cop) <- findOp op h
  return $ substVarComp x v (substVarComp k (Abs y $ Runinst l sl e h c) cop)
-- S-RunInstOpSkip
step _ (Runinst l sl e h (Seq x (OpCall (Inst l') op v) c)) =
  return $ Seq x (OpCall (Inst l') op v) (Runinst l sl e h c)
-- S-RunInstReturn
step _ (Runinst _ _ _ h (Return v)) =
  let (x, c) = findReturn h in
  return $ substVarComp x v c
-- S-RunInstCong
step s (Runinst l sl e h c) = do
  c' <- step (SgLoc s l) c
  return $ Runinst l sl e h c'
step _ _ = Nothing

steps :: Comp -> Comp
steps c =
  case step SgEmpty c of
    Just c' -> steps c'
    Nothing -> c

stepsShow :: Comp -> IO ()
stepsShow c = do
  putStrLn $ show c
  case step SgEmpty c of
    Just c' -> stepsShow c'
    Nothing -> return ()

-- testing
tUnit :: Type
tUnit = TCon "Unit"

tBool :: Type
tBool = TCon "Bool"

tInt :: Type
tInt = TCon "Int"

checkOp :: Eff -> Op -> Err ()
checkOp "Flip" "flip" = return ()
checkOp "State" "get" = return ()
checkOp "State" "put" = return ()
checkOp e o = Left $ "undefined eff or op: " ++ (show (e, o))

opTypes :: Op -> Err (Type, Type)
opTypes "flip" = return (tUnit, tBool)
opTypes "get" = return (tUnit, tInt)
opTypes "put" = return (tInt, tUnit)
opTypes o = Left $ "undefined op " ++ o

delta :: Delta
delta = DEmpty

gamma :: Gamma
gamma = GVar (GVar (GVar (GVar (GVar (GVar GEmpty "False" tBool) "two" tInt) "one" tInt) "zero" tInt) "Unit" tUnit) "True" tBool

refh :: CType -> Handler
refh t =
  HOp "get" "x" "k" (Return $ Abs "s" $ Seq "f" (App "k" "s") (App "f" "s")) $
  HOp "put" "x" "k" (Return $ Abs "s" $ Seq "f" (App "k" "Unit") (App "f" "x")) $
  HReturn "x" (Return $ VAnn (Abs "s" "x") (TFun "Int" t))

ref :: Scope -> Var -> Val -> CType -> Comp -> Comp
ref s x v t c =
  New "State" s (refh t) (Finally "f" $ App "f" v) x c

fliph :: Handler
fliph =
  HOp "flip" "x" "k" (App "k" "True") $
  HReturn "x" "x"

newflip :: Scope -> Var -> Comp -> Comp
newflip s x c =
  New "Flip" s fliph (Finally "x" "x") x c

{-
runscope(s ->
  ff <- new State@s {
    get x k -> \s -> k s s
    put x k -> \s -> k () x
    return x -> \s -> x
    finally f -> f
  } as r in r);
  rr <- ff 0;
  rr#get ()
-}
term :: Comp
term =
  Runscope "s1" $
  Seq "r1" (ref "s1" "rx1" "zero" (purety $ TInst "s1" "State") "rx1") $
  Runscope "s2" $
  Seq "r2" (ref "s2" "rx2" "zero" (purety $ TInst "s2" "State") "rx2") $
  Seq "r3" (ref "s2" "rx3" "two" (purety $ TInst "s2" "State") (Seq "_" (OpCall "r1" "put" "one") "rx3")) $
  Seq "f1" (newflip "s1" "f1" "f1") $
  Seq "xx" (OpCall "r1" "get" "Unit") $
  Seq "yy" (OpCall "r2" "get" "Unit") $
  Seq "zz" (OpCall "r3" "get" "Unit") $
  Seq "aa" (OpCall "f1" "flip" "Unit") $
  Return $ Pair "xx" $ Pair "yy" $ Pair "zz" "aa"

main :: IO ()
main = do
  putStrLn $ "term: " ++ (show term)
  putStrLn ""
  putStrLn "TYPECHECKING"
  case tcComp delta gamma term of
    Left err -> putStrLn $ "type error: " ++ err
    Right ty -> do
      putStrLn $ "type: " ++ (show ty)
  putStrLn ""
  putStrLn "EVALUATION"
  let term' = removeAnnotsComp term
  stepsShow term'
  return ()
