{-# LANGUAGE OverloadedStrings #-}

import GHC.Exts (IsString(..))
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

-- Names
type Name = String
type Row = Set Name

-- Kind
data Kind
  = KTy
  | KEff Name
  deriving (Eq)

instance Show Kind where
  show KTy = "*"
  show (KEff e) = e

-- Types
class ContainsTVar t where
  freeTVars :: t -> Set Name
  substTVar :: Name -> Ty -> t -> t

containsFreeTVar :: ContainsTVar t => Name -> t -> Bool
containsFreeTVar x t = Set.member x $ freeTVars t

data Ty
  = TVar Name
  | TFun Ty TyComp
  | THandler TyComp TyComp
  | TForall Name Kind Ty
  deriving (Eq)

instance Show Ty where
  show (TVar x) = x
  show (TFun x y) = "(" ++ (show x) ++ " -> " ++ (show y) ++ ")"
  show (THandler x y) = "(" ++ (show x) ++ " => " ++ (show y) ++ ")"
  show (TForall x k t) =
    "forall(" ++ x ++ " : " ++ (show k) ++ "). " ++ (show t)

instance IsString Ty where
  fromString = TVar

instance ContainsTVar Ty where
  freeTVars (TVar x) = Set.singleton x
  freeTVars (TFun a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (THandler a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (TForall x k t) = Set.delete x (freeTVars t)

  substTVar x s t@(TVar y) = if x == y then s else t
  substTVar x s (TFun a b) = TFun (substTVar x s a) (substTVar x s b)
  substTVar x s (THandler a b) = THandler (substTVar x s a) (substTVar x s b)
  substTVar x s t@(TForall y k b) = if x == y then t else TForall y k (substTVar x s b)

data TyComp
  = TyComp Ty Row
  | TExists Name Name TyComp
  deriving (Eq)

texists :: [(Name, Name)] -> Ty -> Row -> TyComp
texists [] t r = TyComp t r
texists ((x, e) : xs) t r = TExists x e $ texists xs t r

unwrap :: TyComp -> ([(Name, Name)], Ty, Row)
unwrap (TyComp t r) = ([], t, r)
unwrap (TExists x e t) = let (xs, t', r) = unwrap t in ((x, e) : xs, t', r)

instance Show TyComp where
  show (TyComp t r) =
    if null r then
      show t
    else
      (show t) ++ "!{" ++ (intercalate ", " $ Set.elems r) ++ "}"
  show (TExists x e t) =
    "exists(" ++ x ++ " : " ++ e ++ "). " ++ (show t)

ret :: Ty -> TyComp
ret t = TyComp t Set.empty

instance IsString TyComp where
  fromString x = TyComp (TVar x) Set.empty

instance ContainsTVar TyComp where
  freeTVars (TyComp t r) = Set.union (freeTVars t) r
  freeTVars (TExists y _ b) = Set.delete y (freeTVars b)

  substTVar x s (TyComp t r) = TyComp (substTVar x s t) r
  substTVar x s t@(TExists y e b) = if x == y then t else TExists y e (substTVar x s b)

-- AST
data Val
  = Var Name
  | Abs Name Comp
  | AbsT Name Kind Val
  | AppT Val Ty
  | Handler Val (Name, Comp) (Map Name (Name, Name, Comp))
  | Anno Val Ty
  deriving (Eq)

instance ContainsTVar Val where
  freeTVars (Var _) = Set.empty
  freeTVars (Abs _ b) = freeTVars b
  freeTVars (AbsT x k b) = Set.delete x $ freeTVars b
  freeTVars (AppT v t) = Set.union (freeTVars v) (freeTVars t)
  freeTVars (Handler v (_, c) m) = Set.union (freeTVars v) $ Set.union (freeTVars c)
    (foldl Set.union Set.empty $ map (\(_, _, c) -> freeTVars c) $ Map.elems m)
  freeTVars (Anno v t) = Set.union (freeTVars v) (freeTVars t)

  substTVar x s v@(Var _) = v
  substTVar x s (Abs y b) = Abs y $ substTVar x s b
  substTVar x s v@(AbsT y k b) = if x == y then v else AbsT y k $ substTVar x s b
  substTVar x s (AppT v t) = AppT (substTVar x s v) (substTVar x s t)
  substTVar x s (Handler v (y, c) m) = Handler (substTVar x s v) (y, substTVar x s c) $
    Map.map (\(a, b, c) -> (a, b, substTVar x s c)) m
  substTVar x s (Anno v t) = Anno (substTVar x s v) (substTVar x s t)

instance Show Val where
  show (Var x) = x
  show (Abs x b) = "(\\" ++ x ++ " -> " ++ (show b) ++ ")"
  show (AbsT x k b) = "(/\\(" ++ x ++ " : " ++ (show k) ++ ") -> " ++ (show b) ++ ")"
  show (AppT x y) = "(" ++ (show x) ++ " [" ++ (show y) ++ "])"
  show (Anno x t) = "(" ++ (show x) ++ " : " ++ (show t) ++ ")"
  show (Handler eff (xr, cr) ops) | Map.null ops = "handler(" ++ (show eff) ++ ") { return " ++ xr ++ " -> " ++ (show cr) ++ " }"
  show (Handler eff (xr, cr) ops) = "handler(" ++ (show eff) ++ ") { return " ++ xr ++ " -> " ++ (show cr) ++ ", " ++
    (intercalate ", " $ map (\(op, (x, k, c)) -> op ++ " " ++ x ++ " " ++ k ++ " -> " ++ (show c)) $ Map.assocs ops) ++ " }"

instance IsString Val where
  fromString = Var

data Comp
  = Return Val
  | App Val Val
  | Do Name Comp Comp
  | Handle Val Comp
  | Op Val Name Val
  | New Name Name
  deriving (Eq)

instance Show Comp where
  show (Return v) = "return " ++ (show v)
  show (App x y) = "(" ++ (show x) ++ " " ++ (show y) ++ ")"
  show (Do x a b) = "(" ++ x ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"
  show (Handle v c) = "(with " ++ (show v) ++ " handle " ++ (show c) ++ ")"
  show (Op i o v) = (show i) ++ "#" ++ o ++ "(" ++ (show v) ++ ")"
  show (New e x) = "(new " ++ e ++ " as " ++ x ++ ")"

instance IsString Comp where
  fromString x = Return $ Var x

instance ContainsTVar Comp where
  freeTVars (Return v) = freeTVars v
  freeTVars (App a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Do x a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Handle a b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (Op a o b) = Set.union (freeTVars a) (freeTVars b)
  freeTVars (New e _) = Set.empty

  substTVar x s (Return v) = Return $ substTVar x s v
  substTVar x s (App a b) = App (substTVar x s a) (substTVar x s b)
  substTVar x s (Do y a b) = Do y (substTVar x s a) (substTVar x s b)
  substTVar x s (Handle a b) = Handle (substTVar x s a) (substTVar x s b)
  substTVar x s (Op a o b) = Op (substTVar x s a) o (substTVar x s b)
  substTVar x s v@(New _ _) = v

-- TC
type TC t = Either String t

tcNot :: String -> TC t -> TC ()
tcNot msg (Left _) = return ()
tcNot msg (Right _) = Left msg

tcDrop :: TC t -> TC ()
tcDrop c = do
  c
  return ()

tcMaybe :: String -> Maybe t -> TC t
tcMaybe msg c =
  case c of
    Just v -> return v
    Nothing -> Left msg

-- Context
data Elem
  = CEff Name (Map Name (Ty, Ty))
  | CVar Name Ty
  | CTVar Name Kind
  deriving (Eq)

instance Show Elem where
  show (CEff x ops) = "effect " ++ x
  show (CVar x t) = x ++ " : " ++ (show t)

type Context = [Elem]

context :: [Elem] -> Context
context = reverse

findEff :: Context -> Name -> TC (Map Name (Ty, Ty))
findEff [] x = Left $ "effect " ++ x ++ " not found"
findEff (CEff y ops : _) x | x == y = return ops
findEff (_ : r) x = findEff r x

findVar :: Context -> Name -> TC Ty
findVar [] x = Left $ "var " ++ x ++ " not found"
findVar (CVar y t : _) x | x == y = return t
findVar (_ : r) x = findVar r x

findTVar :: Context -> Name -> TC Kind
findTVar [] x = Left $ "tvar " ++ x ++ " not found"
findTVar (CTVar y k : _) x | x == y = return k
findTVar (_ : r) x = findTVar r x

freshTVar :: Context -> Name -> Name
freshTVar ctx x = fresh ctx x
  where
    fresh [] x = x
    fresh (CTVar y _ : _) x | x == y = fresh ctx (x ++ "'")
    fresh (_ : r) x = fresh r x

-- Subtyping
subTy :: Ty -> Ty -> Bool
subTy (TVar x) (TVar y) = x == y
subTy (TFun x y) (TFun a b) = subTy a x && subTyComp y b
subTy (THandler x y) (THandler a b) = subTyComp a x && subTyComp y b
subTy (TForall x k b) (TForall y k' b') =
  x == y && k == k' && subTy b b'
subTy x y = False

usedTVars :: ContainsTVar t => Set Name -> t -> Set Name -> Set Name
usedTVars xs t r = Set.intersection xs $ Set.union (freeTVars t) r

subTyComp :: TyComp -> TyComp -> Bool
subTyComp ct1 ct2 =
  let (is1, t1, r1) = unwrap ct1 in
  let (is2, t2, r2) = unwrap ct2 in
  let uis1 = usedTVars (Set.fromList $ map fst is1) t1 r1 in
  let uis2 = usedTVars (Set.fromList $ map fst is2) t2 r2 in
  Set.isSubsetOf uis2 uis1 && Set.isSubsetOf r1 r2 && subTy t1 t2

-- Val type checking
synthInst :: Context -> Val -> TC (Name, Name)
synthInst ctx inst = do
  ti <- synthVal ctx inst
  case ti of
    TVar xi -> do
      ki <- findTVar ctx xi
      case ki of
        KEff eff -> return (xi, eff)
        _ -> Left $ "invalid kind for instance " ++ (show inst) ++ " : " ++ (show ti) ++ " : " ++ (show ki)
    _ -> Left $ "invalid instance " ++ (show inst) ++ " : " ++ (show ti)

synthVal :: Context -> Val -> TC Ty
synthVal ctx (Var x) = findVar ctx x
synthVal ctx (Anno x t) = do
  checkVal ctx x t
  return t
synthVal ctx (AbsT x k b) = do
  t <- synthVal (CTVar x k : ctx) b
  return $ TForall x k t
synthVal ctx (AppT a b) = do
  t <- synthVal ctx a
  case t of
    TForall x k t' -> return $ substTVar x b t'
    _ -> Left $ "not a forall in type application " ++ (show a) ++ " : " ++ (show t)
synthVal ctx x = Left $ "cannot synth val " ++ (show x)

checkCase :: Context -> TyComp -> (Ty, Ty, Name, Name, Comp) -> TC ()
checkCase ctx tr (ta, tb, x, k, c) =
  checkComp (CVar x ta : CVar k (TFun tb tr) : ctx) c tr

checkVal :: Context -> Val -> Ty -> TC ()
checkVal ctx (Abs x t) (TFun a b) = checkComp (CVar x a : ctx) t b
checkVal ctx vh@(Handler inst (xr, cr) ops) th@(THandler (TyComp a r1) tr@(TyComp b r2)) = do
  (xi, eff) <- synthInst ctx inst
  tops <- findEff ctx eff
  if Map.keysSet ops == Map.keysSet tops && Set.isSubsetOf (Set.delete xi r1) r2 then do
    checkComp (CVar xr a : ctx) cr tr
    let cases = Map.elems $ Map.intersectionWith (\(ta, tb) (x, k, c) -> (ta, tb, x, k, c)) tops ops
    mapM_ (checkCase ctx tr) cases
  else
    Left $ "invalid type for handler " ++ (show vh) ++ " : " ++ (show th)
checkVal ctx x t = do
  t' <- synthVal ctx x
  if subTy t' t then
    return ()
  else
    Left $ "type mismatch " ++ (show t') ++ " <: " ++ (show t)

-- Comp typechecking
synthComp :: Context -> Comp -> TC TyComp
synthComp ctx (Return v) = do
  t <- synthVal ctx v
  return $ TyComp t Set.empty
synthComp ctx (App a b) = do
  ft <- synthVal ctx a
  case ft of
    TFun l r -> do
      checkVal ctx b l
      return r
    _ -> Left $ "not a function type: " ++ (show ft)
synthComp ctx (Do x a b) = do
  t1 <- synthComp ctx a
  let (is, t, r) = unwrap t1
  t2 <- synthComp (CVar x t : ((map (\(x, e) -> CTVar x (KEff e)) is) ++ ctx)) b
  let (is', t', r') = unwrap t2
  return $ texists (is ++ is') t' (Set.union r r')
synthComp ctx (Handle v c) = do
  ct <- synthComp ctx c
  let (is, t, r) = unwrap ct
  ft <- synthVal ((map (\(x, e) -> CTVar x (KEff e)) is) ++ ctx) v
  case ft of
    THandler a (TyComp b r') -> do
      if subTyComp (TyComp t r) a then
        return $ texists is b r'
      else
        Left $ "subtyping failed in handler application"
    _ -> Left $ "not a handler type: " ++ (show ft)
synthComp ctx (Op inst op v) = do
  (xi, eff) <- synthInst ctx inst
  tops <- findEff ctx eff
  (pt, rt) <- tcMaybe ("operation does not belong to " ++ eff ++ ": " ++ op) $ Map.lookup op tops
  checkVal ctx v pt
  return $ TyComp rt (Set.singleton xi)
synthComp ctx (New e x) = do
  findEff ctx e
  return $ TExists x e $ TyComp (TVar x) Set.empty
-- synthComp ctx t = Left $ "unable to synth comp " ++ (show t)

checkComp :: Context -> Comp -> TyComp -> TC ()
checkComp ctx (Return v) (TyComp t _) = checkVal ctx v t
checkComp ctx x t = do
  t' <- synthComp ctx x
  if subTyComp t' t then
    return ()
  else
    Left $ "type mismatch " ++ (show t') ++ " <: " ++ (show t)

-- Testing
ctx :: Context
ctx =
  context [
    CTVar "Bool" KTy,
    CVar "True" (TVar "Bool"),
    CVar "False" (TVar "Bool"),

    CTVar "Unit" KTy,
    CVar "Unit" (TVar "Unit"),

    CVar "not" (TFun "Bool" "Bool"),

    CEff "Fail" (Map.fromList [("fail", ("Unit", "Unit"))]),
    CEff "State" (Map.fromList [("get", ("Unit", "Bool")), ("put", ("Bool", "Unit"))])
  ]

{-
stateH : forall (t:*) (ti:State). ti -> (t!{ti} => (Bool -> t)) 
stateH = /\t ti -> \i ->
  handler(i) {
    return x -> \s -> x
    get () k -> \s -> k s s
    put s k -> \_ -> k () s
  }
-}
stateH :: Val
stateH = AbsT "t" KTy $ AbsT "ti" (KEff "State") $
  Anno
    (Abs "i" $ Return $ Handler "i" ("x", Return $ Anno (Abs "s" "x") (TFun "Bool" "t")) $ Map.fromList
      [
        ("get", ("_", "k", Return $ Abs "s" $ Do "f" (App "k" "s") (App "f" "s"))),
        ("put", ("s'", "k", Return $ Abs "s" $ Do "f" (App "k" "Unit") (App "f" "s'")))
      ])
    (TFun "ti" $ ret $ THandler (TyComp "t" $ Set.singleton "ti") (ret $ TFun "Bool" "t"))

{-
stateF : forall (t:*)(ti:State). Bool -> ti -> (() -> t!{ti}) -> t
stateF = /\t ti -> \v i a ->
  f <- with (stateH [t] [ti] i) handle (a ());
  f v
-}
stateF :: Val
stateF = AbsT "t" KTy $ AbsT "ti" (KEff "State") $
  Anno
    (Abs "v" $ Return $ Abs "i" $ Return $ Abs "a" $
      Do "h" (App (AppT (AppT stateH "t") "ti") "i") $
      Do "f" (Handle "h" (App "a" "Unit"))
      (App "f" "v"))
    (TFun "Bool" $ ret $ TFun "ti" $ ret $ TFun (TFun "Unit" (TyComp "t" (Set.singleton "ti"))) "t")

{-
stateRef : forall (t:*). Bool -> (forall (ti:State). ti -> t!{ti}) -> t
stateRef = /\t -> \v a ->
  i <- new State;
  stateF [t] [ti] v (a i)
-}
stateRef :: Val
stateRef = AbsT "t" KTy $
  Anno
    (Abs "v" $ Return $ Abs "a" $
      Do "i" (New "State" "ti") $
      Do "fr" (App (AppT (AppT stateF "t") "ti") "v") $
      Do "fr'" (App "fr" "i") $
      Do "ar" (App (AppT "a" "ti") "i") $
      App "fr'" "ar")
    (TFun "Bool" $ ret $ TFun (TForall "ti" (KEff "State") $ TFun "ti" (TyComp "t" (Set.singleton "ti"))) "t")

{-
escapeRef : () -> Bool
escapeRef = \() -> stateRef [Bool] False (/\(ti:State). \i -> i#get ())
-}
escapeRef :: Val
escapeRef = Anno
  (Abs "_" $
    Do "f" (App (AppT stateRef "Bool") "False") $
    App "f" $
      AbsT "ti" (KEff "State") (
        Anno
          (Abs "i" $ Op "i" "get" "Unit")
          (TFun "ti" (TyComp "Bool" (Set.singleton "ti")))))
  (TFun "Unit" "Bool")

term :: Comp
term = Return $ stateRef

main :: IO ()
main = do
  putStrLn $ show term
  putStrLn $ show $ synthComp ctx term
