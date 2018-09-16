import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

type Name = String
type Row = Set Name

data Ty
  = TVar Name
  | TFun Ty TyComp
  | THandler TyComp TyComp
  deriving (Eq)

instance Show Ty where
  show (TVar x) = x
  show (TFun x y) = "(" ++ (show x) ++ " -> " ++ (show y) ++ ")"
  show (THandler x y) = "(" ++ (show x) ++ " => " ++ (show y) ++ ")"

data TyComp
  = TyComp Ty Row
  deriving (Eq)

instance Show TyComp where
  show (TyComp t r) =
    if null r then
      show t
    else
      (show t) ++ "!{" ++ (intercalate ", " $ Set.elems r) ++ "}"

data Val
  = Var Name
  | Abs Name Comp
  | Handler Name (Name, Comp) (Map Name (Name, Name, Comp))
  | Anno Val Ty
  deriving (Eq)

instance Show Val where
  show (Var x) = x
  show (Abs x b) = "(\\" ++ x ++ " -> " ++ (show b) ++ ")"
  show (Anno x t) = "(" ++ (show x) ++ " : " ++ (show t) ++ ")"
  show (Handler eff (xr, cr) ops) | Map.null ops = "handler " ++ eff ++ " { return " ++ xr ++ " -> " ++ (show cr) ++ " }"
  show (Handler eff (xr, cr) ops) = "handler " ++ eff ++ " { return " ++ xr ++ " -> " ++ (show cr) ++ ", " ++
    (intercalate ", " $ map (\(op, (x, k, c)) -> op ++ " " ++ x ++ " " ++ k ++ " -> " ++ (show c)) $ Map.assocs ops) ++ " }"

data Comp
  = Return Val
  | App Val Val
  | Do Name Comp Comp
  | Handle Val Comp
  deriving (Eq)

instance Show Comp where
  show (Return v) = "return " ++ (show v)
  show (App x y) = "(" ++ (show x) ++ " " ++ (show y) ++ ")"
  show (Do x a b) = "(" ++ x ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"
  show (Handle v c) = "(with " ++ (show v) ++ " handle " ++ (show c) ++ ")"

-- TC
type TC t = Either String t

tcNot :: String -> TC t -> TC ()
tcNot msg (Left _) = return ()
tcNot msg (Right _) = Left msg

tcDrop :: TC t -> TC ()
tcDrop c = do
  c
  return ()

-- Context
data Elem
  = CEff Name (Map Name (Ty, Ty))
  | CVar Name Ty
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

subTy :: Ty -> Ty -> Bool
subTy (TVar x) (TVar y) = x == y
subTy (TFun x y) (TFun a b) = subTy a x && subTyComp y b
subTy (THandler x y) (THandler a b) = subTyComp a x && subTyComp y b
subTy x y = False

subTyComp :: TyComp -> TyComp -> Bool
subTyComp (TyComp a r1) (TyComp b r2) =
  subTy a b && Set.isSubsetOf r1 r2

synthVal :: Context -> Val -> TC Ty
synthVal ctx (Var x) = findVar ctx x
synthVal ctx (Anno x t) = do
  checkVal ctx x t
  return t
synthVal ctx x = Left $ "cannot synth val " ++ (show x)

checkCase :: Context -> TyComp -> (Ty, Ty, Name, Name, Comp) -> TC ()
checkCase ctx tr (ta, tb, x, k, c) =
  checkComp (CVar x ta : CVar k (TFun tb tr) : ctx) c tr

checkVal :: Context -> Val -> Ty -> TC ()
checkVal ctx (Abs x t) (TFun a b) = checkComp (CVar x a : ctx) t b
checkVal ctx vh@(Handler eff (xr, cr) ops) th@(THandler (TyComp a r1) tr@(TyComp b r2)) = do
  tops <- findEff ctx eff
  if Map.keysSet ops == Map.keysSet tops && Set.isSubsetOf (Set.delete eff r1) r2 then do
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
  TyComp t r <- synthComp ctx a
  TyComp t' r' <- synthComp (CVar x t : ctx) b
  return $ TyComp t' (Set.union r r')
synthComp ctx (Handle v c) = do
  ft <- synthVal ctx v
  case ft of
    THandler a b -> do
      checkComp ctx c a
      return b
    _ -> Left $ "not a handler type: " ++ (show ft)

checkComp :: Context -> Comp -> TyComp -> TC ()
checkComp ctx (Return v) (TyComp ty _) = checkVal ctx v ty
checkComp ctx (Do x a b) (TyComp t r) = do
  TyComp t' r' <- synthComp ctx a
  checkComp (CVar x t' : ctx) b (TyComp t (Set.union r r'))
checkComp ctx x t = do
  t' <- synthComp ctx x
  if subTyComp t' t then
    return ()
  else
    Left $ "type mismatch " ++ (show t') ++ " <: " ++ (show t)

ctx :: Context
ctx =
  context [
    CVar "True" (TVar "Bool"),
    CVar "False" (TVar "Bool"),
    CVar "Unit" (TVar "Unit"),

    CVar "not" (TFun (TVar "Bool") (TyComp (TVar "Bool") Set.empty)),

    CEff "Fail" (Map.fromList [("fail", (TVar "Unit", TVar "Unit"))]),

    CVar "fail" (TFun (TVar "Unit") (TyComp (TVar "Unit") (Set.fromList ["Fail"]))),
    CVar "rand" (TFun (TVar "Unit") (TyComp (TVar "Bool") (Set.fromList ["Rand"])))
  ]

h :: Val
h = Anno (Handler "Fail" ("x", (Return (Var "x"))) (Map.fromList
  [
    ("fail", ("x", "k", Return (Var "True")))
  ])) (THandler (TyComp (TVar "Bool") (Set.fromList ["A", "Fail"])) (TyComp (TVar "Bool") (Set.fromList ["A"])))

term :: Comp
term = Return $ Anno (Abs "x" (Return (Var "x"))) (TFun (TVar "Bool") (TyComp (TVar "Bool") (Set.fromList ["A", "B", "C"])))

main :: IO ()
main = do
  putStrLn $ show term
  putStrLn $ show $ synthComp ctx term
