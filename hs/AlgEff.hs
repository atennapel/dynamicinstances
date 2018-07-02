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
  
data CompTy = CompTy Ty
  deriving (Eq)

instance Show CompTy where
  show (CompTy t) = show t

data Val
  | Var Name
  | Abs Name (Maybe Ty) Comp
  | Anno Val Ty
  deriving (Eq)

instance Show Val where
  show (Var x) = show x
  show (Abs x (Just t) c) = "(\\(" ++ (show x) ++ " : " ++ (show t) ++ ") -> " ++ (show c) ++ ")"
  show (Abs x Nothing c) = "(\\" ++ (show x) ++ " -> " ++ (show c) ++ ")"
  show (Anno v t) = "(" ++ (show v) ++ " : " ++ (show t) ++ ")"

data Comp
  | Ret Val
  | App Val Val
  | Do Name Comp Comp
  | CAnno Comp CompTy
  deriving (Eq)

instance Show Comp where
  show (Ret v) = "(return " ++ show v ++ ")"
  show (App a b) = "(" ++ (show a) ++ " " ++ (show b) ++ ")"
  show (Do x a b) = "(" ++ (show x) ++ " <- " ++ (show a) ++ "; " ++ (show b) ++ ")"
  show (CAnno c t) = "(" ++ (show c) ++ " : " ++ (show t) ++ ")"

-- Monad
type Res t = Either String t

err :: String -> Res t
err m = Left m

-- context
data Elem
  | CTCon Name
  | CTEx Name
  | CSolved Name Ty
  | CVar Name Ty
  deriving (Eq)

instance Show Elem where
  show (CTCon x) = x
  show (CTEx x) = "^" ++ x
  show (CSolved x t) = "^" ++ x ++ " = " ++ (show t)
  show (CVar x t) = x ++ " : " ++ (show t)

data Context = Context [Elem]
  deriving (Eq)

instance Show Context where
  show (Context es) = show $ reverse es

-- wellformedness
tyWF :: Context -> Ty -> Res ()
tyWF ctx (TCon x) = findTCon ctx x
tyWF ctx (TEx x) = findTExOrSolved ctx x
tyWF ctx (TFun a b) = do
  tyWF ctx a
  tyWF ctx b

compTyWF :: Context -> CompTy -> Res ()

elemWF :: Context -> Elem -> Res ()

contextWF :: Context -> Res ()

-- unification

-- type inference
