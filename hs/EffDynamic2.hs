{-# LANGUAGE OverloadedStrings #-}

import GHC.Exts (IsString(..))
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

-- Names
type Name = String

-- Kinds
data Kind
  = KTy
  deriving (Eq)

instance Show Kind where
  show KTy = "Type"

-- Types
data Ty
  = TBound Int
  | TFree Name
  | TForall Kind CTy
  deriving (Eq)

instance Show Ty where
  show (TBound i) = "'" ++ (show i)
  show (TFree x) = x
  show (TForall k t) = "(forall " ++ (show k) ++ ". " ++ (show t) ++ ")"

data CTy
  = CTy Ty
  deriving (Eq)

instance Show CTy where
  show (CTy t) = show t

-- AST
data Val
  = Bound Int
  | Free Name
  | Abs Ty Comp
  deriving (Eq)

instance Show Val where
  show (Bound i) = "'" ++ (show i)
  show (Free x) = x
  show (Abs t b) = "()"

data Comp
  = Return Val
  | App Val Val
  | Do Comp Comp
  deriving (Eq)
