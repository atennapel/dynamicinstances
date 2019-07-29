{-# LANGUAGE OverloadedStrings #-}

module MiroExample where

import qualified Data.Map as Map

import Miro

tInt :: Type
tInt = TCon "Int"

tBool :: Type
tBool = TCon "Bool"

tUnit :: Type
tUnit = TCon "Unit"

effEnv :: EffEnv
effEnv =
  effEnvFromList [
    ("Flip", [("flip", (tUnit, tBool))]),
    ("State", [("get", (tUnit, tInt)), ("put", (tInt, tUnit))])
  ]

delta :: Delta
delta = DEmpty

gamma :: Gamma
gamma =
  gammaFromList [
    ("Unit", tUnit),

    ("True", tBool),
    ("False", tBool),

    ("zero", tInt),
    ("one", tInt),
    ("two", tInt)
  ]

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
runscope(s1 ->
  r1 <- new State@s1 {..., finally f -> f zero} as rx1 in return rx1;
  runscope(s2 ->
    r2 <- new State@s2 {..., finally f -> f zero} as rx2 in return rx2;
    r3 <- new State@s2 {..., finally f -> f two} as rx3 in (_ <- r1#put(one); return rx3);
    f1 <- new Flip@s1 {...} as f1 in return f1;
    xx <- r1#get();
    yy <- r2#get();
    zz <- r3#get();
    aa <- f1#flip();
    return (xx, (yy, (zz, aa)))
  )
)
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
  case tcComp effEnv delta gamma term of
    Left err -> putStrLn $ "type error: " ++ err
    Right ty -> do
      putStrLn $ "type: " ++ (show ty)
  putStrLn ""
  putStrLn "EVALUATION"
  let term' = removeAnnotsComp term
  stepsShow term'
  return ()
