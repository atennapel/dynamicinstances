effect Flip {
  flip : () -> Bool
}

flip1, flip2 : Inst Flip
flip1 = new Flip
flip2 = new Flip

flipConst : Bool -> Inst Flip -> (<Flip> t => t)
flipConst b i = handler {
  i#flip () k -> k b
}

flipBoth : Inst Flip -> (<Flip> t => (t, t))
flipBoth i = handler {
  i#flip () k -> (k False, k True)
}
