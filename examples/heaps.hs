effect State {
  get : () -> Int
  put : Int -> ()
}

ref : forall s. Int -> (Inst s State -> Int!{State@s}) -> Int!{State@s}
ref = /\s. \v f.
  new State@s with {
    get () k -> \s -> k s s
    put s' k -> \s -> k () s'
    return x -> \s -> x
    finally sf -> sf v
  } as r in
    f r

incRef : forall s. Inst s State -> Int!{State@s}
incRef = /\s. \r.
    x <- r#get ();
    r#put (x + 1);
    return x

comp : forall s. Int!{State@s}
comp = /\s.
  ref [s] 42 \r1 ->
  ref [s] 43 \r2 ->
    x <- incRef [s] r1;
    y <- incRef [s] r2;
    return (x + y)

main : () -> Int
main = \().
  handle(comp)
