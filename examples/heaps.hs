effect State {
  get : () -> Int
  put : Int -> ()
}

ref : forall s. Int -> (Inst s State)!{State@s}
ref = /\s. \v.
  new State@s with {
    get () k -> return \s -> g <- k s; return s
    put s' k -> return \s -> g <- k (); return s'
    return x -> return \s -> return x
    finally sf -> sf v
  } as r in return r

incRef : forall s. Inst s State -> Int!{State@s}
incRef = /\s. \r.
    x <- r#get ();
    r#put (x + 1);
    return x

comp : forall s. Int!{State@s}
comp = /\s.
  r <- ref [s] 42;
  x <- incRef [s] r;
  return x

main : () -> Int
main = \().
  handle(comp)

-- reduction derivation
handle(comp)
~> handle(rf <- ref [s]; r <- rf 42; xf <- incRef [s]; x <- xf r; return x)
~> 
 