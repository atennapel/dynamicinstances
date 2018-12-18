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
incRef = /\s. return \r.
    x <- r#get ();
    _ <- r#put (x + 1);
    return x

comp : forall s. Int!{State@s}
comp = /\s.
  r <- ref [s] 42;
  x <- incRef [s] r;
  return x

main : () -> Int
main = \().
  handle(comp)

-- reduction derivations
h = 
  get () k -> return \s -> g <- k s; g s
  put s' k -> return \s -> g <- k (); g s'
  return x -> return \s -> return x
  finally sf -> sf v
h' =
  ...h
  finally sf -> sf 42

handle(comp)
~> handle(/\s. rf <- ref [s]; r <- rf 42; xf <- incRef [s]; x <- xf r; return x)
~> handle^s(rf <- ref [s']; r <- rf 42; xf <- incRef [s']; x <- xf r; return x)
~> handle^s(rf <- return (\v.new State@s with {h} as r in return r); r <- rf 42; xf <- incRef [s']; x <- xf r; return x)
~> handle^s(r <- (\v.new State@s with {h} as r in return r) 42; xf <- incRef [s']; x <- xf r; return x)
~> handle^s(r <- (new State@s with {h'} as r in return r); xf <- incRef [s']; x <- xf r; return x)
~> handle^s(new State@s with {h'} as r in (r <- return r; xf <- incRef [s']; x <- xf r; return x))
~> handle^s(f <- handle^l{h'}(r <- return (inst l); xf <- incRef [s']; x <- xf r; return x); f 42)
~> handle^s(f <- handle^l{h'}(xf <- incRef [s']; x <- xf (inst l); return x); f 42)
~> handle^s(f <- handle^l{h'}(xf <- (/\s. return \r. x <- r#get (); r#put (x + 1); return x) [s']; x <- xf (inst l); return x); f 42)
~> handle^s(f <- handle^l{h'}(xf <- (return \r. x <- r#get (); r#put (x + 1); return x); x <- xf (inst l); return x); f 42)
~> handle^s(f <- handle^l{h'}(x <- (\r. x <- r#get (); r#put (x + 1); return x) (inst l); return x); f 42)
~> handle^s(f <- handle^l{h'}(x' <- (x <- (inst l)#get (); (inst l)#put (x + 1); return x); return x'); f 42)
~> handle^s(f <- handle^l{h'}(x <- (inst l)#get (); x' <- ((inst l)#put (x + 1); return x); return x'); f 42)
~> handle^s(f <- (return \s -> g <- (\x. handle^l{h'}(x' <- ((inst l)#put (x + 1); return x); return x')) s; g s); f 42)
~> handle^s((\s -> g <- (\x. handle^l{h'}(x' <- ((inst l)#put (x + 1); return x); return x')) s; g s) 42)
~> handle^s(g <- (\x. handle^l{h'}(x' <- ((inst l)#put (x + 1); return x); return x')) 42; g 42)
~> handle^s(g <- handle^l{h'}(x' <- (_ <- (inst l)#put 43; return 42); return x'); g 42)
~> handle^s(g <- handle^l{h'}(_ <- (inst l)#put 43; x' <- return 42; return x'); g 42)
~> handle^s(g <- handle^l{h'}(_ <- (inst l)#put 43; x' <- return 42; return x'); g 42)
~> handle^s(g <- (return \s -> g' <- (\_. handle^l{h'}(x' <- return 42; return x')) (); g' 43); g 42)
~> handle^s((\s -> g' <- (\_. handle^l{h'}(x' <- return 42; return x')) (); g' 43) 42)
~> handle^s(g' <- (\_. handle^l{h'}(x' <- return 42; return x')) (); g' 43)
~> handle^s(g' <- handle^l{h'}(x' <- return 42; return x'); g' 43)
~> handle^s(g' <- handle^l{h'}(return 42); g' 43)
~> handle^s(g' <- (return \s -> return 42); g' 43)
~> handle^s((\s -> return 42) 43)
~> handle^s(return 42)
~> return 42

-- multiple refs
-- handle(/\s.
--    r1 <- ref [s] 1;
--    r2 <- ref [s] 2;
--    x <- r1#get ();
--    y <- r2#get ();
--    return (x + y))
handle(/\s. r1f <- ref [s]; r1 <- r1f 1; r2f <- ref [s]; r2 <- r2f 2; x <- r1#get (); y <- r2#get (); return (x + y))
~> handle^s(r1f <- ref [s]; r1 <- r1f 1; r2f <- ref [s]; r2 <- r2f 2; x <- r1#get (); y <- r2#get (); return (x + y))
~> handle^s(r1f <- return (\v.new State@s with {h} as r in return r); r1 <- r1f 1; r2f <- ref [s]; r2 <- r2f 2; x <- r1#get (); y <- r2#get (); return (x + y))
~> handle^s(r1 <- (\v.new State@s with {h} as r in return r) 1; r2f <- ref [s]; r2 <- r2f 2; x <- r1#get (); y <- r2#get (); return (x + y))
~> handle^s(r1 <- (new State@s with {h1} as r in return r); r2f <- ref [s]; r2 <- r2f 2; x <- r1#get (); y <- r2#get (); return (x + y))
~> handle^s(new State@s with {h1} as r in (r1 <- return r; r2f <- ref [s]; r2 <- r2f 2; x <- r1#get (); y <- r2#get (); return (x + y)))
~> handle^s(f <- handle^l1{h1}(r1 <- return (inst l1); r2f <- ref [s]; r2 <- r2f 2; x <- r1#get (); y <- r2#get (); return (x + y)); f 1)
~> handle^s(f <- handle^l1{h1}(r2f <- ref [s]; r2 <- r2f 2; x <- (inst l1)#get (); y <- r2#get (); return (x + y)); f 1)
~> handle^s(f <- handle^l1{h1}(r2f <- return (\v.new State@s with {h} as r in return r); r2 <- r2f 2; x <- (inst l1)#get (); y <- r2#get (); return (x + y)); f 1)
~> handle^s(f <- handle^l1{h1}(r2 <- (\v.new State@s with {h} as r in return r) 2; x <- (inst l1)#get (); y <- r2#get (); return (x + y)); f 1)
~> handle^s(f <- handle^l1{h1}(r2 <- (new State@s with {h2} as r in return r); x <- (inst l1)#get (); y <- r2#get (); return (x + y)); f 1)
~> handle^s(f <- handle^l1{h1}(new State@s with {h2} as r in (r2 <- return r; x <- (inst l1)#get (); y <- r2#get (); return (x + y)); f 1))
~> handle^s(f <- new State@s with {h2} as r in handle^l1{h1}(r2 <- return r; x <- (inst l1)#get (); y <- r2#get (); return (x + y)); f 1)
~> handle^s(new State@s with {h2} as r in (f <- handle^l1{h1}(r2 <- return r; x <- (inst l1)#get (); y <- r2#get (); return (x + y)); f 1))
~> handle^s(f' <- handle^l2{h2}(f <- handle^l1{h1}(r2 <- return (inst l2); x <- (inst l1)#get (); y <- r2#get (); return (x + y)); f 1); f' 2)
~> handle^s(f' <- handle^l2{h2}(f <- handle^l1{h1}(x <- (inst l1)#get (); y <- (inst l2)#get (); return (x + y)); f 1); f' 2)
~> handle^s(f' <- handle^l2{h2}(f <- handle^l1{h1}(x <- (inst l1)#get (); y <- (inst l2)#get (); return (x + y)); f 1); f' 2)
~> handle^s(f' <- handle^l2{h2}(f <- (return \st -> g <- (\x. handle^l1{h1}(y <- (inst l2)#get (); return (x + y))) st; g st); f 1); f' 2)
~> handle^s(f' <- handle^l2{h2}((\st -> g <- (\x. handle^l1{h1}(y <- (inst l2)#get (); return (x + y))) st; g st) 1); f' 2)
~> handle^s(f' <- handle^l2{h2}(g <- (\x. handle^l1{h1}(y <- (inst l2)#get (); return (x + y))) 1; g 1); f' 2)
~> handle^s(f' <- handle^l2{h2}(g <- handle^l1{h1}(y <- (inst l2)#get (); return (1 + y)); g 1); f' 2)
~> handle^s(f' <- handle^l2{h2}(g <- (y <- (inst l2)#get (); handle^l1{h1}(return (1 + y))); g 1); f' 2)
~> handle^s(f' <- handle^l2{h2}(y <- (inst l2)#get (); g <- handle^l1{h1}(return (1 + y)); g 1); f' 2)
~> handle^s(f' <- handle^l2{h2}(y <- (inst l2)#get (); g <- handle^l1{h1}(return (1 + y)); g 1); f' 2)
WIP
