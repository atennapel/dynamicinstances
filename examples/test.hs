effect State {
  get : () -> Int
  put : Int -> ()
}

effect Fail {
  fail : () -> ()
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
-- expected result = 42
-- h = 
--   get () k -> return \s -> g <- k s; g s
--   put s' k -> return \s -> g <- k (); g s'
--   return x -> return \s -> return x
--   finally sf -> sf v
-- h' =
--   ...h
--   finally sf -> sf 42

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
-- expected result = 1 + 2
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
~> handle^s(f' <- (return \s -> g' <- (\y. handle^l2{h2}(g <- handle^l1{h1}(return (1 + y)); g 1)) s; g' s); f' 2)
~> handle^s((\s -> g' <- (\y. handle^l2{h2}(g <- handle^l1{h1}(return (1 + y)); g 1)) s; g' s) 2)
~> handle^s(g' <- (\y. handle^l2{h2}(g <- handle^l1{h1}(return (1 + y)); g 1)) 2; g' 2)
~> handle^s(g' <- handle^l2{h2}(g <- handle^l1{h1}(return (1 + 2)); g 1); g' 2)
~> handle^s(g' <- handle^l2{h2}(g <- (return \s' -> return (1 + 2)); g 1); g' 2)
~> handle^s(g' <- handle^l2{h2}((\s' -> return (1 + 2)) 1); g' 2)
~> handle^s(g' <- handle^l2{h2}(return (1 + 2)); g' 2)
~> handle^s(g' <- (return \s -> return (1 + 2)); g' 2)
~> handle^s((\s -> return (1 + 2)) 2)
~> handle^s(return (1 + 2))
~> return (1 + 2)

-- handling exception-like effect (Fail)
-- expected result = 42
-- h = fail () k -> return 42; return x -> return x; finally x -> return x
handle(/\s. new Fail@s {h} as f in (_ <- f#fail (); return 0))
~> handle^s(new Fail@s {h} as f in (_ <- f#fail (); return 0))
~> handle^s(handle^l{h}(_ <- (inst l)#fail (); return 0))
~> handle^s(return 42)
~> return 42

-- two instances of Fail, order of handling is important here
-- expected result = 1
-- h1 = fail () k -> return 1; return x -> return x; finally x -> return x
-- h2 = fail () k -> return 2; return x -> return x; finally x -> return x
handle(/\s. new Fail@s {h1} as f1 in (new Fail@s {h2} as f2 in (_ <- f1#fail (); _ <- f2#fail (); return 0)))
~> handle^s(new Fail@s {h1} as f1 in (new Fail@s {h2} as f2 in (_ <- f1#fail (); _ <- f2#fail (); return 0)))
~> handle^s(handle^l1{h1}(new Fail@s {h2} as f2 in (_ <- (inst l1)#fail (); _ <- f2#fail (); return 0)))
~> handle^s(new Fail@s {h2} as f2 in handle^l1{h1}(_ <- (inst l1)#fail (); _ <- f2#fail (); return 0))
~> handle^s(handle^l2{h2}(handle^l1{h1}(_ <- (inst l1)#fail (); _ <- (inst l2)#fail (); return 0)))
~> handle^s(handle^l2{h2}(return 1))
~> handle^s(return 1)
~> return 1

-- previous example with swapped uses of the instances (f2 before f1)
-- expected result = 2
handle(/\s. new Fail@s {h1} as f1 in (new Fail@s {h2} as f2 in (_ <- f2#fail (); _ <- f1#fail (); return 0)))
~> handle^s(new Fail@s {h1} as f1 in (new Fail@s {h2} as f2 in (_ <- f2#fail (); _ <- f1#fail (); return 0)))
~> handle^s(handle^l1{h1}(new Fail@s {h2} as f2 in (_ <- f2#fail (); _ <- (inst l1)#fail (); return 0)))
~> handle^s(new Fail@s {h2} as f2 in handle^l1{h1}(_ <- f2#fail (); _ <- (inst l1)#fail (); return 0))
~> handle^s(handle^l2{h2}(handle^l1{h1}(_ <- (inst l2)#fail (); _ <- (inst l1)#fail (); return 0)))
~> handle^s(handle^l2{h2}(_ <- (inst l2)#fail (); handle^l1{h1}(_ <- (inst l1)#fail (); return 0)))
~> handle^s(return 2)
~> return 2

-- previous example but with a list of handlers instead (without handle^l{h})
handle(/\s. new Fail@s {h1} as f1 in (new Fail@s {h2} as f2 in (_ <- f1#fail (); _ <- f2#fail (); return 0)))
~> handle^s(new Fail@s {h1} as f1 in (new Fail@s {h2} as f2 in (_ <- f1#fail (); _ <- f2#fail (); return 0)))
~> handle^s[l1&h1](new Fail@s {h2} as f2 in (_ <- (inst l1)#fail (); _ <- f2#fail (); return 0))
~> handle^s[l1&h1, l2&h2](_ <- (inst l1)#fail (); _ <- (inst l2)#fail (); return 0)
~> handle^s[l1&h1, l2&h2](return 1)
~> return 1

-- previous example with swapper uses of instances (f2 before f1)
handle(/\s. new Fail@s {h1} as f1 in (new Fail@s {h2} as f2 in (_ <- f2#fail (); _ <- f1#fail (); return 0)))
~> handle^s(new Fail@s {h1} as f1 in (new Fail@s {h2} as f2 in (_ <- f2#fail (); _ <- f1#fail (); return 0)))
~> handle^s[l1&h1](new Fail@s {h2} as f2 in (_ <- f2#fail (); _ <- (inst l1)#fail (); return 0))
~> handle^s[l1&h1, l2&h2](_ <- (inst l2)#fail (); _ <- (inst l1)#fail (); return 0)
~> handle^s[l1&h1, l2&h2](return 2)
~> return 2

-- handle^s with list, with State
-- h = 
--   get () k -> return \s -> g <- k s; g s
--   put s' k -> return \s -> g <- k (); g s'
--   return x -> return \s -> return x
--   finally sf -> sf 42
handle(/\s. new State@s {h} as r in r#get ())
~> handle^s[](new State@s {h} as r in r#get ())
~> handle^s[l&h]((inst l)#get ())
~> handle^s[l&h](x <- (inst l)#get (); return x)
~> handle^s[l&h](f <- (return \s -> g <- (\x. handle^s[l&h](return x)) s; g s); f 42)
~> handle^s[l&h]((\s -> g <- (\x. handle^s[l&h](return x)) s; g s) 42)
~> handle^s[l&h](g <- (\x. handle^s[l&h](return x)) 42; g 42)
~> handle^s[l&h](g <- handle^s[l&h](return 42); g 42)
~> handle^s[l&h](g <- (return \s -> return 42); g 42)
~> handle^s[l&h]((\s -> return 42) 42)
~> handle^s[l&h](return 42)
~> return 42

-- problem with using lists of handlers:
handle(/\s. new State@s {h1} as r1 in (x <- r1#get (); new State@s as r2 in (y <- r2#get (); return (x + y))))
~> handle^s[](new State@s {h1} as r1 in (x <- r1#get (); new State@s as r2 in (y <- r2#get (); return (x + y))))
~> handle^s[l1&h1](x <- (inst l1)#get (); new State@s as r2 in (y <- r2#get (); return (x + y)))
~> handle^s[l1&h1](x <- (inst l1)#get (); new State@s as r2 in (y <- r2#get (); return (x + y)))
~> handle^s[l1&h1](f <- (return \s -> g <- (\x. handle^s[l1&h1](new State@s as r2 in (y <- r2#get (); return (x + y)))) s; g s); f 1)
~> handle^s[l1&h1]((\s -> g <- (\x. handle^s[l1&h1](new State@s as r2 in (y <- r2#get (); return (x + y)))) s; g s) 1)
~> handle^s[l1&h1](g <- (\x. handle^s[l1&h1](new State@s as r2 in (y <- r2#get (); return (x + y)))) 1; g 1)
~> handle^s[l1&h1](g <- handle^s[l1&h1](new State@s as r2 in (y <- r2#get (); return (1 + y))); g 1)
~> handle^s[l1&h1](g <- handle^s[l1&h1, l2&h2](y <- (inst l2)#get (); return (1 + y)); g 1)
~> handle^s[l1&h1](g <- handle^s[l1&h1, l2&h2](f <- (return \s -> g <- (\y. handle^s[l1&h1, l2&h2](return (1 + y))) (); g s'); f 2); g 1)
~> handle^s[l1&h1](g <- handle^s[l1&h1, l2&h2]((\s -> g <- (\y. handle^s[l1&h1, l2&h2](return (1 + y))) (); g s') 2); g 1)
~> handle^s[l1&h1](g <- handle^s[l1&h1, l2&h2](g' <- (\y. handle^s[l1&h1, l2&h2](return (1 + y))) 2; g' 2); g 1)
~> handle^s[l1&h1](g <- handle^s[l1&h1, l2&h2](g' <- handle^s[l1&h1, l2&h2](return (1 + 2)); g' 2); g 1) -- use right-most handler in list to handle: return (1 + 2)
~> handle^s[l1&h1](g <- handle^s[l1&h1, l2&h2](g' <- (return \s -> return (1 + 2)); g' 2); g 1)
~> handle^s[l1&h1](g <- handle^s[l1&h1, l2&h2]((\s -> return (1 + 2)) 2); g 1)
~> handle^s[l1&h1](g <- handle^s[l1&h1, l2&h2](return (1 + 2)); g 1) -- PROBLEM: which handler to use to handle (return (1 + 2))
-- semantically we want to use h1 but above we used the right-most handler h2.

-- testing the type system
handle(/\s. return 5) : Int!{}
~> handle^s'(return 5) : Int!{}
~> return 5 : Int!{}

f:Inst s Flip |- f#flip() : Bool!{Flip@s}

h = flip () k -> k True, return x -> return x, finally x -> return x

|-(Bool,Bool,{Flip@s}) h : Bool!{Flip@s}

new Flip@s h as f in f#flip() : Bool!{Flip@s}

handle(/\s. new Flip@s { h } as f in f@flip ()) : Bool!{}
~> handle^s(new Flip@s { h } as f in f@flip ()) : Bool!{}
~> handle^s(handle^l { h }(inst(l)@flip())) | l := (s, Flip) : Bool!{}
~> handle^s(return True) : Bool!{}
~> return True : Bool!{}
