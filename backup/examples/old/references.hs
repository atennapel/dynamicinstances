-- In this example we define ML-style references 
-- using dynamic instances, similar to how they
-- are defined in the "Eff directly in OCaml" paper.

-- Consider a polymorphic State effect
-- with the usual get and put operations.
effect State t {
  get : () -> t
  put : t -> ()
}

-- We can define instances of this effect to be
-- references.
type alias Ref t = Inst (State t)

-- We can define the usual semantics for the
-- state effect using the following handler
-- (We are using parameterized handlers as in Koka).
-- The function takes an initial value and a reference
-- and returns a handler that handles the state
-- effect on the given reference. 
state : t -> Ref t -> (<State t> r => r)
state v r = handler v {
  r#get v () k -> k v v
  r#put _ v k -> k v ()
}

-- We now introduce an effect to allocate references.
-- The operation ref takes an initial value and returns
-- a reference.
effect RefAlloc {
  ref : t -> Ref t
}

-- We can handle RefAlloc for every ref operation by
-- creating a new instance of the State effect and
-- wrapping the continuation with the state handler.
handleRefs : <RefAlloc> t => t
handleRefs = handler {
  ref v k ->
    i = new State;
    with (state v i) handle (k i)
}

-- We can now write a program that creates and uses
-- references.
program1 : Int -> <RefAlloc> (Ref Int, Int)
program1 v =
  r1 <- ref v;
  x <- r1#get ();
  r2 <- ref x;
  r1#put (x + 1);
  (r2, x)

-- We can handle all the references at once using
-- handleRefs. Note that we get back a reference
-- but this reference no longer has any value
-- associated with it, because we now have
-- access to it outside of the scope of the handler.
program1result : () -> (Ref Int, Int) 
program1result () =
  with handleRefs handle (program1 10)

-- To stop references from escape their scope
-- we could annotate a handler to be implicit
-- such that on the top-level the handler will be applied.
-- This is similar to resources in Eff.
implicit handler handleRefs
