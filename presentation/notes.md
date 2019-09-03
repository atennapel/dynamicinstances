- What are effects
  - explain pure vs impure
  - advantages of pure code
  - need for impure code
- Algebraic effects and handlers
  - what are they and why are they useful
  - Algebraic effects
  - Handlers
  - Dynamic instances
- Miro
  - effect scopes
  - creating instances
  - using instances
  - runscope
- Semantics
  - show the intermediate forms
  - show some rules and example program
- Type system
  - show most important rules
  - Type safety problems
- Questions

# Preface
Thank you all for being here
Welcome to my thesis defence
The plan today is as follows
First I will give a presentation of my work for about 30 minutes
Then you will have the chance to ask some questions
After that the commitee and me will go somewhere else for me to defend my thesis
And finally we'll be back and my final grade will be given

# Cover slide
The title of my thesis is "A type system for dynamic instances"
In order to explain what that means I will start broadly before zooming in on my contribution

# Outline
First I will talk about what I mean when I talk about effects and what the issues with them are
Then I will talk about algebraic effects and handlers, which is a way to deal with effects
I will show some examples and talk about a limitation of algebraic effects
Then I will continue with Miro, which is my proposed solution to that limitation
I will give some example programs in Miro and show how we can express some things we could not before
I will then show some parts of the semantics, which is the way that Miro programs can be run
Lastly I will give a type system for Miro, which makes sure that there will be no runtime errors
And I will talk about issues I encountered when trying to prove type safety

# Effects
Side-effects (also just called effects) are everywhere in programming.
<show example in C with many side-effects>
In this function we can see many examples
- mutable state
- input/output
Anything that a function does except computing some results from input is a side-effect

<show example of pure function>
We call a function with side-effects impure and a function without effects pure
A pure function will always have the same result for the same inputs,
they only use the arguments that they are given and no other global state,
and the only observable effect is the computation of the result of the function itself.

This deterministic behaviour makes pure functions easier to understand, debug and test, than impure functions.
We do not have to keep track of global state, mutations or mock anything
We can always test the function in isolation of the rest of the application

Of course effects are necessary for most applications.
We want to get user input and display things on the screen.
We want to make network requests.
So our programs will have some impure parts
The goal is then to split the pure and impure parts and maximize the pure ones.

There are many research papers and programming languages trying to tackle the problem
of giving the user more control over the pure and impure parts of their programs
I will now zoom in and focus on one such approach

# Algebraic effects and handlers
Algebraic effects and handlers are a structured way to introduce effects to a language.

```
effect State {
  get : () -> Int
  put : Int -> ()
}
```
Here we see the definition of an algebraic effect.
We are defining global mutable integer state.
An algebraic effect consists of operations, in this case: get and put.
Each operation gets a type, get takes a unit value (nothing) and returns an integer.
Put takes an integer and returns unit.
An algebra usually also has some equations but those are often ignored with algebraic effects.
Notice also how we are not giving an implementation of this effect, we are only giving the interface of the operations one can use to use the State effect.

```
postInc : Int!{State}
postInc =
  x <- get ();
  put (x + 1);
  return x
```
We can now use these operations in a function.
This computation gets the current value from the global state.
Sets the global state to that value incremented and returns the old value.
From the type we can see the computation returns an integer value but uses the State effect to do it (we call that an effect annotation).
Using postInc will not actually do anything at this point, it
returns a kind of suspended computation because we have not given any semantics for the operations.

```
handled : (Int, Int)
handled =
  f <- handle (postInc) {
    get () k -> return (\s -> (f <- k s; return f s))
    put v k -> return (\s -> (f <- k (); return f v))
    return v -> return (\s -> return (s, v))
  };
  f 42 // result = (43, 42)
```
Using the handle construct we can give semantics for operations.
In this example we are defining what should happen when get and put are called and when we reach "return".
For each operation we get the value argument that was given when the operation was called and continuation (named k here).
The continuation is "the rest of the computation", what happens after the operation is called.

We can decided how to use this continuation, for example with exceptions we might have a "throw" operation, throwing an exception, in that case we might not want to call the continuation at all, since it might not make sense to continue.
We can also call the continuation multiple times, for example we could continue a computation with different values and collect all the results after. This is useful for logic programming for example.

In our case we handle the State effect similarly to how the State monad is defined in Haskell. We transform the computation into a function that takes the initial value for
our global state and returns the result of the computation.

In the case of get we call the continuation with the current state "s".
And call the resulting state function with "s" again, not changing the state.

In the case of put we call the continuation with unit (as per the interface for State).
And then call the resulting state function with "v", which is the argument given when
put was called, so we update the state value to "v".

When we reach "return" (the end of the computation), we return a tuple of the current
state value and the final result

In this example we handle "postInc" and get back a function from Int -> Int
We call this function with 42, which results in a tuple of 43 (final value of the state)
and 42 (final result of the computation).

Notice how the type no longer has an effect annotation, the result is pure,
all operations are handled.

If there were still unhandled operations and we did not have a type system
that keeps track of the effect we would get a runtime error

Also you can imagine a language could have native handlers for things like IO.
Handling printline operations and so on. Like how Haskell handles the IO monad

One big selling point of algebraic effects are their composability.
We can freely intertwine operations from different effects:
```
effect Exception {
  throw : String -> Void
}

errorIf42 : Int!{State, Exception}
errorIf42 =
  x <- get ();
  if x == 42 then
    throw "The state is 42!"
  else
    return x + 1
```
*Explain exception interface*

This useless computation throws an error if the global state is 42 and else increments.
From the type we can see that the computation uses both the State and Exception effects.

```
handled : (Int, Int)!{Exception}
handled =
  f <- handle (errorIf42) {
    get () k -> return (\s -> (f <- k s; return f s))
    put v k -> return (\s -> (f <- k (); return f v))
    return v -> return (\s -> return (s, v))
  };
  f 42
```
We can now handle the effects seperately, here we only handle the State
effect but as you can see from the type the Exception effect remains

So algebraic effects and handlers give us a nice and composable way
to add effects to languages.
Now I will focus on a limitation of algebraic effects that I address in my thesis

# Limitations/dynamic instances
```
postInc : Int!{State}
postInc =
  x <- get ();
  put (x + 1);
  return x
```
Looking at the "postInc" example again we can see that we are dealing
with a global implicit state.
For many applications we want multiple reference cells, dynamically allocated.
Another example is files or communication channels,
we could have receive and send operations, but that would imply we'd have
a single global already open file, when we actually want to be able to
manipulate multiple files and channels, which are opened dynamically.

The Eff programming language solved this problem by introduction dynamic effect instances:
```
factorialLoop : Inst State -> Int -> Int!{State}
factorialLoop ref n =
  if n == 0 then
    ref#get ()
  else
    x <- ref#get();
    ref#put (x * n);
    factorialLoop ref (n - 1)

factorial : Int -> Int
factorial n =
  ref <- new State;
  statefn <- handle#ref (factorialLoop ref n) {
    get () k -> return (\s -> (f <- k s; return f s))
    put v k -> return (\s -> (f <- k (); return f v))
    return v -> return (\s -> return v)
  };
  statefn 1 -- use 1 as the initial value of ref
```
Here we are calculating the factorial of a number by repeatedly multiplying
a reference cell with an integer.

In the factorial function we are dynamically creating a new instance of State
which we call "ref".
This instance is seperate from all other State instances
and can be handled seperatedly
We pass our fresh instance "ref" to factorialLoop, which can use the instance
by directly calling operations on it using the hash-operator.
We can then handle the state operations as before but we have to say what
instance we want to handle.
*needs better explanation*

So with these effect instances we can have multiple, independent, and dynamically
allocated instances of
an effect, which we can also handle independently.

The problem with these effect instances is that they may escape the scope of their handler.
```
escape : Inst State -> (() -> Int!{State})!{State}
escape ref =
  return \() -> ref#get ()

escaped : () -> Int!{State}
escaped =
  ref <- new State;
  statefn <- handle#ref (escape ref) {
    get () k -> return (\s -> (f <- k s; return f s))
    put v k -> return (\s -> (f <- k (); return f v))
    return v -> return (\s -> return v)
  };
  fn <- statefn 0;
  return fn
```
Here the "escape" computation returns a closure that calls an operation on "ref"
The handler will not handle this operation call, since it is inside of a closure
So in the end we get back a function that calls an operation on an instance we do not
have access anymore outside of "escaped".
So we can never handle this operation resulting in a runtime error.
In this example its easy to see the operation escapes its scope,
but its not always statically possible to do so.

So this was the goal of my thesis.
Restricting these dynamic instances so that we can be sure we have handled all of them.

# Miro (examples/effect scopes)
I will now introduce the calculus I designed named Miro.
Which has dynamic effect instances in a more restricted form, in order make sure
that all operation calls will be handled.

```
effect State {
  get : () -> Int
  put : Int -> ()
}

ref : forall s. Int -> (Inst s State)!{s}
ref [s] v =
  new State@s {
    get () k -> \st -> k st st
    put st' k -> \st -> k () st'
    return x -> \st -> return x
    finally f -> f v
  } as x in return x
```
In the example we define the State effect again, notice how the effect interface stays the same as before.
Then we define a function named "ref" which dynamically creates a new State instance.
This State instance functions basically the same as a mutable reference would
in imperative languages.
Looking at the type we can see things are a little more complicated than before
we have this universally quantified type "forall s."
This s is a type variable that represents an "effect scope"
An effect scope groups together effect instances.
We can read the type annotation as:
"for every effect scope s, given an initial value of type Int (initial value of ref),
we return an effect instance of State in s, and we may perform effects in s"
In the definition we also explicitly mention the type variable "s".
And the initial value "v".

with "new" we can create new instances in Miro.
When creating a new instance we have to give the effect that
the instance is of, the effect scope we are creating the instance in
and a handler for the instance.
we name the new instance "x" which can be used in the body of the "new" construct
in this case we simply return the instance.

the handler itself does the same thing as before when we implemented the State handler.
it transforms the computation to a function that expects an initial state.
what's new here is that we also have a "finally" case, which gets executed after the handler is done.
we use this finally case to run the state function with the initial value given to "ref".

We can also write functions using instances:
```
postInc : forall s. Inst s State -> Int!{s}
postInc [s] inst =
  x <- inst#get();
  inst#put(x + 1);
  return x
```
Here is the same "postInc" function as before, but written in Miro.
This time though it acts on a specific State instance instead of on a global implicit state.
Again the function is universally quantified over the specific effect scope.
So this function works on any effect scope.
From the type we can see "for any effect scope s and a State instance in s, we return an integer and may perform effects in s doing so"
The function itself is the same as before but now we call the operations on the instance using the hash-operator.

Now to actually create the instances and perform the operations on them,
we have to provide a concrete effect scope.
This is done with the "runscope" construct.
```
result : Int
result = -- result = 3
  runscope(s1 ->
    r1 <- ref [s1] 1;
    r2 <- ref [s1] 2;
    x <- postInc [s1] r1;
    y <- r2#get ();
    r2#put(x + y);
    z <- r2#get();
    return z)
```
With runscope we can create a new effect scope and run computations on the scope.
When runscope is called, any instance creation in usage on that scope will actually be performed.
*explain example*
Notice from the type that "result" is pure, all operation calls will be handled.
runscope make sure that no effects in its scope can escape, the resulting computation
will be pure with regards to that scope.

```
result : Int
result =
  runscope(s1 ->
    r1 <- ref [s1] 10;
    ret <- runscope(s2 ->
      r2 <- ref [s2] 20;
      x <- postInc [s2] r2;
      r1#put(x);
      return x);
    y <- r1#get ();
    return y) -- result is 20
```
runscopes can also be nested, any effect on an outer scope will pass through the inner scope.
*short explanation needed, out of time for long one*

These are all the new constructs in Miro.
With these we can simulate mutable references as seen in imperative languages,
something that is not possible with regular algebraic effects
we also guarantee that instances will not be used outside of their scope,
so runscope can encapsulate effects, from the outside we cannot tell if a function uses some effect.
This is similar to how safety works for the ST monad in Haskell.

*MUTABLE VECTOR SHUFFLING EXAMPLE IF TIME*

# Semantics
*show core language*
*show example program with semantics*

# Type system and issues
*show important typing rules*

*show type safety theorem and preservation*
Initially my goal was to also prove type safety
in order to gain certainty that the system is actually type safe.
*explain theorem*
Type safety is usually proven via a preservation lemma
*explain preservation*
Here is where I ran in to problems, in that I found a counter-example
*show counter-example derivation*

We end up with an instance that has escaped its scope
This instance is not actually used, so it will not result in a program getting stuck.
So for the semantics it's not actually a problem
But for the typing rules it is. We cannot typecheck "inst(l)", since l is not in scope anymore.

So I conjecture that Miro is typesafe, since the type system will
ensure that any escape instance is unused in a closure
But we cannot prove this using the typing rules we have now.

We believe the typing rules for the intermediate forms are the main problem
They will probably need to be different
One approach is for the semantics to keep track of a global store of instance locations
which is then also used by the typing rules, but this does not
straightforwardly solve the problems because the type of an instance depends on an effect scope which may be out of scope.

# Conclusion
So in conclusion, I have shown how Miro allows for the definition of
mutable references, which was not possible with regular algebraic effects
I have also shown why type safety is difficult to prove
thank you for listening, please see my thesis for more details
are there any questions?
