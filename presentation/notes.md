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
  - running instances
- Semantics
  - show the intermediate forms
  - show some rules
- Type system
  - 
  - Type soundness
- Future work
  - maybe not?
  - show global scope idea
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
by directly calling operations on it.
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


# Semantics
# Type system and issues
# Conclusion
