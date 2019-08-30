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
And finally my final grade will be given

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
We always test the function in isolation

Of course effects are necessary for most applications.
We want to get user input and display things on the screen.
We want to make network requests.
So our programs will have some impure parts
The goal is then to split the pure and impure parts and maximize the pure ones.

There are many research papers and programming languages trying to tackle the problem
of giving the user more control over the pure and impure parts of their programs
I will now focus on one such approach

# Algebraic effects and handlers

