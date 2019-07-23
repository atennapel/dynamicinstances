This directory contains formalizations in Coq of various algebraic effects systems with type-soundness proofs. <br/>
Stlc.v - STLC with DeBruijn indeces, preservation and type soundness proofs. <br/>
Stlc-comp.v - STLC with computation and value distinction (fine-grained STLC). <br/>
Stlc-eff.v - STLC-comp with effect annotations. <br/>
Stlc-algebraiceffects-1op-ops.v - algebraic effects with 1-operation handlers<br/>
Stlc-algebraiceffects-static-instances-1op-ops.v - algebraic effects with 1-operation handlers and static instances<br/>
Stlc-algebraiceffects-ops.v - algebraic effects (handlers can have more than 1 operation) <br/>

To compile:
- opam install coq (tested on 8.9.0)
- install coq-stdpp (tested with latest development version)
- `coq_makefile -f _CoqProject -o Makefile`
- `make`
- `coqc Util.v`
- `coqc Stlc.v` (or one of the other files)

