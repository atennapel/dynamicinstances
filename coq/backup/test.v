From stdpp Require Import fin_collections gmap.

Definition annot := positive.
Notation annots := (gset annot).

Lemma foo : forall x y z : annot, forall X : annots,
  {[ x ]} ∪ ∅ ∪ {[ y ]} ∪ X= {[ x ; y ]} ∪ X.
Proof. set_solver. Qed.

(* Notations are overloaded, so in the below it's not clear what
kind of set implementation with annot keys we use. We thus have
to put a type annotation `: annots` somewhere to make that clear. *)
Lemma bar : forall x y z : annot,
  {[ x ]} ∪ (∅:annots) ∪ {[ y ]} = {[ x ; y ]}.
Proof. set_solver. Qed.

