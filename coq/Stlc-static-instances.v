Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.
Require Import Util.
From stdpp Require Import fin_collections gmap.

(* effects and instances *)
Definition eff := nat.
Notation effs := (gset eff).

Definition inst := nat.
Notation insts := (gset inst).

Definition op := nat.
Notation ops := (gset op).

Record annot := Annot {
  annot_inst : inst;
  annot_op : op;
}.

Instance annot_eq_dec : EqDecision annot.
Proof. solve_decision. Defined.

Instance annot_countable : Countable annot.
Proof.
  apply (inj_countable' (fun a => (annot_inst a, annot_op a))
                        (fun '(n,o) => Annot n o)).
  by intros [].
Qed.

Notation annots := (gset annot).

(* ast *)
Inductive ty : Type :=
  | tarr : ty -> dirty -> ty
  | tunit : ty
  | thandler : dirty -> dirty -> ty
  | tinst : eff -> insts -> ty
with dirty : Type :=
  | dty : ty -> annots -> dirty.

Scheme ty_mut_ind := Induction for ty Sort Prop
  with dirty_mut_ind := Induction for dirty Sort Prop.
Combined Scheme ty_dirty_mutind from ty_mut_ind, dirty_mut_ind.

Inductive val : Type :=
  | unit : val
  | vinst : inst -> val
  | var : nat -> val
  | abs : comp -> val
  | handler : comp -> handlerlist -> val
with comp : Type :=
  | ret : val -> comp
  | app : val -> val -> comp
  | do : comp -> comp -> comp
  | opc : val -> op -> val -> comp -> comp
  | handle : val -> comp -> comp
with handlerlist : Type :=
  | hnil : handlerlist
  | hcons : val -> op -> comp -> handlerlist -> handlerlist.

Scheme val_mut_ind := Induction for val Sort Prop
  with comp_mut_ind := Induction for comp Sort Prop
  with handlerlist_mut_ind := Induction for handlerlist Sort Prop.
Combined Scheme ast_mutind from val_mut_ind, comp_mut_ind, handlerlist_mut_ind.

(* effect environment *)
Record env := Env {
  env_effs : effs;
  env_ops : eff -> ops;
  env_insts : eff -> insts;
  env_paramty : op -> ty;
  env_returnty : op -> ty;
}.

(* substitution *)
Fixpoint shiftval' (d:nat) (c:nat) (t:val) : val :=
  match t with
  | unit => t
  | vinst i => t
  | var k => if k <? c then t else var (k + d)
  | abs t' => abs (shiftcomp' d (S c) t')
  | handler cr hl => handler (shiftcomp' d (S c) cr) (shifthandlerlist' d c hl)
  end
with shiftcomp' (d:nat) (c:nat) (t:comp) : comp :=
  match t with
  | ret t' => ret (shiftval' d c t')
  | app t1 t2 => app (shiftval' d c t1) (shiftval' d c t2)
  | do t1 t2 => do (shiftcomp' d c t1) (shiftcomp' d (S c) t2)
  | opc vi o v t => opc (shiftval' d c vi) o (shiftval' d c v) (shiftcomp' d (S c) t)
  | handle v t => handle (shiftval' d c v) (shiftcomp' d c t)
  end
with shifthandlerlist' (d:nat) (c:nat) (t:handlerlist) : handlerlist :=
  match t with
  | hnil => t
  | hcons vi o co r => hcons (shiftval' d c vi) o (shiftcomp' d (S (S c)) co) (shifthandlerlist' d c r)
  end.

Definition shiftval d t := shiftval' d 0 t.
Definition shiftcomp d t := shiftcomp' d 0 t.
Definition shifthandlerlist d t := shifthandlerlist' d 0 t.

Hint Unfold shiftval.
Hint Unfold shiftcomp.
Hint Unfold shifthandlerlist.

Fixpoint substval' (j:nat) (s:val) (t:val) : val :=
  match t with
  | unit => t
  | vinst i => t
  | var k => if k =? j then s
              else if k <? j then t else var (pred k)
  | abs t' => abs (substcomp' (S j) (shiftval 1 s) t')
  | handler cr hl => handler (substcomp' (S j) (shiftval 1 s) cr) (substhandlerlist' j s hl)
  end
with substcomp' (j:nat) (s:val) (t:comp) : comp :=
  match t with
  | ret t' => ret (substval' j s t')
  | app t1 t2 => app (substval' j s t1) (substval' j s t2)
  | do t1 t2 => do (substcomp' j s t1) (substcomp' (S j) (shiftval 1 s) t2)
  | opc vi o v t => opc (substval' j s vi) o (substval' j s v) (substcomp' (S j) (shiftval 1 s) t)
  | handle v t => handle (substval' j s v) (substcomp' j s t)
  end
with substhandlerlist' (j:nat) (s:val) (t:handlerlist) : handlerlist :=
  match t with
  | hnil => t
  | hcons vi o co r => hcons (substval' j s vi) o (substcomp' (S (S j)) (shiftval 2 s) co) (substhandlerlist' j s r)
  end.

Definition substval s t := substval' 0 s t.
Definition substcomp s t := substcomp' 0 s t.
Definition substhandlerlist s t := substhandlerlist' 0 s t.

Hint Unfold substval.
Hint Unfold substcomp.
Hint Unfold substhandlerlist.

(* semantics *)
Definition value c := exists v, c = ret v.

Hint Unfold value.

Inductive opcase : handlerlist -> annot -> comp -> Prop :=
  | O_Head : forall i o co r,
    opcase (hcons (vinst i) o co r) (Annot i o) co
  | O_Tail : forall i i' o o' co co' r,
    (Annot i o) <> (Annot i' o') ->
    opcase r (Annot i o) co' ->
    opcase (hcons (vinst i') o' co r) (Annot i o) co'.

Reserved Notation "c1 '===>' c2" (at level 40).

Inductive step : comp -> comp -> Prop :=
  | S_AppAbs : forall t1 t2,
    (app (abs t1) t2) ===> substcomp t2 t1
  | S_DoReturn : forall v t,
    do (ret v) t ===> substcomp v t
  | S_Do : forall t1 t1' t2,
    t1 ===> t1' ->
    do t1 t2 ===> do t1' t2
  | S_DoOp : forall vi o v c1 c2,
    do (opc vi o v c1) c2 ===> opc vi o v (do c1 (shiftcomp' 1 1 c2))
  | S_Handle : forall cr hl c c',
    c ===> c' ->
    handle (handler cr hl) c ===> handle (handler cr hl) c'
  | S_HandleReturn : forall cr hl v,
    handle (handler cr hl) (ret v) ===> substcomp v cr
  | S_HandleOp1 : forall cr i o co hl v c,
    opcase hl (Annot i o) co ->
    handle (handler cr hl) (opc (vinst i) o v c) ===>
      substcomp v
        (substcomp (abs (handle (shiftval 2 (handler cr hl)) (shiftcomp' 1 1 c))) co)
  | S_HandleOp2 : forall cr hl i o v c,
    (forall co, ~(opcase hl (Annot i o) co)) ->
    handle (handler cr hl) (opc (vinst i) o v c) ===>
      opc (vinst i) o v (handle (shiftval 1 (handler cr hl)) c)

where "c1 '===>' c2" := (step c1 c2).

Hint Constructors step.

Definition relation (X: Type) := X->X->Prop.
Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Notation multistep := (multi step).
Notation "t1 '===>*' t2" := (multistep t1 t2) (at level 40).

(* subtyping *)
Definition context := list ty.

Inductive sub_ty : ty -> ty -> Prop :=
  | U_TUnit :
    sub_ty tunit tunit
  | U_TArr : forall t1 t2 t1' t2',
    sub_ty t1' t1 ->
    sub_dirty t2 t2' ->
    sub_ty (tarr t1 t2) (tarr t1' t2')
  | U_TInst : forall e is is',
    is ⊆ is' ->
    sub_ty (tinst e is) (tinst e is')
  | U_THandler : forall t1 t2 t1' t2',
    sub_dirty t1' t1 ->
    sub_dirty t2 t2' ->
    sub_ty (thandler t1 t2) (thandler t1' t2')
with sub_dirty : dirty -> dirty -> Prop :=
  | U_Dirty : forall t t' e e',
    sub_ty t t' ->
    e ⊆ e' ->
    sub_dirty (dty t e) (dty t' e').

Scheme sub_ty_mut_ind := Induction for sub_ty Sort Prop
  with sub_dirty_mut_ind := Induction for sub_dirty Sort Prop.
Combined Scheme sub_mutind from sub_ty_mut_ind, sub_dirty_mut_ind.

Hint Constructors sub_ty.
Hint Constructors sub_dirty.

Inductive sub_context : context -> context -> Prop :=
  | U_Nil :
    sub_context nil nil
  | U_Cons : forall t t' r r',
    sub_ty t t' ->
    sub_context r r' ->
    sub_context (t :: r) (t' :: r').

Hint Constructors sub_context.

(* typing rules *)
Reserved Notation "Env ',' Gamma '|-' t 'in' T" (at level 40).
Reserved Notation "Env ',' Gamma '|-c' t 'in' T" (at level 40).
Reserved Notation "Env ',' Gamma '|-h' t 'in' T ';' A" (at level 40).

Definition s_union (d':annots) (is:insts) (o:op) (d'':annots) :=
  (exists i, is = {[i]} /\ d'' = (union d' {[Annot i o]})) \/
  (~(exists i, is = {[i]}) /\ d'' = d').

Hint Unfold s_union.

Inductive has_type_val : env -> context -> val -> ty -> Prop :=
  | T_Unit : forall E G,
    E,G |- unit in tunit
  | T_Abs : forall E G c t1 t2,
    E,(t1 :: G) |-c c in t2 ->
    E,G |- abs c in tarr t1 t2
  | T_Inst : forall E G i e is,
    is ⊆ env_insts E e ->
    i ∈ is ->
    E,G |- vinst i in tinst e is
  | T_Handler : forall E G cr hl a b e e' e'',
    E,(a :: G) |-c cr in (dty b e') ->
    E,G |-h hl in (dty b e') ; e'' ->
    e ⊆ (union e'' e') ->
    E,G |- handler cr hl in thandler (dty a e) (dty b e')
  | T_SubVal : forall E G v T T',
    E,G |- v in T ->
    sub_ty T T' ->
    E,G |- v in T'

where "Env ',' Gamma '|-' t 'in' T" := (has_type_val Env Gamma t T)

with has_type_comp : env -> context -> comp -> dirty -> Prop :=
  | T_Return : forall E G v t e,
    E,G |- v in t ->
    E,G |-c ret v in (dty t e)
  | T_App : forall E G v1 v2 t1 t2,
    E,G |- v1 in (tarr t1 t2) ->
    E,G |- v2 in t1 ->
    E,G |-c app v1 v2 in t2
  | T_Do : forall E G c1 c2 a b e,
    E,G |-c c1 in (dty a e) ->
    E,(a :: G) |-c c2 in (dty b e) ->
    E,G |-c do c1 c2 in (dty b e)
  | T_Op : forall E G vi o v c a d e is,
    E,G |- vi in tinst e is ->
    o ∈ env_ops E e ->
    E,G |- v in (env_paramty E o) ->
    E,(env_returnty E o :: G) |-c c in (dty a d) ->
    (forall i, i ∈ is -> (Annot i o) ∈ d) ->
    E,G |-c opc vi o v c in (dty a d)
  | T_Handle : forall E G v c a b,
    E,G |- v in thandler a b ->
    E,G |-c c in a ->
    E,G |-c handle v c in b
  | T_SubComp : forall E G c t t',
    E,G |-c c in t ->
    sub_dirty t t' ->
    E,G |-c c in t'

where "Env ',' Gamma '|-c' t 'in' T" := (has_type_comp Env Gamma t T)

with has_type_handlerlist : env -> context -> handlerlist -> dirty -> annots -> Prop :=
  | T_Nil : forall E G t,
    E,G |-h hnil in t ; empty
  | T_Cons : forall E G v o c r t e is d d' d'',
    E,G |- v in tinst e is ->
    o ∈ env_ops E e ->
    E,(tarr (env_returnty E o) t :: env_paramty E o :: G) |-c c in t ->
    E,G |-h r in t ; d' ->
    s_union d' is o d'' /\ d ⊆ d'' ->
    E,G |-h (hcons v o c r) in t ; d

where "Env ',' Gamma '|-h' t 'in' T ';' A" := (has_type_handlerlist Env Gamma t T A).

Scheme has_type_val_mut_ind := Induction for has_type_val Sort Prop
  with has_type_comp_mut_ind := Induction for has_type_comp Sort Prop
  with has_type_handlerlist_mut_ind := Induction for has_type_handlerlist Sort Prop.
Combined Scheme has_type_mut_ind from has_type_val_mut_ind, has_type_comp_mut_ind, has_type_handlerlist_mut_ind.

Hint Constructors has_type_val.
Hint Constructors has_type_comp.
Hint Constructors has_type_handlerlist.

(* lemmas & theorems *)
Lemma opcase_deterministic: forall hl a c,
  opcase hl a c -> (forall c', opcase hl a c' -> c = c').
Proof.
  intros.
  generalize dependent c'.
  induction H; intros.
  - inversion_try_solve H0.
    contradiction.
  - inversion_try_solve H1.
    contradiction.
    apply IHopcase.
    auto.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros; try inversion_try_solve H0.
  - apply IHstep in H4.
    rewrite H4.
    auto.
  - apply IHstep in H5.
    rewrite H5.
    auto.
  - apply opcase_deterministic with (c := co0) in H; auto.
    rewrite H.
    auto.
  - specialize (H8 co).
    contradiction.
  - specialize (H co).
    contradiction.
Qed.

Lemma subtype_reflex : (forall t, sub_ty t t) /\ (forall t, sub_dirty t t).
Proof.
  apply ty_dirty_mutind; intros; auto.
Qed.

Lemma subtype_reflex_context : forall g, sub_context g g.
Proof.
  induction g; auto.
  constructor; auto.
  apply subtype_reflex.
Qed.

Lemma subtype_context_weakening :
  (forall E G v R, E,G |- v in R -> forall G', sub_context G G' -> E,G' |- v in R) /\
  (forall E G v R, E,G |-c v in R -> forall G', sub_context G G' -> E,G' |-c v in R) /\
  (forall E G v R D, E,G |-h v in R ; D -> forall G', sub_context G G' -> E,G' |-h v in R ; D).
Proof.
  apply has_type_mut_ind; intros; auto; try constructor; auto.
  - apply H.
    constructor; auto.
    apply subtype_reflex.
  - apply T_Handler with (e'' := e''); auto.
    apply H.
    constructor; auto.
    apply subtype_reflex.
  - apply T_SubVal with (T := T); auto.
  - apply T_App with (t1 := t1); auto.
  - apply T_Do with (a := a); auto.
    apply H0.
    constructor; auto.
    apply subtype_reflex.
  - apply T_Op with (e := e) (is := is); auto.
    apply H1.
    constructor; auto.
    apply subtype_reflex.
  - apply T_Handle with (a := a); auto.
  - apply T_SubComp with (t := t); auto.
  - apply T_Cons with (e := e) (is := is) (d' := d') (d'' := d''); auto.
    apply H0.
    constructor; auto.
    + apply subtype_reflex.
    + constructor; auto.
      apply subtype_reflex.
Qed.

Lemma subtype_context_tightening :
  (forall E G v R, E,G |- v in R -> forall G', sub_context G' G -> E,G' |- v in R) /\
  (forall E G v R, E,G |-c v in R -> forall G', sub_context G' G -> E,G' |-c v in R) /\
  (forall E G v R D, E,G |-h v in R ; D -> forall G', sub_context G' G -> E,G' |-h v in R ; D).
Proof.
  apply has_type_mut_ind; intros; auto; try constructor; auto.
  - apply H.
    constructor; auto.
    apply subtype_reflex.
  - apply T_Handler with (e'' := e''); auto.
    apply H.
    constructor; auto.
    apply subtype_reflex.
  - apply T_SubVal with (T := T); auto.
  - apply T_App with (t1 := t1); auto.
  - apply T_Do with (a := a); auto.
    apply H0.
    constructor; auto.
    apply subtype_reflex.
  - apply T_Op with (e := e) (is := is); auto.
    apply H1.
    constructor; auto.
    apply subtype_reflex.
  - apply T_Handle with (a := a); auto.
  - apply T_SubComp with (t := t); auto.
  - apply T_Cons with (e := e) (is := is) (d' := d') (d'' := d''); auto.
    apply H0.
    constructor; auto.
    + apply subtype_reflex.
    + constructor; auto.
      apply subtype_reflex.
Qed.

Lemma subtype_weakening :
  (forall E G v T, E,G |- v in T -> forall T', sub_ty T T' -> E,G |- v in T') /\
  (forall E G v T, E,G |-c v in T -> forall T', sub_dirty T T' -> E,G |-c v in T') /\
  (forall E G v T D, E,G |-h v in T ; D -> forall T', sub_dirty T T' -> E,G |-h v in T' ; D).
Proof.
  apply has_type_mut_ind; intros; auto.
  - inversion_try_solve H.
    auto.
  - inversion_try_solve H0.
    constructor.
    assert (H5' := H5).
    apply H in H5'.
    apply subtype_context_tightening with (G := t1 :: G); auto.
    constructor; auto.
    apply subtype_reflex_context.
  - inversion_try_solve H.
    constructor; auto.
    

Lemma progress_effects : forall Env t T E,
  Env,nil |-c t in (dty T E) ->
  (value t \/ exists t', t ===> t') \/ (exists i o v k, t = opc (vinst i) o v k /\ (Annot i o) ∈ E).
Proof.
  remember (@nil ty) as Gamma.
  intros.
  induction H; subst; auto.
  - left. left.
    unfold value. exists v. auto.
  - left. right.
    inversion_try_solve H.
    + exists (substcomp v2 c).
      auto.
    + 
