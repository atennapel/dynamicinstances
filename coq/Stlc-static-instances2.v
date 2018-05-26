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

Inductive handlerlist_value : handlerlist -> Prop :=
  | HV_Nil :
    handlerlist_value hnil
  | HV_Cons : forall i o c r,
    handlerlist_value r ->
    handlerlist_value (hcons (vinst i) o c r).

Hint Constructors handlerlist_value.

Inductive opcase : handlerlist -> annot -> comp -> Prop :=
  | O_Head : forall i o co r,
    opcase (hcons (vinst i) o co r) (Annot i o) co
  | O_Tail : forall i i' o o' co co' r,
    (Annot i o) <> (Annot i' o') ->
    opcase r (Annot i o) co' ->
    opcase (hcons (vinst i') o' co r) (Annot i o) co'.

Hint Constructors opcase.

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

Notation sub_context := (Forall2 sub_ty).

(* type wf *)
Notation wf_annot E a := (exists e,
  e ∈ env_effs E /\ annot_inst a ∈ env_insts E e /\ annot_op a ∈ env_ops E e).
Notation wf_annots E es := (forall a, a ∈ es -> wf_annot E a).

Inductive wf_ty : env -> ty -> Prop :=
  | WF_TUnit : forall E,
    wf_ty E tunit
  | WF_TArr : forall E a b,
    wf_ty E a ->
    wf_dirty E b ->
    wf_ty E (tarr a b)
  | WF_THandler : forall E a b,
    wf_dirty E a ->
    wf_dirty E b ->
    wf_ty E (thandler a b)
  | WF_TInst : forall E e is,
    e ∈ env_effs E ->
    is ⊆ env_insts E e ->
    wf_ty E (tinst e is)
with wf_dirty : env -> dirty -> Prop :=
  | WF_Dirty : forall E t es,
    wf_ty E t ->
    wf_annots E es ->
    wf_dirty E (dty t es).

Scheme wf_ty_mut_ind := Induction for wf_ty Sort Prop
  with wf_dirty_mut_ind := Induction for wf_dirty Sort Prop.
Combined Scheme wf_mut_ind from wf_ty_mut_ind, wf_dirty_mut_ind.

Hint Constructors wf_ty.

Notation wf_context E := (Forall (wf_ty E)).

(* typing rules *)
Reserved Notation "Env ',' Gamma '|-' t 'in' T" (at level 40).
Reserved Notation "Env ',' Gamma '|-c' t 'in' T" (at level 40).
Reserved Notation "Env ',' Gamma '|-h' t 'in' T ';' A" (at level 40).

Notation s_union d' is o d'' :=
  ((exists i, is = {[i]} /\ d'' = (union d' {[Annot i o]})) \/
  (~(exists i, is = {[i]}) /\ d'' = d')).

Inductive has_type_val : env -> context -> val -> ty -> Prop :=
  | T_Var : forall E G i T,
    wf_context E G ->
    nth_error G i = Some T ->
    E,G |- var i in T
  | T_Unit : forall E G,
    E,G |- unit in tunit
  | T_Abs : forall E G c t1 t2,
    wf_ty E t1 ->
    E,(t1 :: G) |-c c in t2 ->
    E,G |- abs c in tarr t1 t2
  | T_Inst : forall E G i e is,
    e ∈ env_effs E ->
    is ⊆ env_insts E e ->
    i ∈ is ->
    E,G |- vinst i in tinst e is
  | T_Handler : forall E G cr hl a b e e' e'',
    wf_ty E a ->
    E,(a :: G) |-c cr in (dty b e') ->
    E,G |-h hl in (dty b e') ; e'' ->
    e ⊆ (union e'' e') ->
    E,G |- handler cr hl in thandler (dty a e) (dty b e')
  | T_SubVal : forall E G v T T',
    wf_ty E T' ->
    E,G |- v in T ->
    sub_ty T T' ->
    E,G |- v in T'

where "Env ',' Gamma '|-' t 'in' T" := (has_type_val Env Gamma t T)

with has_type_comp : env -> context -> comp -> dirty -> Prop :=
  | T_Return : forall E G v t e,
    wf_annots E e ->
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
    wf_ty E (env_paramty E o) ->
    wf_ty E (env_returnty E o) ->
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
    wf_dirty E t' ->
    E,G |-c c in t ->
    sub_dirty t t' ->
    E,G |-c c in t'

where "Env ',' Gamma '|-c' t 'in' T" := (has_type_comp Env Gamma t T)

with has_type_handlerlist : env -> context -> handlerlist -> dirty -> annots -> Prop :=
  | T_Nil : forall E G t,
    wf_dirty E t ->
    E,G |-h hnil in t ; empty
  | T_Cons : forall E G v o c r t e is d d' d'',
    wf_ty E (env_returnty E o) ->
    wf_ty E (env_paramty E o) ->
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
Lemma opcase_dec : forall hl a,
  handlerlist_value hl ->
  (exists c, opcase hl a c) \/ (forall c, ~(opcase hl a c)).
Proof.
  induction hl; intros.
  - right.
    unfold not.
    intros.
    inversion_try_solve H.
  - destruct IHhl with (a := a).
    + inversion_try_solve H; auto.
    + destruct H0.
      inversion_try_solve H.
      inversion_try_solve H0.
      * destruct (annot_eq_dec (Annot i o) (Annot i0 o0)).
        { inversion_try_solve e.
          left.
          exists c; auto. }
        { left.
          exists x; auto. }
      * destruct (annot_eq_dec (Annot i o) (Annot i0 o0)).
        { inversion_try_solve e.
          left.
          exists c; auto. }
        { left.
          exists x; auto. }
    + inversion_try_solve H.
      induction a.
      destruct (annot_eq_dec (Annot i o) (Annot annot_inst0 annot_op0)).
      * inversion_try_solve e.
        left.
        exists c; auto.
      * right.
        unfold not.
        intros.
        inversion_try_solve H1.
        { contradiction. }
        { specialize (H0 c0).
          contradiction. }
Qed.

Lemma opcase_deterministic : forall hl a c,
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

Theorem step_deterministic :
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

Lemma sub_refl :
  (forall t, sub_ty t t) /\
  (forall t, sub_dirty t t).
Proof.
  apply ty_dirty_mutind; intros; auto;
    try (inversion_try_solve H1; constructor; auto).
Qed.

Lemma sub_trans :
  (forall b a c, sub_ty a b -> sub_ty b c -> sub_ty a c) /\
  (forall b a c, sub_dirty a b -> sub_dirty b c -> sub_dirty a c).
Proof.
  apply ty_dirty_mutind; intros; auto.
  - inversion_try_solve H1.
    inversion_try_solve H2.
    constructor; auto.
  - inversion_try_solve H.
    inversion_try_solve H0.
    auto.
  - inversion_try_solve H1.
    inversion_try_solve H2.
    auto.
  - inversion_try_solve H.
    inversion_try_solve H0.
    constructor; set_solver.
  - inversion_try_solve H0.
    inversion_try_solve H1.
    constructor; auto.
    set_solver.
Qed.

Lemma sub_context_refl : forall a,
  sub_context a a.
Proof.
  induction a; auto.
  constructor; auto.
  apply sub_refl.
Qed.

Lemma sub_context_append : forall a b c d,
  sub_context a c ->
  sub_context b d ->
  sub_context (a ++ b) (c ++ d).
Proof.
  intros.
  generalize dependent b.
  generalize dependent d.
  induction H; intros; auto.
  simpl; constructor; auto.
Qed.

Lemma gamma_wellformed : forall E G,
  wf_context E G -> (forall T, T ∈ G -> wf_ty E T).
Proof.
  induction G; intros.
  - set_solver.
  - apply Forall_cons_1 in H.
    destruct H.
    inversion_try_solve H0; auto.
Qed.

Lemma wf_context_append : forall E G G',
  wf_context E G -> wf_context E G' -> wf_context E (G ++ G').
Proof.
  induction G; intros; auto.
  inversion_try_solve H; simpl.
  constructor; auto.
Qed.

Lemma wf_annots_subset : forall E (e':annots) e,
  wf_annots E e' -> e ⊆ e' -> wf_annots E e.
Proof.
  intros.
  assert (a ∈ e').
  set_solver.
  apply H in H2.
  auto.
Qed.

Lemma wf_annots_union : forall E e (e':annots),
  wf_annots E e /\ wf_annots E e' <-> wf_annots E (union e e').
Proof.
  intros.
  split.
  - intros.
    apply elem_of_union in H0.
    destruct H.
    destruct H0; auto.
  - intros.
    split.
    + intros.
      assert (a ∈ (union e e')).
      set_solver.
      apply H in H1.
      auto.
    + intros.
      assert (a ∈ (union e e')).
      set_solver.
      apply H in H1.
      auto.
Qed.

Lemma ty_wellformed :
  (forall E G v t, E,G |- v in t -> wf_context E G -> wf_ty E t) /\
  (forall E G v t, E,G |-c v in t -> wf_context E G -> wf_dirty E t) /\
  (forall E G v t D, E,G |-h v in t ; D -> wf_context E G -> wf_dirty E t /\ wf_annots E D).
Proof.
  apply has_type_mut_ind; intros; auto.
  - apply gamma_wellformed with (T := T) in f; auto.
    rewrite elem_of_list_In.
    apply nth_error_In with (n := i); auto.
  - constructor; auto.
    constructor; auto.
    induction hl.
    + inversion_try_solve h0.
      inversion_try_solve H2.
      apply wf_annots_subset with (e' := e'); auto.
      set_solver.
    + assert (wf_context E (a :: G)); try (constructor; auto).
      apply H in H2.
      inversion_try_solve H2.
      apply H0 in H1.
      destruct H1.
      assert (wf_annots E (union e'' e')).
      apply wf_annots_union; auto.
      apply wf_annots_subset with (e' := union e'' e'); auto.
  - constructor; auto.
  - apply H in H1.
    inversion_try_solve H1; auto.
  - assert (H1' := H1).
    apply H in H1.
    inversion_try_solve H1.
    assert (wf_context E (a :: G)).
    constructor; auto.
    apply H0 in H2; auto.
  - apply H in H1.
    inversion_try_solve H1; auto.
  - split; auto.
    intros.
    set_solver.
  - assert (H2' := H2).
    apply H1 in H2.
    destruct H2.
    split; auto.
    destruct a.
    destruct H4.
    + destruct H4.
      destruct H4.
      subst.
      assert (wf_annot E (Annot x o)).
      * exists e.
        apply H in H2'.
        inversion_try_solve H2'.
        split; auto.
        simpl; split; auto.
        set_solver.
      * assert (wf_annots E (d' ∪ {[{| annot_inst := x; annot_op := o |}]})).
        { apply wf_annots_union; split; auto.
          intros.
          set_solver. }
        { apply wf_annots_subset with (e' := (d' ∪ {[{| annot_inst := x; annot_op := o |}]})); auto. }
    + destruct H4.
      subst.
      apply H1 in H2'.
      destruct H2'.
      apply wf_annots_subset with (e' := d'); auto.
Qed.

Lemma context_subtype : forall G G' i T,
  nth_error G i = Some T -> sub_context G G' -> exists T', sub_ty T T' /\ nth_error G' i = Some T'.
Proof.
  intros.
  generalize dependent i.
  induction H0; intros; auto.
  - rewrite nth_error_nil in H; inversion H.
  - induction i.
    + simpl in H1.
      inversion_try_solve H1.
      exists y; auto.
    + simpl in H1.
      apply IHForall2 in H1.
      destruct H1.
      exists x0; auto.
Qed.

Lemma context_subtype_other : forall G G' i T,
  nth_error G i = Some T -> sub_context G' G -> exists T', sub_ty T' T /\ nth_error G' i = Some T'.
Proof.
  intros.
  generalize dependent i.
  induction H0; intros; auto.
  - rewrite nth_error_nil in H; inversion H.
  - induction i.
    + simpl in H1.
      inversion_try_solve H1.
      exists x; auto.
    + simpl in H1.
      apply IHForall2 in H1.
      destruct H1.
      exists x0; auto.
Qed.

Lemma context_strengthen :
  (forall E G v T, E,G |- v in T -> wf_context E G -> forall G', sub_context G' G -> wf_context E G' -> E,G' |- v in T) /\
  (forall E G v T, E,G |-c v in T -> wf_context E G -> forall G', sub_context G' G -> wf_context E G' -> E,G' |-c v in T) /\
  (forall E G v T D, E,G |-h v in T ; D -> wf_context E G -> forall G', sub_context G' G -> wf_context E G' -> E,G' |-h v in T ; D).
Proof.
  apply has_type_mut_ind; intros; auto.
  - apply gamma_wellformed with (T := T) in H.
    assert (e' := e).
    apply context_subtype_other with (G' := G') in e; auto.
    destruct e, H2.
    apply T_SubVal with (T := x); auto.
    apply nth_error_In in e.
    rewrite elem_of_list_In; auto.
  - constructor; auto.
    apply H; auto.
    constructor; auto.
    apply sub_refl.
  - apply T_Handler with (e'' := e''); auto.
    apply H; auto.
    constructor; auto.
    apply sub_refl.
  - apply T_SubVal with (T := T); auto.
  - apply T_App with (t1 := t1); auto.
  - apply T_Do with (a := a); auto.
    apply ty_wellformed in h; auto.
    inversion_try_solve h.
    apply H0; constructor; auto.
    apply sub_refl.
  - apply T_Op with (e := e) (is := is); auto.
    apply H1; auto.
    constructor; auto.
    apply sub_refl.
  - apply T_Handle with (a := a); auto.
  - apply T_SubComp with (t := t); auto.
  - apply T_Cons with (e := e) (is := is) (d' := d') (d'' := d''); auto.
    apply H0; auto.
    constructor; auto.
    constructor; auto.
    apply ty_wellformed in h1; auto.
    destruct h1; auto.
    constructor; auto.
    constructor; auto; try apply sub_refl.
    constructor; auto.
    apply sub_refl.
    constructor; auto.
    constructor; auto.
    apply ty_wellformed in h1; auto.
    destruct h1; auto.
Qed.

Lemma tarr_implies_abs_or_var : forall E G v T,
  E,G |- v in T -> forall a b, sub_ty T (tarr a b) ->
  (exists c, v = abs c) \/ (exists i T', v = var i /\ nth_error G i = Some T' /\ sub_ty T' T).
Proof.
  intros.
  generalize dependent a.
  generalize dependent b.
  induction H; intros.
  - right. exists i, T; auto.
    split; auto.
    split; auto.
    apply sub_refl.
  - inversion H0.
  - left. exists c; auto.
  - inversion H2.
  - inversion H3.
  - assert (sub_ty T (tarr a b)).
    + apply sub_trans with (b := T'); auto.
    + apply IHhas_type_val in H3.
      destruct H3.
      * destruct H3.
        subst.
        left.
        exists x; auto.
      * right.
        destruct H3.
        exists x.
        destruct H3.
        subst.
        exists x0; auto.
        destruct H3.
        destruct H4.
        subst.
        split; auto.
        split; auto.
        apply sub_trans with (b := T); auto.
Qed.

Lemma empty_tarr_is_abs : forall E v T,
  E,[] |- v in T -> forall a b, sub_ty T (tarr a b) -> exists c, v = abs c.
Proof.
  remember (@nil ty) as G.
  intros.
  induction H; subst; auto.
  - rewrite nth_error_nil in H1; inversion H1.
  - inversion H0.
  - exists c; auto.
  - inversion H0.
  - inversion H0.
  - apply IHhas_type_val; auto.
    apply sub_trans with (b := T'); auto.
Qed.

Lemma empty_tinst_is_vinst : forall E v T,
  E,[] |- v in T -> forall e is, sub_ty T (tinst e is) -> exists i, v = vinst i /\ ~(is = empty).
Proof.
  remember (@nil ty) as G.
  intros.
  induction H; subst; auto.
  - rewrite nth_error_nil in H1; inversion H1.
  - inversion H0.
  - inversion H0.
  - exists i; auto.
    split; auto.
    inversion_try_solve H0.
    set_solver.
  - inversion H0.
  - apply IHhas_type_val; auto.
    apply sub_trans with (b := T'); auto.
Qed.

Lemma vinst_is_tinst : forall E G v T,
  E,G |- v in T -> forall i, v = vinst i ->
  exists e is, sub_ty (tinst e is) T /\ e ∈ env_effs E /\ is ⊆ env_insts E e /\ i ∈ is.
Proof.
  intros.
  generalize dependent i.
  induction H; intros; subst.
  - inversion H1.
  - inversion H0.
  - inversion H1.
  - inversion_try_solve H2.
    exists e, is.
    split; auto.
  - inversion H3.
  - assert (vinst i = vinst i); auto.
    apply IHhas_type_val in H2.
    destruct H2, H2, H2, H3, H4.
    exists x, x0.
    split; auto.
    apply sub_trans with (b := T); auto.
Qed.

Lemma abs_is_tarr : forall E G v T,
  E,G |- v in T -> forall c, v = abs c ->
  exists t1 t2, sub_ty (tarr t1 t2) T /\  wf_ty E t1 /\ E,t1::G |-c c in t2.
Proof.
  intros.
  generalize dependent c.
  induction H; intros; subst.
  - inversion H1.
  - inversion H0.
  - inversion_try_solve H1.
    exists t1, t2.
    split; auto.
    apply sub_refl.
  - inversion H2.
  - inversion H3.
  - assert (abs c = abs c); auto.
    apply IHhas_type_val in H2.
    destruct H2, H2.
    exists x, x0.
    destruct H2.
    split; auto.
    apply sub_trans with (b := T); auto.
Qed.

Lemma ret_is_dty : forall P E G c T,
  E,G |-c c in T -> wf_context E G ->
  match c with
  | ret v => forall a e, sub_dirty (dty a e) T ->
    wf_annots E e ->
    E,G |- v in a -> P
  
  end ->
  P.
Proof.
  intros.
  generalize dependent v.
  induction H; intros; subst.
  - inversion_try_solve H2.
    exists t, e.
    split. auto.
    apply sub_refl.
    split; auto.
  - inversion H2.
  - inversion H2.
  - inversion H7.
  - inversion H2.
  - apply IHhas_type_comp with (v0 := v) in H0; auto.
    destruct H0, H0, H0, H3.
    exists x, x0.
    split; auto.
    apply sub_trans with (b := t); auto.
Qed.

Lemma app_is_dty : forall E G c T,
  E,G |-c c in T -> wf_context E G -> forall c1 c2, c = app c1 c2 ->
  exists t1 t2, sub_dirty t2 T /\
    E,G |- c1 in (tarr t1 t2) /\
    E,G |- c2 in t1.
Proof.
  intros.
  generalize dependent c1.
  generalize dependent c2.
  induction H; intros; subst.
  - inversion H2.
  - inversion_try_solve H2.
    exists t1, t2.
    split; auto.
    apply sub_refl.
  - inversion H2.
  - inversion H7.
  - inversion H2.
  - apply IHhas_type_comp with (c3 := c2) (c4 := c1) in H0; auto.
    destruct H0, H0, H0, H3.
    exists x, x0.
    split; auto.
    apply sub_trans with (b := t); auto.
Qed.

Lemma handle_is_dty : forall E G c T,
  E,G |-c c in T -> wf_context E G -> forall v k, c = handle v k ->
  exists a b, sub_dirty b T /\
    E,G |- v in thandler a b /\
    E,G |-c k in a.
Proof.
  intros.
  induction H; intros; subst.
  - inversion H1.
  - inversion H1.
  - inversion H1.
  - inversion H1.
  - inversion_try_solve H1.
    exists a, b.
    split; auto.
    apply sub_refl.
  - apply IHhas_type_comp in H0; auto.
    destruct H0, H0, H0.
    exists x, x0.
    split; auto.
    apply sub_trans with (b := t); auto.
Qed.

Lemma opc_is_dty : forall E G c T,
  E,G |-c c in T -> wf_context E G -> forall vi o v k, c = opc vi o v k ->
  exists a es e is, sub_dirty (dty a es) T /\
    wf_ty E (env_paramty E o) /\
    wf_ty E (env_returnty E o) /\
    E,G |- vi in tinst e is /\
    o ∈ env_ops E e /\
    E,G |- v in (env_paramty E o) /\
    E,(env_returnty E o :: G) |-c k in (dty a es) /\
    (forall i, i ∈ is -> (Annot i o) ∈ es).
Proof.
  intros.
  generalize dependent vi.
  generalize dependent o.
  generalize dependent v.
  generalize dependent k.
  induction H; intros; subst.
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - inversion_try_solve H7.
    exists a, d, e, is.
    split; auto.
    apply sub_refl.
    split; auto.
    split; auto.
  - inversion H2.
  - apply IHhas_type_comp with (vi0 := vi) (o0 := o) (v0 := v) (k0 := k) in H0; auto.
    destruct H0, H0, H0, H0, H0, H3.
    destruct H4, H5, H6, H7, H8.
    exists x, x0, x1, x2.
    split; auto.
    apply sub_trans with (b := t); auto.
    split; auto.
    split; auto.
Qed.

Lemma do_is_dty : forall E G c T,
  E,G |-c c in T -> wf_context E G -> forall c1 c2, c = do c1 c2 ->
  exists a e b, sub_dirty (dty b e) T /\
    wf_ty E a /\
    E,G |-c c1 in dty a e /\
    E,(a::G) |-c c2 in dty b e.
Proof.
  intros.
  generalize dependent c1.
  generalize dependent c2.
  induction H; intros; subst.
  - inversion H2.
  - inversion H2.
  - inversion_try_solve H2.
    exists a, e, b.
    split; auto.
    apply sub_refl.
    split; auto.
    apply ty_wellformed in H; auto.
    inversion_try_solve H; auto.
  - inversion H7.
  - inversion H2.
  - apply IHhas_type_comp with (c3 := c2) (c4 := c1) in H0; auto.
    destruct H0, H0, H0, H0, H3.
    exists x, x0, x1.
    split; auto.
    apply sub_trans with (b := t); auto.
Qed.

Lemma handler_is_thandler : forall E G v T,
  E,G |- v in T -> wf_context E G -> forall cr hl, v = handler cr hl ->
  exists a b e e'' e', sub_ty (thandler (dty a e) (dty b e')) T /\
    wf_dirty E (dty a e) /\ e ⊆ (union e'' e') /\
    E,(a :: G) |-c cr in (dty b e') /\
    E,G |-h hl in (dty b e') ; e''.
Proof.
  intros.
  generalize dependent cr.
  generalize dependent hl.
  induction H; intros; subst.
  - inversion H2.
  - inversion H1.
  - inversion H2.
  - inversion H3.
  - inversion_try_solve H4.
    exists a, b, e, e'', e'.
    split; auto.
    constructor; auto; constructor; auto; apply sub_refl.
    split; auto.
    apply ty_wellformed in H2; auto.
    destruct H2.
    constructor; auto.
    inversion_try_solve H2.
    apply wf_annots_subset with (e' := union e'' e'); auto.
    rewrite <- wf_annots_union.
    split; auto.
  - apply IHhas_type_val with (hl0 := hl) (cr0 := cr) in H0; auto.
    destruct H0, H0, H0, H0, H0, H0, H3.
    exists x, x0, x1, x2, x3.
    split; auto.
    apply sub_trans with (b := T); auto.
Qed.

Lemma var_typing : forall E G v T,
  E,G |- v in T -> forall n, v = var n ->
  exists T', sub_ty T' T /\ nth_error G n = Some T'.
Proof.
  intros.
  generalize dependent n.
  induction H; intros; subst.
  - inversion_try_solve H1.
    exists T; auto.
    split; auto.
    apply sub_refl.
  - inversion H0.
  - inversion H1.
  - inversion H2.
  - inversion H3.
  - assert (var n = var n); auto.
    apply IHhas_type_val in H2; auto.
    destruct H2, H2.
    exists x.
    split; auto.
    apply sub_trans with (b := T); auto.
Qed.

Lemma opc_not_empty : forall E c T,
  E,[] |-c c in T -> forall i o v c' t e, c = opc i o v c' ->
  sub_dirty T (dty t e) -> exists j, i = vinst j /\ e <> empty.
Proof.
  remember (@nil ty) as G.
  intros.
  induction H; subst; auto.
  - inversion H0.
  - inversion H0.
  - inversion H0.
  - apply empty_tinst_is_vinst with (e := e0) (is := is) in H3; auto.
    destruct H3, H3.
    subst.
    inversion_try_solve H0.
    exists x.
    split; auto.
    inversion_try_solve H1.
    set_solver.
  - inversion H0.
  - apply IHhas_type_comp; auto.
    apply sub_trans with (b := t'); auto.
Qed.

Lemma sub_tunit : forall T,
  (sub_ty T tunit -> T = tunit) /\ (sub_ty tunit T -> T = tunit).
Proof.
  intros.
  split; intros; inversion_try_solve H; inversion_try_solve H0.
Qed.

Lemma unit_is_tunit : forall E G v T,
  E,G |- v in T -> v = unit -> T = tunit.
Proof.
  intros.
  induction H; subst; auto; try inversion H0.
  assert (unit = unit); auto.
  apply IHhas_type_val in H0.
  subst.
  apply sub_tunit; auto.
Qed.

Lemma empty_handler_type_value : forall E hl T D,
  E,[] |-h hl in T ; D -> handlerlist_value hl.
Proof.
  remember (@nil ty) as G.
  intros.
  induction H; subst; auto.
  apply empty_tinst_is_vinst with (e := e) (is := is) in H1.
  - destruct H1, H1; subst; auto.
  - apply sub_refl.
Qed.

Lemma empty_thandler_is_handler : forall E v T,
  E,[] |- v in T -> forall a b, sub_ty T (thandler a b) ->
  exists cr hl, v = handler cr hl /\ handlerlist_value hl.
Proof.
  remember (@nil ty) as G.
  intros.
  induction H; subst; auto.
  - rewrite nth_error_nil in H1; inversion H1.
  - inversion H0.
  - inversion H0.
  - inversion H0.
  - exists cr, hl; auto.
    split; auto.
    apply empty_handler_type_value in H2; auto.
  - apply IHhas_type_val; auto.
    apply sub_trans with (b := T'); auto.
Qed.

Lemma progress_effects : forall Env t T E,
  Env,nil |-c t in (dty T E) ->
  (value t \/ exists t', t ===> t') \/ (exists i o v k, t = opc (vinst i) o v k).
Proof.
  remember (@nil ty) as Gamma.
  intros.
  induction H; subst; auto.
  - left. left.
    unfold value. exists v. auto.
  - left. right.
    apply empty_tarr_is_abs with (a := t1) (b := t2) in H.
    + destruct H; subst.
      exists (substcomp v2 x); auto.
    + apply sub_refl.
  - left. right.
    assert (@nil ty = []); auto.
    apply IHhas_type_comp1 in H1.
    destruct H1.
    + destruct H1.
      * inversion_try_solve H1.
        exists (substcomp x c2); auto.
      * destruct H1.
        exists (do x c2); auto.
    + destruct H1, H1, H1, H1; subst.
      exists (opc (vinst x) x0 x1 (do x2 (shiftcomp' 1 1 c2))); auto.
  - right.
    apply empty_tinst_is_vinst with (e := e) (is := is) in H1.
    + destruct H1, H1; subst.
      exists x, o, v, c; auto.
    + apply sub_refl.
  - apply empty_thandler_is_handler with (a := a) (b := b) in H.
    destruct H, H, H; subst.
    assert (@nil ty = []); auto.
    apply IHhas_type_comp in H.
    destruct H.
    + destruct H.
      * inversion_try_solve H.
        left. right.
        exists (substcomp x1 x); auto.
      * destruct H.
        left. right.
        exists (handle (handler x x0) x1); auto.
    + destruct H, H, H, H; subst.
      apply opcase_dec with (a := Annot x1 x2) in H1.
      destruct H1.
      * destruct H.
        left. right.
        exists (substcomp x3
          (substcomp (abs (handle (shiftval 2 (handler x x0)) (shiftcomp' 1 1 x4))) x5)); auto.
      * left. right.
        exists (opc (vinst x1) x2 x3 (handle (shiftval 1 (handler x x0)) x4)); auto.
    + apply sub_refl.
Qed.

Theorem progress : forall E t T,
  E,[] |-c t in (dty T empty) ->
  value t \/ exists t', t ===> t'.
Proof.
  intros.
  assert (H' := H).
  apply progress_effects in H'.
  destruct H' as [V | [S O]]; auto.
  destruct O, H0, H0.
  subst.
  apply opc_not_empty with (c := opc (vinst S) x x0 x1) (T := dty T empty) (t := T) (e := empty) (i := vinst S) (o := x) (v := x0) (c' := x1) in H; auto.
  - destruct H, H.
    set_solver.
  - apply sub_refl.
Qed.

Lemma context_invariance :
  (forall E G t T, E,G |- t in T -> forall G', wf_context E G' -> E,(G ++ G') |- t in T) /\
  (forall E G t T, E,G |-c t in T -> forall G', wf_context E G' -> E,(G ++ G') |-c t in T) /\
  (forall E G t T D, E,G |-h t in T ; D -> forall G', wf_context E G' -> E,(G ++ G') |-h t in T ; D).
Proof.
  apply has_type_mut_ind;
    intros;
    try constructor;
    auto.
  - apply wf_context_append; auto.
  - apply nth_error_weakening; auto.
  - rewrite app_comm_cons.
    apply H; auto.
  - apply T_Handler with (e'' := e''); auto.
    rewrite app_comm_cons.
    apply H; auto.
  - apply T_SubVal with (T := T); auto.
  - apply T_App with (t1 := t1); auto.
  - apply T_Do with (a := a); auto.
    rewrite app_comm_cons.
    apply H0; auto.
  - apply T_Op with (e := e) (is := is); auto.
    apply H1; auto.
  - apply T_Handle with (a := a); auto.
  - apply T_SubComp with (t := t); auto.
  - apply T_Cons with (e := e) (is := is) (d' := d') (d'' := d''); auto.
    apply H0; auto.
Qed.

Lemma shift_typing :
  (forall E G t T,
    E,G |- t in T ->
    forall m L,
      wf_context E L ->
      E,(firstn m G ++ L ++ skipn m G) |- shiftval' (length L) m t in T) /\
  (forall E G t T,
    E,G |-c t in T ->
    forall m L,
      wf_context E L ->
      E,(firstn m G ++ L ++ skipn m G) |-c shiftcomp' (length L) m t in T) /\
  (forall E G t T D,
    E,G |-h t in T ; D ->
    forall m L,
      wf_context E L ->
      E,(firstn m G ++ L ++ skipn m G) |-h shifthandlerlist' (length L) m t in T ; D).
Proof.
  apply has_type_mut_ind; intros; simpl; try constructor; auto.
  - destruct (i <? m) eqn:eq; constructor.
    + apply wf_context_append.
      apply Forall_take; auto.
      apply wf_context_append; auto.
      apply Forall_drop; auto.
    + apply nth_error_weakening.
      apply nth_error_firstn.
      rewrite Nat.ltb_lt in eq; auto.
      auto.
    + apply wf_context_append.
      apply Forall_take; auto.
      apply wf_context_append; auto.
      apply Forall_drop; auto.
    + apply Nat.ltb_ge in eq.
      apply nth_error_firstn_append_skipn; auto.
  - apply H with (m := S m); auto.
  - apply T_Handler with (e'' := e''); auto.
    apply H with (m := S m); auto.
  - apply T_SubVal with (T := T); auto.
  - apply T_App with (t1 := t1).
    + apply H; auto.
    + apply H0; auto.
  - apply T_Do with (a := a).
    + apply H; auto.
    + apply H0 with (m := S m); auto.
  - apply T_Op with (e := e) (is := is); auto.
    apply H1 with (m := S m); auto.
  - apply T_Handle with (a := a); auto.
  - apply T_SubComp with (t := t); auto.
  - apply T_Cons with (e := e) (is := is) (d' := d') (d'' := d''); auto.
    apply H0 with (m := S (S m)); auto.
Qed.

Lemma shift_typing1 :
  (forall E G t T,
    E,G |- t in T ->
    forall m U,
      wf_ty E U ->
      E,(firstn m G ++ U :: skipn m G) |- shiftval' 1 m t in T) /\
  (forall E G t T,
    E,G |-c t in T ->
    forall m U,
      wf_ty E U ->
      E,(firstn m G ++ U :: skipn m G) |-c shiftcomp' 1 m t in T) /\
  (forall E G t T D,
    E,G |-h t in T ; D ->
    forall m U,
      wf_ty E U ->
      E,(firstn m G ++ U :: skipn m G) |-h shifthandlerlist' 1 m t in T ; D).
Proof.
  split; try split; intros.
  - assert (U :: drop m G = [U] ++ drop m G).
    auto.
    rewrite H1.
    apply shift_typing; auto.
  - assert (U :: drop m G = [U] ++ drop m G).
    auto.
    rewrite H1.
    apply shift_typing; auto.
  - assert (U :: drop m G = [U] ++ drop m G).
    auto.
    rewrite H1.
    apply shift_typing; auto.
Qed.

Lemma shift1 :
  (forall E G t T,
    E,G |- t in T ->
    forall U,
      wf_context E G ->
      wf_ty E U ->
      E,(U :: G) |- shiftval 1 t in T) /\
  (forall E G t T,
    E,G |-c t in T ->
    forall U,
      wf_context E G ->
      wf_ty E U ->
      E,(U :: G) |-c shiftcomp 1 t in T) /\
  (forall E G t T D,
    E,G |-h t in T ; D ->
    forall U,
      wf_context E G ->
      wf_ty E U ->
      E,(U :: G) |-h shifthandlerlist 1 t in T ; D).
Proof.
  split; try split; intros.
  - assert (U :: G = [] ++ [U] ++ G).
    auto.
    rewrite H2.
    unfold shiftval.
    assert (length [U] = 1).
    auto.
    rewrite <- H3.
    assert ([] = take 0 G); auto.
    rewrite H4.
    assert (G = drop 0 G); auto.
    rewrite H5.
    apply shift_typing; auto.
    constructor; auto.
    apply Forall_take.
    apply Forall_drop.
    auto.
  - assert (U :: G = [] ++ [U] ++ G).
    auto.
    rewrite H2.
    unfold shiftval.
    assert (length [U] = 1).
    auto.
    rewrite <- H3.
    assert ([] = take 0 G); auto.
    rewrite H4.
    assert (G = drop 0 G); auto.
    rewrite H5.
    apply shift_typing; auto.
    constructor; auto.
    apply Forall_take.
    apply Forall_drop.
    auto.
  - assert (U :: G = [] ++ [U] ++ G).
    auto.
    rewrite H2.
    unfold shiftval.
    assert (length [U] = 1).
    auto.
    rewrite <- H3.
    assert ([] = take 0 G); auto.
    rewrite H4.
    assert (G = drop 0 G); auto.
    rewrite H5.
    apply shift_typing; auto.
    constructor; auto.
    apply Forall_take.
    apply Forall_drop.
    auto.
Qed.

Lemma shiftn :
  (forall E G t T,
    E,G |- t in T ->
    forall L,
      wf_context E L ->
      E,(L ++ G) |- shiftval (length L) t in T) /\
  (forall E G t T,
    E,G |-c t in T ->
    forall L,
      wf_context E L ->
      E,(L ++ G) |-c shiftcomp (length L) t in T) /\
  (forall E G t T D,
    E,G |-h t in T ; D ->
    forall L,
      wf_context E L ->
      E,(L ++ G) |-h shifthandlerlist (length L) t in T ; D).
Proof.
  split; try split; intros.
  - assert (L ++ G = (take 0 G) ++ L ++ (drop 0 G)); auto.
    rewrite H1.
    unfold shiftval.
    apply shift_typing; auto.
  - assert (L ++ G = (take 0 G) ++ L ++ (drop 0 G)); auto.
    rewrite H1.
    unfold shiftcomp.
    apply shift_typing; auto.
  - assert (L ++ G = (take 0 G) ++ L ++ (drop 0 G)); auto.
    rewrite H1.
    unfold shiftcomp.
    apply shift_typing; auto.
Qed.

Lemma substitution_preserves_typing :
  (forall (t:val) E Gamma Gamma' v T U,
    E,(Gamma ++ U :: Gamma') |- t in T ->
    wf_context E Gamma ->
    wf_ty E U ->
    wf_context E Gamma' ->
    E,(Gamma ++ Gamma') |- v in U ->
    E,(Gamma ++ Gamma') |- substval' (length Gamma) v t in T) /\
  (forall (t:comp) E Gamma Gamma' v T U,
    E,(Gamma ++ U :: Gamma') |-c t in T ->
    wf_context E Gamma ->
    wf_ty E U ->
    wf_context E Gamma' ->
    E,(Gamma ++ Gamma') |- v in U ->
    E,(Gamma ++ Gamma') |-c substcomp' (length Gamma) v t in T) /\
  (forall (t:handlerlist) E Gamma Gamma' v T U D,
    E,(Gamma ++ U :: Gamma') |-h t in T ; D ->
    wf_context E Gamma ->
    wf_ty E U ->
    wf_context E Gamma' ->
    E,(Gamma ++ Gamma') |- v in U ->
    E,(Gamma ++ Gamma') |-h substhandlerlist' (length Gamma) v t in T ; D).
Proof.
  apply ast_mutind; intros; simpl; auto; simpl.
  - inversion_try_solve H; auto.
    apply unit_is_tunit in H; auto.
    subst.
    auto.
  - assert (H' := H).
    apply vinst_is_tinst with (i := i) in H; auto.
    destruct H, H, H, H4, H5.
    inversion_try_solve H.
    constructor; auto.
    apply ty_wellformed in H'; auto.
    inversion_try_solve H'; auto.
    apply wf_context_append; auto.
  - assert (H' := H).
    apply var_typing with (n := n) in H; auto.
    destruct H, H.
    apply ty_wellformed in H'; auto.
    destruct (n ?= length Gamma) eqn:eq.
    + apply nat_compare_eq in eq.
      subst.
      rewrite <- beq_nat_refl.
      rewrite nth_error_app in H4.
      inversion_try_solve H4.
      apply T_SubVal with (T := x); auto.
    + rewrite <- nat_compare_lt in eq.
      assert (eq' := eq).
      rewrite <- Nat.ltb_lt in eq'.
      rewrite eq'.
      assert (~(n = length Gamma)).
      omega.
      rewrite <- Nat.eqb_neq in H5.
      rewrite H5.
      apply T_SubVal with (T := x); auto.
      constructor.
      apply wf_context_append; auto.
      assert (eq'' := eq).
      apply nth_error_contraction with (l' := U :: Gamma') in eq; auto.
      apply nth_error_contraction with (l' := Gamma') in eq''; auto.
      rewrite <- H4.
      rewrite eq.
      rewrite eq''.
      auto.
    + rewrite <- nat_compare_gt in eq.
      assert (n <> length Gamma).
      omega.
      assert (~(n < length Gamma)).
      omega.
      rewrite <- Nat.eqb_neq in H5.
      rewrite H5.
      rewrite <- Nat.ltb_nlt in H6.
      rewrite H6.
      apply T_SubVal with (T := x); auto.
      constructor.
      apply wf_context_append; auto.
      remember (pred n - length Gamma) as m.
      assert (pred n = m + length Gamma).
      omega.
      rewrite H7.
      apply nth_error_pred_app with (h := U).
      assert (n = S (m + length Gamma)).
      omega.
      rewrite <- H8.
      auto.
    + apply wf_context_append; auto.
  - assert (H0' := H0).
    apply ty_wellformed in H0'.
    apply abs_is_tarr with (c := c) in H0; auto.
    destruct H0, H0, H0, H5.
    inversion_try_solve H0.
    inversion_try_solve H0'.
    constructor; auto.
    apply (H E (t1' :: Gamma) Gamma' (shiftval 1 v) t2' U); auto.
    apply T_SubComp with (t := x0); auto.
    assert (S := context_strengthen).
    destruct S, H8.
    clear H7. clear H10.
    specialize (H8 E (x :: Gamma ++ U :: Gamma') c x0).
    apply H8; auto.
    { constructor; auto. apply wf_context_append; auto. }
    { simpl. constructor; auto. apply sub_context_append; auto. apply sub_context_refl. constructor; auto. apply sub_refl. apply sub_context_refl. }
    { simpl. constructor; auto. apply wf_context_append; auto. }
    simpl.
    apply shift1; auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
  - assert (H1' := H1).
    apply ty_wellformed in H1'; auto.
    apply handler_is_thandler with (cr := c) (hl := h) in H1; auto.
    destruct H1, H1, H1, H1, H1, H1, H6.
    inversion_try_solve H1.
    inversion_try_solve H10.
    inversion_try_solve H12.
    apply T_SubVal with (T := thandler (dty x x1) (dty x0 x3)); auto.
    inversion_try_solve H6.
    apply T_Handler with (e := x1) (e'' := x2) (e' := x3); auto.
    replace (x :: Gamma ++ Gamma') with ((x :: Gamma) ++ Gamma'); auto.
    apply H with (U := U); auto.
    destruct H7, H8.
    auto.
    apply shift1; auto.
    apply wf_context_append; auto.
    destruct H7, H8.
    apply H0 with (U := U); auto.
    destruct H7; auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
  - assert (H0' := H0); auto.
    apply ty_wellformed in H0'; auto.
    apply ret_is_dty with (v := v) in H0; auto.
    destruct H0, H0, H0, H5.
    inversion_try_solve H0.
    inversion_try_solve H0'.
    constructor; auto.
    apply H with (U := U); auto.
    apply T_SubVal with (T := x); auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
  - assert (H1' := H1).
    apply ty_wellformed in H1'; auto.
    apply app_is_dty with (c1 := v) (c2 := v0) in H1; auto.
    destruct H1, H1, H1, H6.
    apply T_App with (t1 := x); auto.
    apply H with (U := U); auto.
    apply T_SubVal with (T := tarr x x0); auto.
    apply ty_wellformed in H7; auto.
    apply H8 in H7.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
    constructor; auto.
    apply sub_refl.
    apply H0 with (U := U); auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
  - assert (H1' := H1).
    apply ty_wellformed in H1'; auto.
    apply do_is_dty with (c1 := c) (c2 := c0) in H1; auto.
    destruct H1, H1, H1, H1, H6, H7.
    inversion_try_solve H1; auto.
    apply T_Do with (a := x) (b := t') (e := e'); auto.
    apply H with (U := U); auto.
    apply T_SubComp with (t := dty x x0); auto.
    constructor; auto.
    inversion_try_solve H1'; auto.
    constructor; auto.
    apply sub_refl.
    rewrite app_comm_cons.
    apply H0 with (U := U); auto.
    simpl.
    apply T_SubComp with (t := dty x1 x0); auto.
    apply shift1; auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
  - assert (H2' := H2).
    apply ty_wellformed in H2'; auto.
    apply opc_is_dty with (vi := v) (o := o) (v := v0) (k := c) in H2; auto.
    destruct H2, H2, H2, H2.
    destruct H2, H7, H8, H9, H10, H11, H12.
    inversion_try_solve H2; auto.
    apply T_Op with (e := x1) (is := x2); auto.
    apply H with (U := U); auto.
    apply H0 with (U := U); auto.
    rewrite app_comm_cons.
    apply H1 with (U := U); auto.
    simpl.
    apply T_SubComp with (t := dty x x0); auto.
    apply shift1; auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
  - assert (H1' := H1).
    apply ty_wellformed in H1'; auto.
    apply handle_is_dty with (v := v) (k := c) in H1; auto.
    destruct H1, H1.
    destruct H1, H6.
    inversion_try_solve H1.
    apply T_Handle with (a := x); auto.
    apply H with (U := U); auto.
    apply T_SubVal with (T := thandler x (dty t e)).
    constructor; auto.
    apply ty_wellformed in H7; auto.
    apply wf_context_append; auto.
    auto.
    constructor; auto.
    apply sub_refl.
    apply H0 with (U := U); auto.
    apply wf_context_append; auto.
    apply wf_context_append; auto.
  - inversion_try_solve H; auto.
  - inversion_try_solve H2.
    apply T_Cons with (e := e) (is := is) (d' := d') (d'' := d''); auto.
    apply H with (U := U); auto.
    replace (tarr (env_returnty E o) T :: env_paramty E o :: Gamma ++ Gamma') with ((tarr (env_returnty E o) T :: env_paramty E o :: Gamma) ++ Gamma'); auto.
    apply H0 with (U := U); auto.
    constructor; auto.
    constructor; auto.
    apply ty_wellformed in H2; auto.
    destruct H2; auto.
    apply wf_context_append; auto.
    replace ((tarr (env_returnty E o) T :: env_paramty E o :: Gamma) ++ Gamma') with ([tarr (env_returnty E o) T; env_paramty E o] ++ (Gamma ++ Gamma')); auto.
    apply shiftn; auto.
    constructor; auto.
    constructor; auto.
    apply ty_wellformed in H2; auto.
    destruct H2; auto.
    apply wf_context_append; auto.
    apply H1 with (U := U); auto.
Qed.

Lemma substitution_preserves_typing_nil :
  (forall (t:val) E v T U,
    E,(U :: nil) |- t in T ->
    E,nil |- v in U ->
    E,nil |- substval v t in T) /\
  (forall (t:comp) E v T U,
    E,(U :: nil) |-c t in T ->
    E,nil |- v in U ->
    E,nil |-c substcomp v t in T) /\
  (forall (t:handlerlist) E v T U D,
    E,(U :: nil) |-h t in T ; D ->
    E,nil |- v in U ->
    E,nil |-h substhandlerlist v t in T ; D).
Proof.
  unfold substval, substcomp, substhandlerlist.
  replace 0 with (@length nat nil); auto.
  assert (forall t, @nil t = nil ++ nil); auto.
  rewrite H.
  assert (H' := substitution_preserves_typing).
  inversion H'.
  split; try split; intros; simpl in H0.
  - apply H0 with (U := U); auto.
    apply ty_wellformed in H3; auto.
    constructor; auto.
  - apply H1 with (U := U); auto.
    apply ty_wellformed in H3; auto.
    constructor; auto.
  - apply H1 with (U := U); auto.
    apply ty_wellformed in H3; auto.
    constructor; auto.
Qed.

Lemma handlerlist_typing : forall E G hl o c T D,
  opcase hl o c ->
  E,G |-h hl in T ; D ->
  E,(tarr (env_returnty E (annot_op o)) T :: env_paramty E (annot_op o) :: G) |-c c in T.
Proof.
  intros.
  generalize dependent T.
  generalize dependent D.
  induction H; intros; simpl.
  - inversion_try_solve H0; auto.
  - inversion_try_solve H1; auto.
    apply IHopcase with (D := d'); auto.
Qed.

Theorem preservation : forall E Gamma t t' T,
  E,Gamma |-c t in T ->
  wf_context E Gamma ->
  t ===> t' ->
  E,Gamma |-c t' in T.
Proof with eauto.
  intros.
  generalize dependent t'.
  induction H; intros.
  - inversion_try_solve H1.
  - inversion_try_solve H2.
    assert (H' := H).
    apply ty_wellformed in H'; auto.
    apply abs_is_tarr with (c := t0) in H; auto.
    destruct H, H, H, H3.
    unfold substcomp.
    replace G with ([] ++ G); auto.
    replace 0 with (@length ty []); auto.
    apply substitution_preserves_typing with (U := t1); auto.
    inversion_try_solve H.
    simpl.
    apply context_strengthen with (G := x :: G); auto.
    inversion_try_solve H'.
    apply T_SubComp with (t := x0); auto.
    constructor; auto.
    apply sub_context_refl.
    constructor; auto.
    inversion_try_solve H'; auto.
    inversion_try_solve H'; auto.
  - inversion_try_solve H2.
    + assert (H' := H); auto.
      apply ty_wellformed in H'; auto.
      inversion_try_solve H'.
      apply ret_is_dty with (v := v) in H; auto.
      destruct H, H, H, H3.
      unfold substcomp.
      replace G with ([] ++ G); auto.
      replace 0 with (@length ty []); auto.
      apply substitution_preserves_typing with (U := a); auto.
      inversion_try_solve H.
      apply T_SubVal with (T := x); auto.
    + apply T_Do with (a := a); auto.
    + assert (H' := H).
      apply ty_wellformed in H'.
      inversion_try_solve H'.
      apply opc_is_dty with (vi := vi) (o := o) (v := v) (k := c0) in H; auto.
      destruct H, H, H, H.
      destruct H, H3, H4, H5, H8, H9, H10.
      apply T_Op with (e := x1) (is := x2); auto.
      apply T_Do with (a := a); auto.
      apply T_SubComp with (t := dty x x0); auto.
      replace (a :: env_returnty E o :: G) with ((take 1 (a :: G)) ++ [env_returnty E o] ++ (drop 1 (a :: G))); auto.
      apply shift_typing1; auto.
      inversion_try_solve H; auto.
      auto.
  - inversion_try_solve H7.
  - inversion_try_solve H2.
    + assert (H' := H); auto.
      apply ty_wellformed in H'; auto.
      apply handler_is_thandler with (cr := cr) (hl := hl) in H; auto.
      destruct H, H, H, H, H.
      destruct H, H3, H4, H5.
      inversion_try_solve H.
      inversion_try_solve H11.
      inversion_try_solve H13.
      inversion_try_solve H3.
      apply T_Handle with (a := dty x x1); auto.
      apply T_Handler with (e'' := x2); auto.
      apply T_SubComp with (t := dty x0 x3); auto.
      inversion_try_solve H'; auto.
      inversion_try_solve H13; auto.
      { auto. }
      { set_solver. }
      { apply T_SubComp with (t := dty t e); auto. }
    + assert (H1' := H1).
      apply ty_wellformed in H1'; auto.
      apply ret_is_dty with (v := v0) in H1; auto.
      destruct H1, H1, H1, H3.
      unfold substcomp.
      replace G with ([] ++ G); auto.
      replace 0 with (@length ty []); auto.
      apply substitution_preserves_typing with (U := x); auto.
      * assert (H' := H); auto.
        apply ty_wellformed in H'; auto.
        apply handler_is_thandler with (cr := cr) (hl := hl) in H; auto.
        destruct H, H, H, H, H, H, H5, H6, H7.
        inversion_try_solve H.
        inversion_try_solve H12.
        inversion_try_solve H14.
        simpl.
        inversion_try_solve H'.
        inversion_try_solve H5.
        apply context_strengthen with (G := x1 :: G); auto.
        apply T_SubComp with (t := dty x2 x5); auto.
        constructor; auto.
        inversion_try_solve H1.
        apply sub_trans with (b := t); auto.
        apply sub_context_refl.
        constructor; auto.
        apply ty_wellformed in H4; auto.
      * apply ty_wellformed in H4; auto.
    + assert (H1' := H1).
      apply ty_wellformed in H1'; auto.
      apply opc_is_dty with (vi := vinst i) (o := o) (v := v0) (k := c0) in H1; auto.
      destruct H1, H1, H1, H1.
      destruct H1, H3, H4, H5, H7, H8, H9.
      replace G with ([] ++ G); auto.
      unfold substcomp.
      replace 0 with (@length ty []) at 1; auto.
      apply substitution_preserves_typing with (U := env_paramty E o); auto.
      assert (H' := H).
      assert (H'' := H).
      apply ty_wellformed in H'; auto.
      apply handler_is_thandler with (cr := cr) (hl := hl) in H; auto.
      destruct H, H, H, H, H.
      destruct H, H11, H12, H13.
      replace 0 with (@length ty []) at 1; auto.
      apply substitution_preserves_typing with (U := tarr (env_returnty E o) b); auto.
      apply handlerlist_typing with (E := E) (G := G) (T := dty x4 x7) (D := x6) in H6; auto.
      simpl in H6.
      simpl.
      apply context_strengthen with (G := tarr (env_returnty E o) (dty x4 x7) :: env_paramty E o :: G); auto.
      apply T_SubComp with (t := dty x4 x7); auto.
      inversion_try_solve H'; auto.
      inversion_try_solve H; auto.
      constructor; auto.
      apply ty_wellformed in H13; auto.
      constructor; auto.
      inversion_try_solve H11; auto.
      Admitted.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.
Definition stuck (t:comp) : Prop :=
  (normal_form step) t /\ ~(value t).

Corollary soundness : forall E t t' T,
  E,nil |-c t in dty T empty ->
  t ===>* t' ->
  ~(stuck t').
Proof.
  intros.
  unfold stuck, normal_form, not.
  intros.
  destruct H1.
  induction H0.
  - apply progress in H.
    destruct H; auto.
  - apply IHmulti; auto.
    apply preservation with (t' := y) in H; auto.
Qed.
