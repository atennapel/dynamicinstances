(*
  A formalization of simple algebraic effects
*)
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.
Require Import Util.
From stdpp Require Import fin_collections gmap.

(* effects *)
Definition op := nat.
Notation ops := (gset op).

(* ast *)
Inductive ty : Type :=
  | tarr : ty -> ops -> ty -> ty
  | tunit : ty
  | thandler : ops -> ty -> ops -> ty -> ty.

Inductive val : Type :=
  | unit : val
  | var : nat -> val
  | abs : comp -> val
  | handler : comp -> handlerlist -> val
with comp : Type :=
  | ret : val -> comp
  | app : val -> val -> comp
  | do : comp -> comp -> comp
  | opc : op -> val -> comp -> comp
  | handle : val -> comp -> comp
with handlerlist : Type :=
  | hnil : handlerlist
  | hcons : op -> comp -> handlerlist -> handlerlist.

Scheme val_comp_ind := Induction for val Sort Prop
  with comp_val_ind := Induction for comp Sort Prop
  with handlerlist_mut_ind := Induction for handlerlist Sort Prop.
Combined Scheme val_comp_mutind from val_comp_ind, comp_val_ind, handlerlist_mut_ind.

(* get computation of operation in list, but only the first one *)
Inductive opcase : handlerlist -> op -> comp -> Prop :=
  | O_Head : forall o co r,
    opcase (hcons o co r) o co
  | O_Tail : forall o o' co co' r,
    o <> o' ->
    opcase r o co' ->
    opcase (hcons o' co r) o co'.

Hint Constructors opcase.

(* parameter and return type of an operation *)
Axiom paramty : op -> ty.
Axiom returnty : op -> ty.

(* closed *)
Inductive closedval' : nat -> val -> Prop :=
  | C_Unit : forall n,
    closedval' n unit
  | C_Var : forall n x,
    x < n ->
    closedval' n (var x)
  | C_Abs : forall n t,
    closedcomp' (S n) t ->
    closedval' n (abs t)
  | C_Handler : forall n cr hl,
    closedcomp' (S n) cr ->
    closedhandlerlist' n hl ->
    closedval' n (handler cr hl)
with closedcomp' : nat -> comp -> Prop :=
  | C_Return : forall n t,
    closedval' n t ->
    closedcomp' n (ret t)
  | C_App : forall n t1 t2,
    closedval' n t1 ->
    closedval' n t2 ->
    closedcomp' n (app t1 t2)
  | C_Do : forall n t1 t2,
    closedcomp' n t1 ->
    closedcomp' (S n) t2 ->
    closedcomp' n (do t1 t2)
  | C_Op : forall n o v c,
    closedval' n v ->
    closedcomp' (S n) c ->
    closedcomp' n (opc o v c)
  | C_Handle : forall n v c,
    closedval' n v ->
    closedcomp' n c ->
    closedcomp' n (handle v c)
with closedhandlerlist' : nat -> handlerlist -> Prop :=
  | C_Nil : forall n,
    closedhandlerlist' n hnil
  | C_Cons : forall n o c r,
    closedcomp' (S (S n)) c ->
    closedhandlerlist' n r ->
    closedhandlerlist' n (hcons o c r).

Scheme closed_val_comp_ind := Induction for closedval' Sort Prop
  with closed_comp_val_ind := Induction for closedcomp' Sort Prop
  with closed_handlerlist_mut_ind := Induction for closedhandlerlist' Sort Prop.
Combined Scheme closed_val_comp_mutind from closed_val_comp_ind, closed_comp_val_ind, closed_handlerlist_mut_ind.

Hint Constructors closedval'.
Hint Constructors closedcomp'.
Hint Constructors closedhandlerlist'.

Definition closedval t := closedval' 0 t.
Definition closedcomp t := closedcomp' 0 t.
Definition closedhandlerlist t := closedhandlerlist' 0 t.

Hint Unfold closedval.
Hint Unfold closedcomp.
Hint Unfold closedhandlerlist.

(* substitution *)
Fixpoint shiftval' (d:nat) (c:nat) (t:val) : val :=
  match t with
  | unit => t
  | var k => if k <? c then t else var (k + d)
  | abs t' => abs (shiftcomp' d (S c) t')
  | handler cr hl => handler (shiftcomp' d (S c) cr) (shifthandlerlist' d c hl)
  end
with shiftcomp' (d:nat) (c:nat) (t:comp) : comp :=
  match t with
  | ret t' => ret (shiftval' d c t')
  | app t1 t2 => app (shiftval' d c t1) (shiftval' d c t2)
  | do t1 t2 => do (shiftcomp' d c t1) (shiftcomp' d (S c) t2)
  | opc o v t => opc o (shiftval' d c v) (shiftcomp' d (S c) t)
  | handle v t => handle (shiftval' d c v) (shiftcomp' d c t)
  end
with shifthandlerlist' (d:nat) (c:nat) (t:handlerlist) : handlerlist :=
  match t with
  | hnil => t
  | hcons o co r => hcons o (shiftcomp' d (S (S c)) co) (shifthandlerlist' d c r)
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
  | opc o v t => opc o (substval' j s v) (substcomp' (S j) (shiftval 1 s) t)
  | handle v t => handle (substval' j s v) (substcomp' j s t)
  end
with substhandlerlist' (j:nat) (s:val) (t:handlerlist) : handlerlist :=
  match t with
  | hnil => t
  | hcons o co r => hcons o (substcomp' (S (S j)) (shiftval 2 s) co) (substhandlerlist' j s r)
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

Reserved Notation "c1 '===>' c2" (at level 40).

Inductive step : comp -> comp -> Prop :=
  | S_AppAbs : forall t1 t2,
    (app (abs t1) t2) ===> substcomp t2 t1
  | S_DoReturn : forall v t,
    do (ret v) t ===> substcomp v t
  | S_Do : forall t1 t1' t2,
    t1 ===> t1' ->
    do t1 t2 ===> do t1' t2
  | S_DoOp : forall o v c1 c2,
    do (opc o v c1) c2 ===> opc o v (do c1 (shiftcomp' 1 1 c2))
  | S_Handle : forall cr hl c c',
    c ===> c' ->
    handle (handler cr hl) c ===> handle (handler cr hl) c'
  | S_HandleReturn : forall cr hl v,
    handle (handler cr hl) (ret v) ===> substcomp v cr
  | S_HandleOp1 : forall cr o co hl v c,
    opcase hl o co ->
    handle (handler cr hl) (opc o v c) ===>
      substcomp v
        (substcomp (abs (handle (shiftval 2 (handler cr hl)) (shiftcomp' 1 1 c))) co)
  | S_HandleOp2 : forall cr hl o v c,
    (forall co, ~(opcase hl o co)) ->
    handle (handler cr hl) (opc o v c) ===>
      opc o v (handle (shiftval 1 (handler cr hl)) c)

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

(* typing rules *)
Fixpoint ops_of (hl:handlerlist) : ops :=
  match hl with
  | hnil => empty
  | hcons o _ r => union {[o]} (ops_of r)
  end.

Definition context := list ty.

Reserved Notation "Gamma '|-' t 'in' T" (at level 40).
Reserved Notation "Gamma '|-c' t 'in' T ';' E" (at level 40).
Reserved Notation "Gamma '|-h' t 'in' T ';' E" (at level 40).

Inductive has_type_val : context -> val -> ty -> Prop :=
  | T_Unit : forall Gamma,
    Gamma |- unit in tunit
  | T_Var : forall Gamma x T,
    nth_error Gamma x = Some T ->
    Gamma |- var x in T
  | T_Abs : forall Gamma t T1 E T2,
    (T1 :: Gamma) |-c t in T2 ; E ->
    Gamma |- abs t in tarr T1 E T2
  | T_Handler : forall Gamma cr hl E1 T1 E2 T2,
    (T1 :: Gamma) |-c cr in T2 ; E2 ->
    Gamma |-h hl in T2 ; E2 ->
    (E1 ∖  (ops_of hl)) ⊆ E2 ->
    Gamma |- handler cr hl in thandler E1 T1 E2 T2

where "Gamma '|-' t 'in' T" := (has_type_val Gamma t T)

with has_type_comp : context -> comp -> ty -> ops -> Prop :=
  | T_Return : forall Gamma v T E,
    Gamma |- v in T ->
    Gamma |-c ret v in T ; E
  | T_App : forall Gamma t1 t2 T1 E T2,
    Gamma |- t1 in tarr T1 E T2 ->
    Gamma |- t2 in T1 ->
    Gamma |-c app t1 t2 in T2 ; E
  | T_Do : forall Gamma t1 t2 T1 E T2,
    Gamma |-c t1 in T1 ; E ->
    (T1 :: Gamma) |-c t2 in T2 ; E ->
    Gamma |-c do t1 t2 in T2; E
  | T_Op : forall Gamma o v c T E,
    Gamma |- v in paramty o ->
    (returnty o :: Gamma) |-c c in T ; E ->
    o ∈ E ->
    Gamma |-c opc o v c in T ; E
  | T_Handle : forall Gamma v c E1 T1 E2 T2,
    Gamma |- v in thandler E1 T1 E2 T2 ->
    Gamma |-c c in T1 ; E1 ->
    Gamma |-c handle v c in T2 ; E2

where "Gamma '|-c' t 'in' T ';' E" := (has_type_comp Gamma t T E)

with has_type_handlerlist : context -> handlerlist -> ty -> ops -> Prop :=
  | T_Nil : forall Gamma T E,
    Gamma |-h hnil in T ; E
  | T_Cons : forall Gamma T E o c r,
    (tarr (returnty o) E T :: paramty o :: Gamma) |-c c in T ; E ->
    Gamma |-h r in T ; E ->
    Gamma |-h hcons o c r in T ; E

where "Gamma '|-h' t 'in' T ';' E" := (has_type_handlerlist Gamma t T E).

Scheme has_type_val_comp_ind := Induction for has_type_val Sort Prop
  with has_type_comp_val_ind := Induction for has_type_comp Sort Prop
  with has_type_handlerlist_mut_ind := Induction for has_type_handlerlist Sort Prop.
Combined Scheme has_type_val_comp_mutind from has_type_val_comp_ind, has_type_comp_val_ind, has_type_handlerlist_mut_ind.

Hint Constructors has_type_val.
Hint Constructors has_type_comp.

(* theorems *)
Lemma opcase_deterministic: forall hl o c,
  opcase hl o c -> (forall c', opcase hl o c' -> c = c').
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
  generalize dependent y1.
  induction H0; intros; try (inversion_try_solve H).
  - apply IHstep in H4.
    rewrite H4.
    auto.
  - apply IHstep in H5.
    rewrite H5.
    auto.
  - inversion_try_solve H0.
    + inversion_try_solve H7.
      contradiction.
    + specialize (H7 co).
      contradiction.
  - inversion_try_solve H0.
    + apply opcase_deterministic with (c := co1) in H; auto.
      rewrite H.
      auto.
    + specialize (H9 co).
      contradiction.
  - inversion_try_solve H0.
    specialize (H co).
    contradiction.
Qed.

Lemma opcase_weakening : forall hl o c o' c',
  opcase hl o c ->
  o <> o' ->
  opcase (hcons o' c' hl) o c.
Proof.
  intros.
  generalize dependent o'.
  generalize dependent c'.
  induction H; intros; constructor; auto.
Qed.

Lemma typable_closed_length :
  (forall Gamma t T, Gamma |- t in T -> closedval' (length Gamma) t) /\
  (forall Gamma t T E, Gamma |-c t in T ; E -> closedcomp' (length Gamma) t) /\
  (forall Gamma t T E, Gamma |-h t in T ; E -> closedhandlerlist' (length Gamma) t).
Proof.
  apply has_type_val_comp_mutind; intros; auto.
  constructor.
  apply nth_error_length in e; assumption.
Qed.

Lemma shift_closed :
  (forall n t, closedval' n t -> forall m, shiftval' m n t = t) /\
  (forall n t, closedcomp' n t -> forall m, shiftcomp' m n t = t) /\
  (forall n t, closedhandlerlist' n t -> forall m, shifthandlerlist' m n t = t).
Proof.
  apply closed_val_comp_mutind; intros; auto; simpl;
    try (rewrite H; auto);
    try (rewrite H0; auto);
    try (rewrite H; rewrite H0; auto).
  - rewrite <- Nat.ltb_lt in l.
    rewrite l.
    auto.
Qed.

Lemma opcase_remove : forall h o o' c c',
  opcase (hcons o' c' h) o c ->
  o <> o' ->
  opcase h o c.
Proof.
  induction h; intros; inversion_try_solve H; try contradiction; auto.
Qed.

Lemma opcase_dec : forall h o,
  (exists c, opcase h o c) \/ (forall c, ~(opcase h o c)).
Proof.
  induction h; intros.
  - right.
    intros.
    unfold not.
    intros.
    inversion H.
  - destruct IHh with (o := o0).
    + destruct H.
      assert (Hd := Nat.eq_dec o o0).
      destruct Hd.
      * subst.
        left.
        exists c.
        auto.
      * left.
        exists x.
        auto.
    + assert (Hd := Nat.eq_dec o o0).
      destruct Hd.
      * subst.
        left.
        exists c.
        auto.
      * right.
        unfold not.
        intros.
        apply H with (c := c0).
        apply opcase_remove with (o' := o) (c' := c); auto.
Qed.

Lemma progress_effects : forall t T E,
  nil |-c t in T ; E ->
  (value t \/ exists t', t ===> t') \/ (exists o v k, t = opc o v k).
Proof.
  remember (@nil ty) as Gamma.
  intros.
  induction H; subst; auto.
  - left. left. unfold value. exists v. auto.
  - left. right.
    inversion_try_solve H.
    + rewrite nth_error_nil in H1. inversion H1.
    + exists (substcomp t2 t).
      auto.
  - assert (@nil ty = []); auto.
    apply IHhas_type_comp1 in H1.
    inversion_try_solve H1.
    inversion_try_solve H2.
    + inversion_try_solve H3.
      left. right.
      exists (substcomp x t2).
      auto.
    + destruct H3.
      left. right.
      exists (do x t2).
      auto.
    + destruct H2 as [o], H2 as [v], H2 as [k].
      subst.
      left. right.
      exists (opc o v (do k t2)).
      inversion_try_solve H.
      replace t2 with (shiftcomp' 1 1 t2) at 2; auto.
      apply shift_closed.
      replace 1 with (length [T1]); auto.
      apply typable_closed_length in H0; auto.
  - right.
    exists o, v, c.
    auto.
  - inversion_try_solve H.
    + rewrite nth_error_nil in H1. inversion H1.
    + left. right.
      assert (@nil ty = []); auto.
      apply IHhas_type_comp in H1.
      inversion_try_solve H1.
      inversion_try_solve H2.
      * inversion_try_solve H3.
        exists (substcomp x cr).
        auto.
      * destruct H3.
        exists (handle (handler cr hl) x).
        auto.
      * destruct H2 as [o'], H2 as [v], H2 as [k].
        subst.
        destruct (opcase_dec hl o').
        { destruct H2.
          exists (substcomp v (substcomp (abs (handle (shiftval 2 (handler cr hl)) (shiftcomp' 1 1 k))) x)).
          auto. }
        { exists (opc o' v (handle (shiftval 1 (handler cr hl)) k)).
          auto. }
Qed.

Theorem progress : forall t T,
  nil |-c t in T ; empty ->
  value t \/ exists t', t ===> t'.
Proof.
  intros.
  assert (H' := H).
  apply progress_effects in H'.
  destruct H' as [V | [S O]]; auto.
  destruct O, H0.
  subst.
  inversion_try_solve H.
Qed.

Lemma context_invariance :
  (forall Gamma t T, Gamma |- t in T -> forall Gamma', (Gamma ++ Gamma') |- t in T) /\
  (forall Gamma t T E, Gamma |-c t in T ; E -> forall Gamma', (Gamma ++ Gamma') |-c t in T ; E) /\
  (forall Gamma t T E, Gamma |-h t in T ; E -> forall Gamma', (Gamma ++ Gamma') |-h t in T ; E).
Proof.
  apply has_type_val_comp_mutind;
    intros;
    try constructor;
    auto;
    try (apply H);
    try (apply H0).
  - apply nth_error_weakening.
    auto.
  - apply T_App with (T1 := T1).
    + apply H.
    + apply H0.
  - apply T_Do with (T1 := T1).
    + apply H.
    + apply H0.
  - apply T_Handle with (T1 := T1) (E1 := E1).
    + apply H.
    + apply H0.
Qed.

Lemma ops_of_shift_invariance : forall n m l,
  ops_of (shifthandlerlist' n m l) = ops_of l.
Proof.
  induction l; auto.
  simpl.
  rewrite IHl.
  auto.
Qed.

Lemma ops_of_subst_invariance : forall n m l,
  ops_of (substhandlerlist' n m l) = ops_of l.
Proof.
  induction l; auto.
  simpl.
  rewrite IHl.
  auto.
Qed.

Lemma shift_typing :
  (forall Gamma t T,
    Gamma |- t in T ->
    forall m L,
      (firstn m Gamma ++ L ++ skipn m Gamma) |- shiftval' (length L) m t in T) /\
  (forall Gamma t T E,
    Gamma |-c t in T ; E ->
    forall m L,
      (firstn m Gamma ++ L ++ skipn m Gamma) |-c shiftcomp' (length L) m t in T ; E) /\
  (forall Gamma t T E,
    Gamma |-h t in T ; E ->
    forall m L,
      (firstn m Gamma ++ L ++ skipn m Gamma) |-h shifthandlerlist' (length L) m t in T ; E).
Proof.
  apply has_type_val_comp_mutind; intros; simpl; try constructor; auto.
  - destruct (x <? m) eqn:eq; constructor.
    + apply nth_error_weakening.
      apply nth_error_firstn.
      rewrite Nat.ltb_lt in eq; auto.
      auto.
    + apply Nat.ltb_ge in eq.
      apply nth_error_firstn_append_skipn; auto.
  - apply H with (m := S m).
  - apply H with (m := S m).
  - rewrite ops_of_shift_invariance.
    auto.
  - apply T_App with (T1 := T1).
    + apply H.
    + apply H0.
  - apply T_Do with (T1 := T1).
    + apply H.
    + apply H0 with (m := S m).
  - apply H0 with (m := S m).
  - apply T_Handle with (T1 := T1) (E1 := E1).
    + apply H.
    + apply H0.
  - apply H with (m := S (S m)).
Qed.

Lemma shift_typing1 :
  (forall Gamma t T,
    Gamma |- t in T ->
    forall m U,
      (firstn m Gamma ++ U :: skipn m Gamma) |- shiftval' 1 m t in T) /\
  (forall Gamma t T E,
    Gamma |-c t in T ; E ->
    forall m U,
      (firstn m Gamma ++ U :: skipn m Gamma) |-c shiftcomp' 1 m t in T ; E) /\
  (forall Gamma t T E,
    Gamma |-h t in T ; E ->
    forall m U,
      (firstn m Gamma ++ U :: skipn m Gamma) |-h shifthandlerlist' 1 m t in T ; E).
Proof.
  split; try split; intros.
  - assert (U :: drop m Gamma = [U] ++ drop m Gamma).
    auto.
    rewrite H0.
    apply shift_typing; auto.
  - assert (U :: drop m Gamma = [U] ++ drop m Gamma).
    auto.
    rewrite H0.
    apply shift_typing; auto.
  - assert (U :: drop m Gamma = [U] ++ drop m Gamma).
    auto.
    rewrite H0.
    apply shift_typing; auto.
Qed.

Lemma shift1 :
  (forall Gamma t T,
    Gamma |- t in T ->
    forall U,
      (U :: Gamma) |- shiftval 1 t in T) /\
  (forall Gamma t T E,
    Gamma |-c t in T ; E ->
    forall U,
      (U :: Gamma) |-c shiftcomp 1 t in T ; E) /\
  (forall Gamma t T E,
    Gamma |-h t in T ; E ->
    forall U,
      (U :: Gamma) |-h shifthandlerlist 1 t in T ; E).
Proof.
  split; try split; intros.
  - assert (U :: Gamma = [] ++ [U] ++ Gamma).
    auto.
    rewrite H0.
    unfold shiftval.
    assert (length [U] = 1).
    auto.
    rewrite <- H1.
    assert ([] = take 0 Gamma); auto.
    rewrite H2.
    assert (Gamma = drop 0 Gamma); auto.
    rewrite H3.
    apply shift_typing; auto.
  - assert (U :: Gamma = [] ++ [U] ++ Gamma).
    auto.
    rewrite H0.
    unfold shiftval.
    assert (length [U] = 1).
    auto.
    rewrite <- H1.
    assert ([] = take 0 Gamma); auto.
    rewrite H2.
    assert (Gamma = drop 0 Gamma); auto.
    rewrite H3.
    apply shift_typing; auto.
  - assert (U :: Gamma = [] ++ [U] ++ Gamma).
    auto.
    rewrite H0.
    unfold shiftval.
    assert (length [U] = 1).
    auto.
    rewrite <- H1.
    assert ([] = take 0 Gamma); auto.
    rewrite H2.
    assert (Gamma = drop 0 Gamma); auto.
    rewrite H3.
    apply shift_typing; auto.
Qed.

Lemma shiftn :
  (forall Gamma t T,
    Gamma |- t in T ->
    forall L,
      (L ++ Gamma) |- shiftval (length L) t in T) /\
  (forall Gamma t T E,
    Gamma |-c t in T ; E ->
    forall L,
      (L ++ Gamma) |-c shiftcomp (length L) t in T ; E) /\
  (forall Gamma t T E,
    Gamma |-h t in T ; E ->
    forall L,
      (L ++ Gamma) |-h shifthandlerlist (length L) t in T ; E).
Proof.
  split; try split; intros.
  - assert (L ++ Gamma = (take 0 Gamma) ++ L ++ (drop 0 Gamma)); auto.
    rewrite H0.
    unfold shiftval.
    apply shift_typing; auto.
  - assert (L ++ Gamma = (take 0 Gamma) ++ L ++ (drop 0 Gamma)); auto.
    rewrite H0.
    unfold shiftcomp.
    apply shift_typing; auto.
  - assert (L ++ Gamma = (take 0 Gamma) ++ L ++ (drop 0 Gamma)); auto.
    rewrite H0.
    unfold shiftcomp.
    apply shift_typing; auto.
Qed.

Lemma substitution_preserves_typing :
  (forall (t:val) Gamma Gamma' v T U,
    (Gamma ++ U :: Gamma') |- t in T ->
    (Gamma ++ Gamma') |- v in U ->
    (Gamma ++ Gamma') |- substval' (length Gamma) v t in T) /\
  (forall (t:comp) Gamma Gamma' v T U E,
    (Gamma ++ U :: Gamma') |-c t in T ; E ->
    (Gamma ++ Gamma') |- v in U ->
    (Gamma ++ Gamma') |-c substcomp' (length Gamma) v t in T ; E) /\
  (forall (t:handlerlist) Gamma Gamma' v T U E,
    (Gamma ++ U :: Gamma') |-h t in T ; E ->
    (Gamma ++ Gamma') |- v in U ->
    (Gamma ++ Gamma') |-h substhandlerlist' (length Gamma) v t in T ; E).
Proof.
  apply val_comp_mutind; intros; simpl; auto; simpl.
  - inversion_try_solve H; auto.
  - inversion_try_solve H.
    destruct (n ?= length Gamma) eqn:eq.
    + apply nat_compare_eq in eq.
      subst.
      rewrite <- beq_nat_refl.
      rewrite nth_error_app in H3.
      inversion_try_solve H3.
      auto.
    + rewrite <- nat_compare_lt in eq.
      assert (eq' := eq).
      rewrite <- Nat.ltb_lt in eq'.
      rewrite eq'.
      assert (~(n = length Gamma)).
      omega.
      rewrite <- Nat.eqb_neq in H1.
      rewrite H1.
      constructor.
      assert (eq'' := eq).
      apply nth_error_contraction with (l' := U :: Gamma') in eq; auto.
      apply nth_error_contraction with (l' := Gamma') in eq''; auto.
      rewrite <- H3.
      rewrite eq.
      rewrite eq''.
      auto.
    + rewrite <- nat_compare_gt in eq.
      assert (n <> length Gamma).
      omega.
      assert (~(n < length Gamma)).
      omega.
      rewrite <- Nat.eqb_neq in H1.
      rewrite H1.
      rewrite <- Nat.ltb_nlt in H2.
      rewrite H2.
      constructor.
      remember (pred n - length Gamma) as m.
      assert (pred n = m + length Gamma).
      omega.
      rewrite H4.
      apply nth_error_pred_app with (h := U).
      assert (n = S (m + length Gamma)).
      omega.
      rewrite <- H5.
      auto.
  - inversion_try_solve H0.
    constructor.
    apply (H (T1 :: Gamma) Gamma' (shiftval 1 v) T2 U); auto.
    simpl.
    apply shift1; auto.
  - inversion_try_solve H1.
    constructor; auto.
    + apply (H (T1 :: Gamma)) with (U := U); auto.
      simpl.
      apply shift1; auto.
    + apply H0 with (U := U); auto.
    + rewrite ops_of_subst_invariance; auto.
  - constructor.
    apply H with (U := U); auto.
    inversion_try_solve H0; auto.
  - inversion_try_solve H1.
    apply T_App with (T1 := T1).
    + apply H with (U := U); auto.
    + apply H0 with (U := U); auto.
  - inversion_try_solve H1.
    apply T_Do with (T1 := T1).
    apply H with (U := U); auto.
    rewrite app_comm_cons.
    apply H0 with (U := U); auto.
    simpl.
    apply shift1; auto.
  - inversion_try_solve H1.
    constructor; auto.
    + apply H with (U := U); auto.
    + apply (H0 (returnty o :: Gamma) Gamma' (shiftval 1 v0) T U); auto.
      apply shift1; auto.
  - inversion_try_solve H1.
    apply T_Handle with (E1 := E1) (T1 := T1); auto.
    + apply H with (U := U); auto.
    + apply H0 with (U := U); auto.
  - constructor.
  - constructor.
    + replace (S (S (length Gamma))) with (length (tarr (returnty o) E T :: paramty o :: Gamma)); auto.
      replace (tarr (returnty o) E T :: paramty o :: Gamma ++ Gamma') with ((tarr (returnty o) E T :: paramty o :: Gamma) ++ Gamma'); auto.
      apply H with (U := U) (v := shiftval 2 v); simpl; auto.
      * inversion_try_solve H1; auto.
      * replace (tarr (returnty o) E T :: paramty o :: Gamma ++ Gamma') with ([tarr (returnty o) E T; paramty o] ++ (Gamma ++ Gamma')); auto.
        apply shiftn; auto.
    + apply H0 with (U := U); auto.
      inversion H1; auto.
Qed.

Lemma substitution_preserves_typing_nil :
  (forall (t:val) v T U,
    (U :: nil) |- t in T ->
    nil |- v in U ->
    nil |- substval v t in T) /\
  (forall (t:comp) v T U E,
    (U :: nil) |-c t in T ; E ->
    nil |- v in U ->
    nil |-c substcomp v t in T ; E) /\
  (forall (t:handlerlist) v T U E,
    (U :: nil) |-h t in T ; E ->
    nil |- v in U ->
    nil |-h substhandlerlist v t in T ; E).
Proof.
  unfold substval, substcomp.
  replace 0 with (@length nat nil); auto.
  assert (forall t, @nil t = nil ++ nil); auto.
  rewrite H.
  assert (H' := substitution_preserves_typing).
  inversion H'.
  split; try split; intros; simpl in H0.
  - apply H0 with (U := U); auto.
  - apply H1 with (U := U); auto.
  - apply H1 with (U := U); auto.
Qed.

Lemma handlerlist_typing : forall Gamma hl o c T E,
  opcase hl o c ->
  Gamma |-h hl in T ; E ->
  (tarr (returnty o) E T :: paramty o :: Gamma) |-c c in T ; E.
Proof.
  intros.
  generalize dependent T.
  generalize dependent E.
  induction H; intros.
  - inversion_try_solve H0; auto.
  - inversion_try_solve H1.
    apply IHopcase in H9; auto.
Qed.

Lemma opcase_ops_of : forall hl o c,
  opcase hl o c -> o ∈ ops_of hl.
Proof.
  intros.
  induction H; set_solver.
Qed.

Lemma opcase_cons : forall o o' c c' r,
  o <> o' -> opcase (hcons o' c' r) o c -> opcase r o c.
Proof.
  intros.
  inversion_try_solve H0.
  - contradiction.
  - auto.
Qed.

Lemma opcase_cons_op_neq : forall o o' c r,
  (forall c', ~(opcase (hcons o c r) o' c')) -> o <> o'.
Proof.
  intros.
  destruct (Nat.eq_dec o o').
  - subst.
    specialize (H c).
    exfalso.
    apply H.
    constructor.
  - auto.
Qed.

Lemma opcase_cons_remove : forall o o' c r,
  (forall c', ~(opcase (hcons o c r) o' c')) -> (forall c', ~(opcase r o' c')).
Proof.
  unfold not.
  intros.
  assert (H' := H).
  apply opcase_cons_op_neq in H'.
  induction H0.
  - specialize (H co).
    apply H.
    constructor.
    + auto.
    + constructor.
  - apply IHopcase; auto.
    intros.
    specialize (H c').
    apply H.
    constructor; auto.
    constructor; auto.
    apply opcase_cons in H2; auto.
Qed.

Lemma opcase_not_ops_of : forall hl o,
  (forall c, ~(opcase hl o c)) -> ~(o ∈ ops_of hl).
Proof.
  induction hl; intros.
  - simpl. set_solver.
  - assert (H' := H).
    apply opcase_cons_op_neq in H'.
    simpl.
    rewrite not_elem_of_union.
    split.
    + set_solver.
    + apply IHhl.
      unfold not.
      intros.
      specialize (H c0).
      apply H.
      auto.
Qed.

Theorem preservation : forall Gamma t t' T E,
  Gamma |-c t in T ; E ->
  t ===> t' ->
  Gamma |-c t' in T ; E.
Proof with eauto.
  intros.
  generalize dependent t'.
  induction H; intros.
  - inversion_try_solve H0.
  - inversion_try_solve H1.
    inversion_try_solve H.
    unfold substcomp.
    replace Gamma with ([] ++ Gamma); auto.
    replace 0 with (@length ty []); auto.
    apply substitution_preserves_typing with (U := T1); auto.
  - inversion_try_solve H1.
    + inversion_try_solve H.
      unfold substcomp.
      replace Gamma with ([] ++ Gamma); auto.
      replace 0 with (@length ty []); auto.
      apply substitution_preserves_typing with (U := T1); auto.
    + apply T_Do with (T1 := T1); auto.
    + inversion_try_solve H.
      apply T_Op; auto.
      apply T_Do with (T1 := T1); auto.
      replace (T1 :: returnty o :: Gamma) with ((take 1 (T1 :: Gamma)) ++ [returnty o] ++ (drop 1 (T1 :: Gamma))); auto.
      replace 1 with (length [returnty o]) at 1; auto.
      apply shift_typing; auto.
  - inversion_try_solve H2.
  - inversion_try_solve H.
    inversion_try_solve H1.
    + apply T_Handle with (E1 := E1) (T1 := T1); auto.
    + inversion_try_solve H0.
      unfold substcomp.
      replace Gamma with ([] ++ Gamma); auto.
      replace 0 with (@length ty []); auto.
      apply substitution_preserves_typing with (U := T1); auto.
    + inversion_try_solve H0.
      unfold substcomp.
      replace Gamma with ([] ++ Gamma); auto.
      replace 0 with (@length ty []) at 1; auto.
      apply substitution_preserves_typing with (U := paramty o); auto.
      replace 0 with (@length ty []) at 1; auto.
      apply substitution_preserves_typing with (U := tarr (returnty o) E2 T2); simpl; auto.
      * apply handlerlist_typing with (Gamma := Gamma) (T := T2) (E := E2) in H6; auto.
      * constructor.
        apply T_Handle with (T1 := T1) (E1 := E1); auto.
        { replace 2 with (length [returnty o; paramty o]); auto.
          replace (returnty o :: paramty o :: Gamma) with ([returnty o; paramty o] ++ Gamma); auto.
          apply shiftn; auto. }
        { replace 1 with (length [paramty o]) at 1; auto.
          replace (returnty o :: paramty o :: Gamma) with
            ((take 1 (returnty o :: Gamma)) ++ [paramty o] ++ (drop 1 (returnty o :: Gamma))); auto.
          apply shift_typing; auto. }
    + inversion_try_solve H0.
      apply T_Op; auto.
      * apply T_Handle with (E1 := E1) (T1 := T1); auto.
        replace 1 with (length [returnty o]); auto.
        replace (returnty o :: Gamma) with ([returnty o] ++ Gamma); auto.
        apply shiftn.
        apply T_Handler; auto.
      * apply opcase_not_ops_of in H6.
        set_solver.
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.
Definition stuck (t:comp) : Prop :=
  (normal_form step) t /\ ~(value t).

Corollary soundness : forall t t' T,
  nil |-c t in T ; empty ->
  t ===>* t' ->
  ~(stuck t').
Proof.
  intros.
  unfold stuck.
  unfold normal_form.
  unfold not.
  intros [H1 H2].
  induction H0.
  - apply progress in H.
    inversion H; try contradiction.
  - apply IHmulti; auto.
    apply preservation with (t := x); auto.
Qed.
