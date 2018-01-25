Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.
Require Import Util.

(* ast *)
Inductive ty : Type :=
  | tarr : ty -> ty -> ty
  | tunit : ty.

Inductive term : Type :=
  | unit : term
  | var : nat -> term
  | abs : term -> term
  | app : term -> term -> term.

(* closed *)
Inductive closed' : nat -> term -> Prop :=
  | C_Unit : forall n,
    closed' n unit
  | C_Var : forall n x,
    x < n ->
    closed' n (var x)
  | C_Abs : forall n t,
    closed' (S n) t ->
    closed' n (abs t)
  | C_App : forall n t1 t2,
    closed' n t1 ->
    closed' n t2 ->
    closed' n (app t1 t2).

Hint Constructors closed'.

Definition closed t := closed' 0 t.

Hint Unfold closed.

(* substitution *)
Fixpoint shift' (d:nat) (c:nat) (t:term) : term :=
  match t with
  | unit => t
  | var k => if k <? c then t else var (k + d)
  | abs t' => abs (shift' d (S c) t')
  | app t1 t2 => app (shift' d c t1) (shift' d c t2)
  end.

Definition shift d t := shift' d 0 t.

Fixpoint subst' (j:nat) (s:term) (t:term) : term :=
  match t with
  | unit => t
  | var k => if k =? j then s
              else if k <? j then t else var (pred k)
  | abs t' => abs (subst' (S j) (shift 1 s) t')
  | app t1 t2 => app (subst' j s t1) (subst' j s t2)
  end.

Definition subst s t := subst' 0 s t.

Hint Unfold shift.
Hint Unfold subst.

(* semantics *)
Inductive value : term -> Prop :=
  | V_Unit :
    value unit
  | V_Abs : forall t,
     value (abs t).

Reserved Notation "c1 '==>' c2" (at level 40).

Inductive step : term -> term -> Prop :=
  | S_AppAbs : forall t1 t2,
    value t2 ->
    (app (abs t1) t2) ==> subst t2 t1
  | S_App1 : forall t1 t1' t2,
    t1 ==> t1' ->
    app t1 t2 ==> app t1' t2
  | S_App2 : forall t1 t2 t2',
    value t1 ->
    t2 ==> t2' ->
    app t1 t2 ==> app t1 t2'

where "c1 '==>' c2" := (step c1 c2).

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
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* typing rules *)
Definition context := list ty.

Reserved Notation "Gamma '|-' t 'in' T" (at level 40).

Inductive has_type : context -> term -> ty -> Prop :=
  | T_Unit : forall Gamma,
    Gamma |- unit in tunit
  | T_Var : forall Gamma x T,
    nth_error Gamma x = Some T ->
    Gamma |- var x in T
  | T_Abs : forall Gamma t T1 T2,
    (T1 :: Gamma) |- t in T2 ->
    Gamma |- abs t in tarr T1 T2
  | T_App : forall Gamma t1 t2 T1 T2,
    Gamma |- t1 in tarr T1 T2 ->
    Gamma |- t2 in T1 ->
    Gamma |- app t1 t2 in T2

where "Gamma '|-' t 'in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* theorems *)
Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic.
  intros.
  generalize dependent y1.
  induction H0; intros;
    inversion_try_solve H;
    inversion_try_solve H0;
    inversion_try_solve H;
    inversion_try_solve H1;
    try apply_rewrite_solve IHstep H3;
    try apply_rewrite_solve IHstep H5;
    try apply_rewrite_solve IHstep H7;
    try apply_rewrite_solve IHstep H8.
Qed.

Theorem progress : forall t T,
  nil |- t in T ->
  value t \/ exists t', t ==> t'.
Proof.
  remember (@nil ty) as Gamma.
  intros.
  induction H; try (left; constructor).
  - rewrite HeqGamma in H.
    rewrite nth_error_nil in H.
    inversion H.
  - right.
    assert (HeqGamma' := HeqGamma).
    apply IHhas_type1 in HeqGamma.
    apply IHhas_type2 in HeqGamma'.
    clear IHhas_type1; clear IHhas_type2.
    inversion HeqGamma; inversion HeqGamma'.
    + inversion_try_solve H1.
      exists (subst t2 t).
      constructor.
      assumption.
    + inversion H2.
      exists (app t1 x).
      constructor; assumption.
    + inversion H1.
      exists (app x t2).
      constructor; assumption.
    + inversion H1.
      exists (app x t2).
      constructor; assumption.
Qed.

Lemma typable_closed_length : forall t T Gamma,
  Gamma |- t in T -> closed' (length Gamma) t.
Proof.
  intros.
  induction H; subst; constructor; auto; simpl.
  apply nth_error_length in H; assumption.
Qed.

Corollary typeable_empty_closed : forall t T,
  nil |- t in T -> closed t.
Proof.
  intros.
  apply typable_closed_length in H.
  auto.
Qed.

Lemma closed_weakening : forall n m t,
  closed' n t -> m >= n -> closed' m t.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try constructor.
  - omega.
  - apply IHclosed'.
    omega.
  - apply IHclosed'1.
    omega.
  - apply IHclosed'2.
    omega.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
  Gamma |- t in T ->
  (Gamma ++ Gamma') |- t in T.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H; intros; try constructor.
  - apply nth_error_weakening.
    assumption.
  - simpl in IHhas_type.
    apply IHhas_type.
  - apply T_App with (T1 := T1).
    + apply IHhas_type1.
    + apply IHhas_type2.
Qed.

Lemma shift_closed : forall n m t,
  closed' n t ->
  shift' m n t = t.
Proof.
  intros.
  generalize dependent n.
  induction t; intros; auto; simpl; inversion_try_solve H.
  - rewrite <- Nat.ltb_lt in H2.
    rewrite H2.
    auto.
  - apply IHt in H2.
    rewrite H2.
    auto.
  - apply IHt1 in H3.
    apply IHt2 in H4.
    rewrite H3; rewrite H4.
    auto.
Qed.

Lemma subst_closed : forall n t v,
  closed' n t ->
  subst' n v t = t.
Proof.
  intros.
  generalize dependent n.
  generalize dependent v.
  induction t; intros; auto; simpl; inversion_try_solve H.
  - simpl.
    destruct (n =? n0) eqn:eq; auto.
    apply beq_nat_true in eq.
    omega.
    rewrite <- Nat.ltb_lt in H2.
    rewrite H2.
    auto.
  - apply IHt with (v := shift 1 v) in H2.
    rewrite H2.
    auto.
  - apply IHt1 with (v := v) in H3.
    apply IHt2 with (v := v) in H4.
    rewrite H3, H4.
    auto.
Qed.

Lemma shift_0 : forall m t,
  shift' 0 m t = t.
Proof.
  intros.
  generalize dependent m.
  induction t; intros; simpl; auto.
  - rewrite Nat.add_0_r.
    destruct (n <? m); auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

Lemma shift_typing : forall Gamma m t T U,
  Gamma |- t in T ->
  (firstn m Gamma ++ U :: skipn m Gamma) |- shift' 1 m t in T.
Proof.
  intros.
  generalize dependent U.
  generalize dependent m.
  generalize dependent Gamma.
  generalize dependent T.
  induction t; intros; simpl; inversion_try_solve H; try constructor.
  - destruct (n <? m) eqn:eq; constructor.
    + apply nth_error_weakening.
      apply nth_error_firstn.
      rewrite Nat.ltb_lt in eq.
      omega.
      auto.
    + apply Nat.ltb_ge in eq.
      rewrite Nat.add_1_r.
      apply nth_error_firstn_cons_skipn; auto.
  - rewrite app_comm_cons.
    rewrite <- firstn_cons.
    rewrite skipn_cons with (x := T1).
    apply IHt.
    auto.
  - apply IHt1 with (m := m) (U := U) in H3.
    apply IHt2 with (m := m) (U := U) in H5.
    apply T_App with (T1 := T1); auto.
Qed.

Lemma substitution_preserves_typing : forall Gamma Gamma' U t v T,
  (Gamma ++ U :: Gamma') |- t in T ->
  (Gamma ++ Gamma') |- v in U ->
  (Gamma ++ Gamma') |- subst' (length Gamma) v t in T.
Proof.
  intros.
  generalize dependent v.
  generalize dependent T.
  generalize dependent Gamma.
  induction t; intros;
    inversion_try_solve H; simpl; auto; simpl.
  - destruct (n ?= length Gamma) eqn:eq.
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
  - constructor.
    apply (IHt (T1 :: Gamma)); auto.
    simpl.
    unfold shift.
    apply shift_typing with (m := 0) (U := T1) in H0.
    simpl in H0.
    auto.
  - apply T_App with (T1 := T1).
    apply IHt1 with (v := v) in H4; auto.
    apply IHt2 with (v := v) in H6; auto.
Qed.

Lemma substitution_preserves_typing_nil : forall U t v T,
  (U :: nil) |- t in T ->
  nil |- v in U ->
  nil |- subst v t in T.
Proof.
  intros.
  unfold subst.
  replace 0 with (@length nat nil); auto.
  assert (forall t, @nil t = nil ++ nil); auto.
  rewrite H1.
  apply substitution_preserves_typing with (U := U); auto.
Qed.

Theorem preservation : forall t t' T,
  nil |- t in T ->
  t ==> t' ->
  nil |- t' in T.
Proof with eauto.
  remember nil as Gamma.
  intros.
  generalize dependent t'.
  induction H; intros; subst; try solve [inversion H0].
  inversion_try_solve H1.
  - inversion_try_solve H.
    apply substitution_preserves_typing_nil with (U := T1); auto.
  - apply IHhas_type1 in H5; auto.
    apply T_App with (T1 := T1); auto.
  - apply IHhas_type2 in H6; auto.
    apply T_App with (T1 := T1); auto.
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.
Definition stuck (t:term) : Prop :=
  (normal_form step) t /\ ~(value t).

Corollary soundness : forall t t' T,
  nil |- t in T ->
  t ==>* t' ->
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
