Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.

Require Import Maps.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; 
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.
Ltac solve_by_invert := solve_by_inverts 1.
Ltac inversion_try_solve H := inversion H; subst; try reflexivity; try solve_by_invert.
Ltac inv H := inversion_try_solve H; auto.

Inductive ty : Type :=
  | tunit : ty
  | tarr : ty -> ty -> ty.

Hint Constructors ty.

Inductive term : Type :=
  | unit : term
  | bound : nat -> term
  | free : id -> term
  | app : term -> term -> term
  | abs : term -> term.

Hint Constructors term.

Fixpoint open' k u t : term :=
  match t with
  | unit => t
  | bound n => if n =? k then u else t
  | free _ => t
  | app t1 t2 => app (open' k u t1) (open' k u t2)
  | abs t' => abs (open' (S k) u t')
  end.

Definition open u t := open' 0 u t.
Definition openVar x t := open (free x) t.

Fixpoint close' k x t : term :=
  match t with
  | unit => t
  | bound _ => t
  | free y => if beq_id y x then bound k else t
  | app t1 t2 => app (close' k x t1) (close' k x t2)
  | abs t' => abs (close' (S k) x t')
  end.

Definition close x t := close' 0 x t.

Definition subst x u t := open u (close x t).

Inductive lc' : nat -> term -> Prop :=
  | lc_unit : forall k,
    lc' k unit
  | lc_bound : forall k n,
    n < k ->
    lc' k (bound n)
  | lc_free : forall k n,
    lc' k (free n)
  | lc_app : forall k t1 t2,
    lc' k t1 ->
    lc' k t2 ->
    lc' k (app t1 t2)
  | lc_abs : forall k t,
    lc' (S k) t ->
    lc' k (abs t).

Definition lc t := lc' 0 t.

Inductive value : term -> Prop :=
  | value_unit :
    value unit
  | value_abs : forall t,
    lc (abs t) ->
    value (abs t).

Inductive step : term -> term -> Prop :=
  | step_abs : forall t1 t2,
    value t2 ->
    step (app (abs t1) t2) (open t2 t1)
  | step_app1 : forall t1 t1' t2,
    step t1 t1' ->
    step (app t1 t2) (app t1' t2)
  | step_app2 : forall t1 t2 t2',
    value t1 ->
    step t2 t2' ->
    step (app t1 t2) (app t1 t2').

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

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic.
  intros.
  generalize dependent y1.
  induction H0; intros.
  - inv H0.
    inv H5.
  - inv H.
    + apply IHstep in H4.
      rewrite H4.
      auto.
    + inv H0.
  - inv H1.
    + inv H0.
    + inv H5.
    + apply IHstep in H6.
      rewrite H6.
      auto.
Qed.

Definition env := partial_map ty.

Inductive type : env -> term -> ty -> Prop :=
  | type_unit : forall E,
    type E unit tunit
  | type_free : forall E n T,
    E n = Some T ->
    type E (free n) T
  | type_app : forall E t1 t2 T1 T2,
    type E t1 (tarr T1 T2) ->
    type E t2 T1 ->
    type E (app t1 t2) T2
  | type_abs : forall E t x T1 T2,
    E x = None ->
    type (update E x T1) (openVar x t) T2 ->
    type E (abs t) (tarr T1 T2).

Hint Constructors type.

Theorem type_lc : forall t T,
  type empty t T <-> lc t.
Proof.
  remember empty as E.
  intros.
  split; intros.
  - induction H; subst; constructor.
    + apply IHtype1. auto.
    + apply IHtype2. auto.
    + 

Theorem progress : forall t T,
  type empty t T ->
  value t \/ exists t', step t t'.
Proof.
  remember empty as E.
  intros.
  induction H; subst.
  - left.
    constructor.
  - inv H.
  - assert (@empty ty = empty); auto.
    assert (@empty ty = empty); auto.
    apply IHtype1 in H1.
    apply IHtype2 in H2.
    destruct H1; destruct H2.
    + 