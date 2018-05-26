Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.

(* ast *)
Inductive ty : Type :=
  | tunit : ty
  | tvar : nat -> ty
  | tarr : ty -> ty -> ty
  | tforall : ty -> ty
  | texists : ty -> ty
  | tprod : ty -> ty -> ty
  | tsum : ty -> ty -> ty.

Hint Constructors ty.

Inductive term : Type :=
  | unit : term
  | var : nat -> term
  | abs : term -> term
  | app : term -> term -> term
  | pair : term -> term -> term
  | inl : term -> term
  | inr : term -> term
  | prod_elim : term -> term -> term
  | sum_elim : term -> term -> term -> term.

Hint Constructors term.

(* substitution *)
Fixpoint shift' (d:nat) (c:nat) (t:term) : term :=
  match t with
  | unit => t
  | var k => if k <? c then t else var (k + d)
  | abs t' => abs (shift' d (S c) t')
  | app t1 t2 => app (shift' d c t1) (shift' d c t2)
  | pair t1 t2 => pair (shift' d c t1) (shift' d c t2)
  | inl t' => inl (shift' d c t')
  | inr t' => inr (shift' d c t')
  | prod_elim t1 t2 => prod_elim (shift' d c t1) (shift' d c t2)
  | sum_elim t1 t2 t3 => sum_elim (shift' d c t1) (shift' d c t2) (shift' d c t3)
  end.

Definition shift d t := shift' d 0 t.

Fixpoint subst' (j:nat) (s:term) (t:term) : term :=
  match t with
  | unit => t
  | var k => if k =? j then s
              else if k <? j then t else var (pred k)
  | abs t' => abs (subst' (S j) (shift 1 s) t')
  | app t1 t2 => app (subst' j s t1) (subst' j s t2)
  | pair t1 t2 => pair (subst' j s t1) (subst' j s t2)
  | inl t' => inl (subst' j s t')
  | inr t' => inr (subst' j s t')
  | prod_elim t1 t2 => prod_elim (subst' j s t1) (subst' j s t2)
  | sum_elim t1 t2 t3 => sum_elim (subst' j s t1) (subst' j s t2) (subst' j s t3)
  end.

Definition subst s t := subst' 0 s t.

Hint Unfold shift.
Hint Unfold subst.

Fixpoint shift_ty' (d:nat) (c:nat) (t:ty) : ty :=
  match t with
  | tunit => t
  | tvar k => if k <? c then t else tvar (k + d)
  | tarr t1 t2 => tarr (shift_ty' d c t1) (shift_ty' d c t2)
  | tforall t' => tforall (shift_ty' d (S c) t')
  | texists t' => texists (shift_ty' d (S c) t')
  | tprod t1 t2 => tprod (shift_ty' d c t1) (shift_ty' d c t2)
  | tsum t1 t2 => tsum (shift_ty' d c t1) (shift_ty' d c t2)
  end.

Definition shift_ty d t := shift_ty' d 0 t.

Fixpoint subst_ty' (j:nat) (s:ty) (t:ty) : ty :=
  match t with
  | tunit => t
  | tvar k => if k =? j then s
              else if k <? j then t else tvar (pred k)
  | tarr t1 t2 => tarr (subst_ty' j s t1) (subst_ty' j s t2)
  | tforall t' => tforall (subst_ty' (S j) (shift_ty 1 s) t')
  | texists t' => texists (subst_ty' (S j) (shift_ty 1 s) t')
  | tprod t1 t2 => tprod (subst_ty' j s t1) (subst_ty' j s t2)
  | tsum t1 t2 => tsum (subst_ty' j s t1) (subst_ty' j s t2)
  end.

Definition subst_ty s t := subst_ty' 0 s t.

Hint Unfold shift_ty.
Hint Unfold subst_ty.

(* typing *)
Notation context := (list ty).

Inductive has_type : context -> term -> ty -> Prop :=
  | T_unit : forall gamma,
    has_type gamma unit tunit
  | T_var : forall gamma n t,
    nth_error gamma n = Some t ->
    has_type gamma (var n) t
  | T_abs : forall gamma e t1 t2,
    has_type (t1 :: gamma) e t2 ->
    has_type gamma (abs e) (tarr t1 t2)
  | T_app : forall gamma f x t1 t2,
    has_type gamma f (tarr t1 t2) ->
    has_type gamma x t1 ->
    has_type gamma (app f x) t2
  | T_forall_intro : forall gamma e t,
    has_type gamma e t ->
    has_type gamma e (tforall t)
  | T_forall_elim : forall gamma e t u,
    has_type gamma e (tforall t) ->
    has_type gamma e (subst_ty u t)
  | T_exists_intro : forall gamma e t u,
    has_type gamma e (subst_ty u t) ->
    has_type gamma e (texists t)
  | T_exists_elim : forall gamma e t,
    has_type gamma e (texists t) ->
    has_type gamma e t
  | T_pair : forall gamma e1 e2 t1 t2,
    has_type gamma e1 t1 ->
    has_type gamma e2 t2 ->
    has_type gamma (pair e1 e2) (tprod t1 t2)
  | T_inl : forall gamma e t1 t2,
    has_type gamma e t1 ->
    has_type gamma (inl e) (tsum t1 t2)
  | T_inr : forall gamma e t1 t2,
    has_type gamma e t2 ->
    has_type gamma (inr e) (tsum t1 t2)
  | T_prod_elim : forall gamma e f t1 t2 t3,
    has_type gamma e (tprod t1 t2) ->
    has_type (t1 :: t2 :: gamma) f t3 ->
    has_type gamma (prod_elim e f) t3
  | T_sum_elim : forall gamma e f g t1 t2 t3,
    has_type gamma e (tsum t1 t2) ->
    has_type (t1 :: gamma) f t3 ->
    has_type (t2 :: gamma) g t3 ->
    has_type gamma (sum_elim e f g) t3.

Hint Constructors has_type.

(* testing *)
Example test_ty1 :
  has_type nil (abs (var 0)) (tarr tunit tunit).
Proof.
  apply T_abs.
  apply T_var.
  reflexivity.
Qed.

Example test_ty2 :
  has_type nil (abs (var 0)) (tforall (tarr (tvar 0) (tvar 0))).
Proof.
  apply T_forall_intro.
  apply T_abs.
  apply T_var.
  reflexivity.
Qed.

Example test_ty3 :
  has_type nil (app (abs (var 0)) unit) tunit.
Proof.
  apply T_app with (t1 := tunit).
  - apply T_abs.
    apply T_var.
    reflexivity.
  - apply T_unit.
Qed.

Example test_ty4 :
  has_type nil (app (abs (var 0)) unit) tunit.
Proof.
  apply T_app with (t1 := tunit).
  - replace (tarr tunit tunit) with (subst_ty tunit (tarr (tvar 0) (tvar 0))).
    + apply T_forall_elim.
      apply T_forall_intro.
      apply T_abs.
      apply T_var.
      reflexivity.
    + reflexivity.
  - apply T_unit.
Qed.

Example test_ty5 :
  has_type nil (abs (var 0)) (texists (tarr (tvar 0) (tvar 0))).
Proof.
  apply T_exists_intro with (u := tunit).
  unfold subst_ty.
  simpl.
  apply T_abs.
  apply T_var.
  reflexivity.
Qed.

Example test_ty6 :
  has_type nil (pair unit (abs (var 0))) (texists (tprod (tvar 0) (tarr (tvar 0) (tvar 0)))).
Proof.
  apply T_exists_intro with (u := tunit).
  unfold subst_ty.
  simpl.
  apply T_pair.
  - auto.
  - auto.
Qed.

Example test_ty7 :
  has_type ((texists (tprod (tvar 0) (tarr (tvar 0) tunit))) :: nil) (prod_elim (var 0) (app (var 1) (var 0))) tunit.
Proof.
  apply T_prod_elim with (t1 := tvar 0) (t2 := tarr (tvar 0) tunit).
  - auto.
  - apply T_app with (t1 := tvar 0).
    + auto.
    + auto.
Qed.
