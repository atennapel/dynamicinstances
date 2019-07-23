(*
  A formalization of simple algebraic effects with static instances, with the following limitations:
  - a handler can only handle one operation.
*)
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.
Require Import Util.
From stdpp Require Import gmap.

(* effects and static instances *)
Definition eff := nat.
Notation effs := (gset eff).
Definition eff_inst := nat.
Notation eff_insts := (gset eff_inst).
Definition eff_op := nat.
Notation eff_ops := (gset eff_op).

Record eff_annot := EffAnnot {
  eff_annot_inst : eff_inst;
  eff_annot_op : eff_op;
}.

Instance eff_annot_eq_dec : EqDecision eff_annot.
Proof. solve_decision. Defined.

Instance eff_annot_countable : Countable eff_annot.
Proof.
  apply (inj_countable' (fun a => (eff_annot_inst a, eff_annot_op a))
                        (fun '(n,o) => EffAnnot n o)).
  by intros [].
Qed.

(* effect annotation for types *)
Notation eff_annots := (gset eff_annot).

(* ast *)
Inductive ty : Type :=
  | tarr : ty -> eff_annots -> ty -> ty
  | tunit : ty
  | thandler : eff_annots -> ty -> eff_annots -> ty -> ty.

Inductive val : Type :=
  | unit : val
  | var : nat -> val
  | abs : comp -> val
  | handler : comp -> eff_annot -> comp -> val (* one comp for the return clause, one for the single operation *)
with comp : Type :=
  | ret : val -> comp
  | app : val -> val -> comp
  | do : comp -> comp -> comp
  | opc : eff_annot -> val -> comp -> comp
  | handle : val -> comp -> comp.

Scheme val_comp_ind := Induction for val Sort Prop
  with comp_val_ind := Induction for comp Sort Prop.
Combined Scheme val_comp_mutind from val_comp_ind, comp_val_ind.

(* effect environment *)
Record eff_env := EffEnv {
  eff_env_effs : effs;
  eff_env_ops : eff_ops;
  eff_env_insts : eff_insts;

  eff_env_op_to_eff : eff_op -> eff;
  eff_env_inst_to_eff : eff_inst -> eff;

  eff_env_paramty : eff_op -> ty;
  eff_env_returnty : eff_op -> ty;
}.

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
  | C_Handler : forall n cr o co,
    closedcomp' (S n) cr ->
    closedcomp' (S (S n)) co ->
    closedval' n (handler cr o co)
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
    closedcomp' n (handle v c).

Scheme closed_val_comp_ind := Induction for closedval' Sort Prop
  with closed_comp_val_ind := Induction for closedcomp' Sort Prop.
Combined Scheme closed_val_comp_mutind from closed_val_comp_ind, closed_comp_val_ind.

Hint Constructors closedval'.
Hint Constructors closedcomp'.

Definition closedval t := closedval' 0 t.
Definition closedcomp t := closedcomp' 0 t.

Hint Unfold closedval.
Hint Unfold closedcomp.

(* substitution *)
Fixpoint shiftval' (d:nat) (c:nat) (t:val) : val :=
  match t with
  | unit => t
  | var k => if k <? c then t else var (k + d)
  | abs t' => abs (shiftcomp' d (S c) t')
  | handler cr o co => handler (shiftcomp' d (S c) cr) o (shiftcomp' d (S (S c)) co)
  end
with shiftcomp' (d:nat) (c:nat) (t:comp) : comp :=
  match t with
  | ret t' => ret (shiftval' d c t')
  | app t1 t2 => app (shiftval' d c t1) (shiftval' d c t2)
  | do t1 t2 => do (shiftcomp' d c t1) (shiftcomp' d (S c) t2)
  | opc o v t => opc o (shiftval' d c v) (shiftcomp' d (S c) t)
  | handle v t => handle (shiftval' d c v) (shiftcomp' d c t)
  end.

Definition shiftval d t := shiftval' d 0 t.
Definition shiftcomp d t := shiftcomp' d 0 t.

Fixpoint substval' (j:nat) (s:val) (t:val) : val :=
  match t with
  | unit => t
  | var k => if k =? j then s
              else if k <? j then t else var (pred k)
  | abs t' => abs (substcomp' (S j) (shiftval 1 s) t')
  | handler cr o co => handler (substcomp' (S j) (shiftval 1 s) cr) o (substcomp' (S (S j)) (shiftval 2 s) co)
  end
with substcomp' (j:nat) (s:val) (t:comp) : comp :=
  match t with
  | ret t' => ret (substval' j s t')
  | app t1 t2 => app (substval' j s t1) (substval' j s t2)
  | do t1 t2 => do (substcomp' j s t1) (substcomp' (S j) (shiftval 1 s) t2)
  | opc o v t => opc o (substval' j s v) (substcomp' (S j) (shiftval 1 s) t)
  | handle v t => handle (substval' j s v) (substcomp' j s t)
  end.

Definition substval s t := substval' 0 s t.
Definition substcomp s t := substcomp' 0 s t.

Hint Unfold shiftval.
Hint Unfold shiftcomp.
Hint Unfold substval.
Hint Unfold substcomp.

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
  | S_Handle : forall cr o co c c',
    c ===> c' ->
    handle (handler cr o co) c ===> handle (handler cr o co) c'
  | S_HandleReturn : forall cr o co v,
    handle (handler cr o co) (ret v) ===> substcomp v cr
  | S_HandleOp1 : forall cr o co v c,
    handle (handler cr o co) (opc o v c) ===>
      substcomp v (substcomp (abs (handle (handler (shiftcomp' 2 1 cr) o (shiftcomp' 2 2 co)) (shiftcomp' 1 1 c))) co)
  | S_HandleOp2 : forall cr o o' co v c,
    o <> o' ->
    handle (handler cr o co) (opc o' v c) ===>
      opc o' v (handle (handler (shiftcomp' 1 1 cr) o (shiftcomp' 1 2 co)) c)

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
Definition context := list ty.

Reserved Notation "Env ',' Gamma '|-' t 'in' T" (at level 40).
Reserved Notation "Env ',' Gamma '|-c' t 'in' T ';' E" (at level 40).

Definition valid_eff_annot (Env:eff_env) (o:eff_annot) :=
  (eff_annot_inst o ∈ eff_env_insts Env) /\
  (eff_annot_op o ∈ eff_env_ops Env) /\
  (eff_env_inst_to_eff Env (eff_annot_inst o) = eff_env_op_to_eff Env (eff_annot_op o)).

Inductive has_type_val : eff_env -> context -> val -> ty -> Prop :=
  | T_Unit : forall Env Gamma,
    Env, Gamma |- unit in tunit
  | T_Var : forall Env Gamma x T,
    nth_error Gamma x = Some T ->
    Env, Gamma |- var x in T
  | T_Abs : forall Env Gamma t T1 E T2,
    Env, (T1 :: Gamma) |-c t in T2 ; E ->
    Env, Gamma |- abs t in tarr T1 E T2
  | T_Handler : forall Env Gamma cr o co E1 T1 E2 T2,
    valid_eff_annot Env o ->
    Env, (T1 :: Gamma) |-c cr in T2 ; E2 ->
    Env, (tarr (eff_env_returnty Env (eff_annot_op o)) E2 T2 :: (eff_env_paramty Env (eff_annot_op o)) :: Gamma) |-c co in T2 ; E2 ->
    (E1 ∖  {[o]}) ⊆ E2 ->
    Env, Gamma |- handler cr o co in thandler E1 T1 E2 T2

where "Env ',' Gamma '|-' t 'in' T" := (has_type_val Env Gamma t T)

with has_type_comp : eff_env -> context -> comp -> ty -> eff_annots -> Prop :=
  | T_Return : forall Env Gamma v T E,
    Env, Gamma |- v in T ->
    Env, Gamma |-c ret v in T ; E
  | T_App : forall Env Gamma t1 t2 T1 E T2,
    Env, Gamma |- t1 in tarr T1 E T2 ->
    Env, Gamma |- t2 in T1 ->
    Env, Gamma |-c app t1 t2 in T2 ; E
  | T_Do : forall Env Gamma t1 t2 T1 E T2,
    Env, Gamma |-c t1 in T1 ; E ->
    Env, (T1 :: Gamma) |-c t2 in T2 ; E ->
    Env, Gamma |-c do t1 t2 in T2; E
  | T_Op : forall Env Gamma o v c T E,
    valid_eff_annot Env o ->
    Env, Gamma |- v in eff_env_paramty Env (eff_annot_op o) ->
    Env, ((eff_env_returnty Env (eff_annot_op o)) :: Gamma) |-c c in T ; E ->
    o ∈ E ->
    Env, Gamma |-c opc o v c in T ; E
  | T_Handle : forall Env Gamma v c E1 T1 E2 T2,
    Env, Gamma |- v in thandler E1 T1 E2 T2 ->
    Env, Gamma |-c c in T1 ; E1 ->
    Env, Gamma |-c handle v c in T2 ; E2

where "Env ',' Gamma '|-c' t 'in' T ';' E" := (has_type_comp Env Gamma t T E).

Scheme has_type_val_comp_ind := Induction for has_type_val Sort Prop
  with has_type_comp_val_ind := Induction for has_type_comp Sort Prop.
Combined Scheme has_type_val_comp_mutind from has_type_val_comp_ind, has_type_comp_val_ind.

Hint Constructors has_type_val.
Hint Constructors has_type_comp.

(* theorems *)
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
  - apply IHstep in H6.
    rewrite H6.
    auto.
  - contradiction.
  - inversion_try_solve H0.
    contradiction.
Qed.

Lemma typable_closed_length :
  (forall Env Gamma t T, Env, Gamma |- t in T -> closedval' (length Gamma) t) /\
  (forall Env Gamma t T E, Env, Gamma |-c t in T ; E -> closedcomp' (length Gamma) t).
Proof.
  apply has_type_val_comp_mutind; intros; auto.
  constructor.
  apply nth_error_length in e; assumption.
Qed.

Lemma shift_closed :
  (forall n t, closedval' n t -> forall m, shiftval' m n t = t) /\
  (forall n t, closedcomp' n t -> forall m, shiftcomp' m n t = t).
Proof.
  apply closed_val_comp_mutind; intros; auto; simpl;
    try (rewrite H; auto);
    try (rewrite H0; auto);
    try (rewrite H; rewrite H0; auto).
  - rewrite <- Nat.ltb_lt in l.
    rewrite l.
    auto.
Qed.

Lemma progress_effects : forall Env t T E,
  Env, nil |-c t in T ; E ->
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
        exists (handle (handler cr o co) x).
        auto.
      * destruct H2 as [o'], H2 as [v], H2 as [k].
        subst.
        destruct (eff_annot_eq_dec o o').
        { subst.
          exists (substcomp v (substcomp (abs (handle (handler (shiftcomp' 2 1 cr) o' (shiftcomp' 2 2 co)) (shiftcomp' 1 1 k))) co)).
          auto. }
        { exists (opc o' v (handle (handler (shiftcomp' 1 1 cr) o (shiftcomp' 1 2 co)) k)).
          auto. }
Qed.

Theorem progress : forall Env t T,
  Env, nil |-c t in T ; empty ->
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

Corollary typable_closed_empty :
  (forall Env Gamma t T, Env, Gamma |- t in T -> Gamma = nil -> closedval t) /\
  (forall Env Gamma t T E, Env, Gamma |-c t in T ; E -> Gamma = nil -> closedcomp t).
Proof.
  assert (H' := typable_closed_length).
  split; intros; subst;
    apply typable_closed_length in H; simpl in H; auto.
Qed.

Lemma closed_weakening :
  (forall n t, closedval' n t -> forall m, m >= n -> closedval' m t) /\
  (forall n t, closedcomp' n t -> forall m, m >= n -> closedcomp' m t).
Proof.
  apply closed_val_comp_mutind;
    intros; auto;
    constructor; auto;
    try omega;
    try (apply H; omega);
    try (apply H0; omega).
Qed.

Lemma context_invariance :
  (forall Env Gamma t T, Env, Gamma |- t in T -> forall Gamma', Env, (Gamma ++ Gamma') |- t in T) /\
  (forall Env Gamma t T E, Env, Gamma |-c t in T ; E -> forall Gamma', Env, (Gamma ++ Gamma') |-c t in T ; E).
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

Lemma subst_closed :
  (forall n t, closedval' n t -> forall v, substval' n v t = t) /\
  (forall n t, closedcomp' n t -> forall v, substcomp' n v t = t).
Proof.
  apply closed_val_comp_mutind;
    intros;
    auto;
    simpl;
    try (rewrite H; auto);
    try (rewrite H0; auto);
    try (rewrite H; rewrite H0; auto).
  - assert (~(x = n)).
    omega.
    rewrite <- Nat.eqb_neq in H.
    rewrite H.
    rewrite <- Nat.ltb_lt in l.
    rewrite l.
    auto.
Qed.

Lemma shift_0 :
  (forall t m, shiftval' 0 m t = t) /\
  (forall t m, shiftcomp' 0 m t = t).
Proof.
  apply val_comp_mutind; intros; simpl; auto;
    try (rewrite H; auto);
    try (rewrite H0; auto);
    try (rewrite H; rewrite H0; auto).
  - rewrite Nat.add_0_r.
    destruct (n <? m); auto.
Qed.

Lemma shift_typing :
  (forall Env Gamma t T,
    Env, Gamma |- t in T ->
    forall m L,
      Env, (firstn m Gamma ++ L ++ skipn m Gamma) |- shiftval' (length L) m t in T) /\
  (forall Env Gamma t T E,
    Env, Gamma |-c t in T ; E ->
    forall m L,
      Env, (firstn m Gamma ++ L ++ skipn m Gamma) |-c shiftcomp' (length L) m t in T ; E).
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
  - apply H0 with (m := S (S m)).
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
Qed.

Lemma shift_typing1 :
  (forall Env Gamma t T,
    Env, Gamma |- t in T ->
    forall m U,
      Env, (firstn m Gamma ++ U :: skipn m Gamma) |- shiftval' 1 m t in T) /\
  (forall Env Gamma t T E,
    Env, Gamma |-c t in T ; E ->
    forall m U,
      Env, (firstn m Gamma ++ U :: skipn m Gamma) |-c shiftcomp' 1 m t in T ; E).
Proof.
  split; intros.
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
  (forall Env Gamma t T,
    Env, Gamma |- t in T ->
    forall U,
      Env, (U :: Gamma) |- shiftval 1 t in T) /\
  (forall Env Gamma t T E,
    Env, Gamma |-c t in T ; E ->
    forall U,
      Env, (U :: Gamma) |-c shiftcomp 1 t in T ; E).
Proof.
  split; intros.
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
  (forall Env Gamma t T,
    Env, Gamma |- t in T ->
    forall L,
      Env, (L ++ Gamma) |- shiftval (length L) t in T) /\
  (forall Env Gamma t T E,
    Env, Gamma |-c t in T ; E ->
    forall L,
      Env, (L ++ Gamma) |-c shiftcomp (length L) t in T ; E).
Proof.
  split; intros.
  - assert (L ++ Gamma = (take 0 Gamma) ++ L ++ (drop 0 Gamma)); auto.
    rewrite H0.
    unfold shiftval.
    apply shift_typing; auto.
  - assert (L ++ Gamma = (take 0 Gamma) ++ L ++ (drop 0 Gamma)); auto.
    rewrite H0.
    unfold shiftcomp.
    apply shift_typing; auto.
Qed.

Lemma substitution_preserves_typing :
  (forall (t:val) Env Gamma Gamma' v T U,
    Env, (Gamma ++ U :: Gamma') |- t in T ->
    Env, (Gamma ++ Gamma') |- v in U ->
    Env, (Gamma ++ Gamma') |- substval' (length Gamma) v t in T) /\
  (forall (t:comp) Env Gamma Gamma' v T U E,
    Env, (Gamma ++ U :: Gamma') |-c t in T ; E ->
    Env, (Gamma ++ Gamma') |- v in U ->
    Env, (Gamma ++ Gamma') |-c substcomp' (length Gamma) v t in T ; E).
Proof.
  apply val_comp_mutind; intros; simpl; auto; simpl.
  - inversion_try_solve H; auto.
  - inversion_try_solve H.
    destruct (n ?= length Gamma) eqn:eq.
    + apply nat_compare_eq in eq.
      subst.
      rewrite <- beq_nat_refl.
      rewrite nth_error_app in H4.
      inversion_try_solve H4.
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
      rewrite <- H4.
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
      rewrite Heqm.
      apply gt_to_geq_pred in eq.
      apply sub_same; auto.
      rewrite H3.
      apply nth_error_pred_app with (h := U).
      assert (n = S (m + length Gamma)).
      rewrite Heqm.
      rewrite <- sub_same2; auto.
      rewrite <- H5.
      auto.
  - inversion_try_solve H0.
    constructor.
    apply (H Env (T1 :: Gamma) Gamma' (shiftval 1 v) T2 U); auto.
    simpl.
    apply shift1; auto.
  - inversion_try_solve H1.
    constructor; auto.
    + apply (H Env (T1 :: Gamma)) with (U := U); auto.
      simpl.
      apply shift1; auto.
    + apply (H0 Env (tarr (eff_env_returnty Env (eff_annot_op e)) E2 T2 :: (eff_env_paramty Env (eff_annot_op e)) :: Gamma)) with (U := U); auto.
      assert ((tarr (eff_env_returnty Env (eff_annot_op e)) E2 T2 :: eff_env_paramty Env (eff_annot_op e) :: Gamma) ++ Gamma' = (tarr (eff_env_returnty Env (eff_annot_op e)) E2 T2 :: eff_env_paramty Env (eff_annot_op e) :: nil) ++ (Gamma ++ Gamma')); auto.
      rewrite H3.
      apply shiftn; auto.
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
    + apply (H0 Env (eff_env_returnty Env (eff_annot_op e) :: Gamma) Gamma' (shiftval 1 v0) T U); auto.
      apply shift1; auto.
  - inversion_try_solve H1.
    apply T_Handle with (E1 := E1) (T1 := T1); auto.
    + apply H with (U := U); auto.
    + apply H0 with (U := U); auto.
Qed.

Lemma substitution_preserves_typing_nil :
  (forall (t:val) Env v T U,
    Env, (U :: nil) |- t in T ->
    Env, nil |- v in U ->
    Env, nil |- substval v t in T) /\
  (forall (t:comp) Env v T U E,
    Env, (U :: nil) |-c t in T ; E ->
    Env, nil |- v in U ->
    Env, nil |-c substcomp v t in T ; E).
Proof.
  unfold substval, substcomp.
  replace 0 with (@length nat nil); auto.
  assert (forall t, @nil t = nil ++ nil); auto.
  rewrite H.
  assert (H' := substitution_preserves_typing).
  inversion H'.
  split; intros; simpl in H0.
  - apply H0 with (U := U); auto.
  - apply H1 with (U := U); auto.
Qed.

Theorem preservation : forall Env Gamma t t' T E,
  Env, Gamma |-c t in T ; E ->
  t ===> t' ->
  Env, Gamma |-c t' in T ; E.
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
      replace (T1 :: eff_env_returnty Env (eff_annot_op o) :: Gamma) with ((take 1 (T1 :: Gamma)) ++ [eff_env_returnty Env (eff_annot_op o)] ++ (drop 1 (T1 :: Gamma))); auto.
      replace 1 with (length [eff_env_returnty Env (eff_annot_op o)]) at 1; auto.
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
      apply substitution_preserves_typing with (U := eff_env_paramty Env (eff_annot_op o)); auto.
      replace 0 with (@length ty []) at 1; auto.
      apply substitution_preserves_typing with (U := tarr (eff_env_returnty Env (eff_annot_op o)) E2 T2); auto.
      simpl.
      apply T_Abs.
      apply T_Handle with (E1 := E1) (T1 := T1).
      * apply T_Handler; auto.
        { replace 2 with (length [eff_env_returnty Env (eff_annot_op o); eff_env_paramty Env (eff_annot_op o)]) at 1; auto.
          replace (T1 :: eff_env_returnty Env (eff_annot_op o) :: eff_env_paramty Env (eff_annot_op o) :: Gamma) with ((take 1 (T1 :: Gamma)) ++ [eff_env_returnty Env (eff_annot_op o); eff_env_paramty Env (eff_annot_op o)] ++ (drop 1 (T1 :: Gamma))); auto.
          apply shift_typing; auto. }
        { replace 2 with (length [eff_env_returnty Env (eff_annot_op o); eff_env_paramty Env (eff_annot_op o)]) at 1; auto.
          replace (tarr (eff_env_returnty Env (eff_annot_op o)) E2 T2 :: eff_env_paramty Env (eff_annot_op o) :: eff_env_returnty Env (eff_annot_op o) :: eff_env_paramty Env (eff_annot_op o) :: Gamma) with
            ((take 2 (tarr (eff_env_returnty Env (eff_annot_op o)) E2 T2 :: eff_env_paramty Env (eff_annot_op o) :: Gamma)) ++ [eff_env_returnty Env (eff_annot_op o); eff_env_paramty Env (eff_annot_op o)] ++
              (drop 2 (tarr (eff_env_returnty Env (eff_annot_op o)) E2 T2 :: eff_env_paramty Env (eff_annot_op o) :: Gamma))); auto.
          apply shift_typing; auto. }
      * replace 1 with (length [eff_env_paramty Env (eff_annot_op o)]) at 1; auto.
        replace (eff_env_returnty Env (eff_annot_op o) :: eff_env_paramty Env (eff_annot_op o) :: Gamma) with
          ((take 1 (eff_env_returnty Env (eff_annot_op o) :: Gamma)) ++ [eff_env_paramty Env (eff_annot_op o)] ++ (drop 1 (eff_env_returnty Env (eff_annot_op o) :: Gamma))); auto.
        apply shift_typing; auto.
    + inversion_try_solve H0.
      apply T_Op; auto.
      * apply T_Handle with (E1 := E1) (T1 := T1); auto.
        apply T_Handler; auto.
        { replace 1 with (length [eff_env_returnty Env (eff_annot_op o')]) at 1; auto.
          replace (T1 :: eff_env_returnty Env (eff_annot_op o') :: Gamma) with
            ((take 1 (T1 :: Gamma)) ++ [eff_env_returnty Env (eff_annot_op o')] ++ (drop 1 (T1 :: Gamma))); auto.
          apply shift_typing; auto. }
        { replace 1 with (length [eff_env_returnty Env (eff_annot_op o')]) at 1; auto.
          replace (tarr (eff_env_returnty Env (eff_annot_op o)) E2 T2 :: eff_env_paramty Env (eff_annot_op o) :: eff_env_returnty Env (eff_annot_op o') :: Gamma) with
            ((take 2 (tarr (eff_env_returnty Env (eff_annot_op o)) E2 T2 :: eff_env_paramty Env (eff_annot_op o) :: Gamma)) ++ [eff_env_returnty Env (eff_annot_op o')] ++
              (drop 2 (tarr (eff_env_returnty Env (eff_annot_op o)) E2 T2 :: eff_env_paramty Env (eff_annot_op o) :: Gamma))); auto.
          apply shift_typing; auto. }
      * set_solver.
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.
Definition stuck (t:comp) : Prop :=
  (normal_form step) t /\ ~(value t).

Corollary soundness : forall Env t t' T,
  Env, nil |-c t in T ; empty ->
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
