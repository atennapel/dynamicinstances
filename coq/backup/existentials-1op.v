(*
  algebraic effects with handlers with dynamic instances
  using existentials types

  handlers can only handle 1 operation

  since an instance belongs to 1 effect
  we can simply operation calls to
  inst(v; x. c)
  we can leave out the operation since
  the instance only had 1 operation anyway
*)

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.
Require Import Util.
From stdpp Require Import fin_collections gmap.

(* effects *)
Definition eff := nat.
Notation effs := (gset eff).

Definition inst := nat.
Notation annots := (gset inst).

(* types *)
Inductive ty : Type :=
  | tinst : inst -> ty
  | tunit : ty
  | tarr : ty -> cty -> ty
  | thandler : cty -> cty -> ty
with cty : Type :=
  | tannot : ty -> annots -> cty
  | texists : eff -> cty -> cty.

Scheme vty_mut_ind := Induction for ty Sort Prop
  with cty_mut_ind := Induction for cty Sort Prop.
Combined Scheme ty_mut_ind from vty_mut_ind, cty_mut_ind.

Hint Constructors ty.
Hint Constructors cty.

(* env & contenxt *)
Definition env := list eff.
Definition context := list ty.

Record eff_env := EffEnv {
  eff_env_paramty : eff -> ty;
  eff_env_returnty : eff -> ty;
}.

(* flatten cty *)
Inductive unwrap_cty : env -> cty -> cty -> Prop :=
  | Ex_nil : forall t r,
    unwrap_cty [] (tannot t r) (tannot t r)
  | Ex_cons : forall E l t1 t2,
    unwrap_cty l t1 t2 ->
    unwrap_cty (E :: l) (texists E t1) t2.

Hint Constructors unwrap_cty.

(* ast *)
Inductive val : Type :=
  | var : nat -> val
  | unit : val
  | vinst :nat -> val
  | abs : comp -> val
  | handler : val -> comp -> comp -> val
with comp : Type :=
  | ret : val -> comp
  | app : val -> val -> comp
  | do : comp -> comp -> comp
  | handle : val -> comp -> comp
  | opc : val -> val -> comp -> comp
  | new : eff -> comp.

Scheme val_mut_ind := Induction for val Sort Prop
  with comp_mut_ind := Induction for comp Sort Prop.
Combined Scheme ast_mut_ind from val_mut_ind, comp_mut_ind.

Hint Constructors val.
Hint Constructors comp.

(* type closed *)
Inductive closed_ty : inst -> ty -> Prop :=
  | C_tunit : forall i,
    closed_ty i tunit
  | C_tarr : forall i a b,
    closed_ty i a ->
    closed_cty i b ->
    closed_ty i (tarr a b)
  | C_tinst : forall i j,
    j <= i ->
    closed_ty i (tinst j)
  | C_thandler : forall i a b,
    closed_cty i a ->
    closed_cty i b ->
    closed_ty i (thandler a b)
with closed_cty : inst -> cty -> Prop :=
  | C_tannot : forall i t e,
    closed_ty i t ->
    ~(i ∈ e) ->
    closed_cty i (tannot t e)
  | C_texists : forall i e t,
    closed_cty (S i) t ->
    closed_cty i (texists e t).

Scheme closed_ty_mut_ind := Induction for closed_ty Sort Prop
  with closed_cty_mut_ind := Induction for closed_cty Sort Prop.
Combined Scheme closed_type_mut_ind from closed_ty_mut_ind, closed_cty_mut_ind.

Hint Constructors closed_ty.
Hint Constructors closed_cty.

(* swap tinst *)
Definition swap_2_tinst_in_annot (i:inst) (j:inst) (e:annots) : annots :=
  if decide (i ∈ e) then
    if decide (j ∈ e) then
      e
    else
      {[ j ]} ∪ e ∖ {[ i ]}
  else
    if decide (j ∈ e) then
      {[ i ]} ∪ e ∖ {[ j ]}
    else
      e.

Fixpoint swap_2_tinst_ty_rec (i:inst) (j:inst) (t:ty) : ty :=
  match t with
  | tunit => tunit
  | tinst i' => if i' =? i then tinst j else if i' =? j then tinst i else t
  | tarr a b => tarr (swap_2_tinst_ty_rec i j a) (swap_2_tinst_cty_rec i j b)
  | thandler a b => thandler (swap_2_tinst_cty_rec i j a) (swap_2_tinst_cty_rec i j b)
  end
with swap_2_tinst_cty_rec (i:inst) (j:inst) (t:cty) : cty :=
  match t with
  | tannot t' e => tannot (swap_2_tinst_ty_rec i j t') (swap_2_tinst_in_annot i j e)
  | texists e t' => texists e (swap_2_tinst_cty_rec (S i) (S j) t')
  end.

Definition swap_2_tinst_ty t := swap_2_tinst_ty_rec 0 1 t.
Definition swap_2_tinst_cty t := swap_2_tinst_cty_rec 0 1 t.

Hint Unfold swap_2_tinst_ty.
Hint Unfold swap_2_tinst_cty.

(* substitution *)
Fixpoint shiftval' (d:nat) (c:nat) (t:val) : val :=
  match t with
  | unit => t
  | vinst _ =>t
  | var k => if k <? c then t else var (k + d)
  | abs t' => abs (shiftcomp' d (S c) t')
  | handler v cr co => handler (shiftval' d c v) (shiftcomp' d (S c) cr) (shiftcomp' d (S (S c)) co)
  end
with shiftcomp' (d:nat) (c:nat) (t:comp) : comp :=
  match t with
  | ret t' => ret (shiftval' d c t')
  | app t1 t2 => app (shiftval' d c t1) (shiftval' d c t2)
  | do t1 t2 => do (shiftcomp' d c t1) (shiftcomp' d (S c) t2)
  | opc vi v t => opc (shiftval' d c vi) (shiftval' d c v) (shiftcomp' d (S c) t)
  | handle v t => handle (shiftval' d c v) (shiftcomp' d c t)
  | new E => t
  end.

Definition shiftval d t := shiftval' d 0 t.
Definition shiftcomp d t := shiftcomp' d 0 t.

Hint Unfold shiftval.
Hint Unfold shiftcomp.

Fixpoint substval' (j:nat) (s:val) (t:val) : val :=
  match t with
  | unit => t
  | vinst _ => t
  | var k => if k =? j then s
              else if k <? j then t else var (pred k)
  | abs t' => abs (substcomp' (S j) (shiftval 1 s) t')
  | handler v cr co => handler (substval' j s v) (substcomp' (S j) (shiftval 1 s) cr) (substcomp' (S (S j)) (shiftval 2 s) co)
  end
with substcomp' (j:nat) (s:val) (t:comp) : comp :=
  match t with
  | ret t' => ret (substval' j s t')
  | app t1 t2 => app (substval' j s t1) (substval' j s t2)
  | do t1 t2 => do (substcomp' j s t1) (substcomp' (S j) (shiftval 1 s) t2)
  | opc vi v t => opc (substval' j s vi) (substval' j s v) (substcomp' (S j) (shiftval 1 s) t)
  | handle v t => handle (substval' j s v) (substcomp' j s t)
  | new E => t
  end.

Definition substval s t := substval' 0 s t.
Definition substcomp s t := substcomp' 0 s t.

Hint Unfold substval.
Hint Unfold substcomp.

(* semantics *)
Definition value c := exists v, c = ret v.
Hint Unfold value.

Inductive step : comp -> nat -> comp -> nat -> Prop :=
  | S_AppAbs : forall t1 t2 i,
    step (app (abs t1) t2) i (substcomp t2 t1) i
  | S_New : forall E i,
     step (new E) i (ret (vinst i)) (S i)
  | S_DoReturn : forall v t i,
    step (do (ret v) t) i (substcomp v t) i
  | S_Do : forall t1 t1' i i' t2,
    step t1 i t1' i' ->
    step (do t1 t2) i (do t1' t2) i'
  | S_DoOp : forall vi v c1 c2 i,
    step (do (opc vi v c1) c2) i (opc vi v (do c1 (shiftcomp' 1 1 c2))) i
  | S_Handle : forall v cr hl c c' i i',
    step c i c' i' ->
    step (handle (handler v cr hl) c) i (handle (handler v cr hl) c') i'
  | S_HandleReturn : forall vi cr hl v i,
    step (handle (handler vi cr hl) (ret v)) i (substcomp v cr) i
  | S_HandleOp1 : forall cr vi i co v c,
    step
      (handle (handler vi cr co) (opc vi v c))
      i
      (substcomp v
        (substcomp (abs (handle (shiftval 2 (handler vi cr co)) (shiftcomp' 1 1 c))) co))
      i
  | S_HandleOp2 : forall cr co i vi vi' v c,
    ~(vi = vi') ->
    step
      (handle (handler vi cr co) (opc vi' v c))
      i
      (opc vi' v (handle (shiftval 1 (handler vi cr co)) c))
      i.

Hint Constructors step.

Definition relation2 (X Y: Type) := X->Y->X->Y->Prop.
Definition deterministic2 {X Y: Type} (R: relation2 X Y) :=
  forall (a1 a2 a3 : X)(b1 b2 b3:Y), R a1 b1 a2 b2 -> R a1 b1 a3 b3 -> a2 = a3 /\ b2 = b3.
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Notation multistep := (multi step).
Notation "t1 '===>*' t2" := (multistep t1 t2) (at level 40).

(* subtyping *)
Inductive sub_ty : ty -> ty -> Prop :=
  | U_tunit :
    sub_ty tunit tunit
  | U_tarr : forall t1 t2 t1' t2',
    sub_ty t1' t1 ->
    sub_cty t2 t2' ->
    sub_ty (tarr t1 t2) (tarr t1' t2')
  | U_tinst : forall i,
    sub_ty (tinst i) (tinst i)
  | U_thandler : forall t1 t2 t1' t2',
    sub_cty t1' t1 ->
    sub_cty t2 t2' ->
    sub_ty (thandler t1 t2) (thandler t1' t2')
with sub_cty : cty -> cty -> Prop :=
  | U_tannot : forall t t' e e',
    sub_ty t t' ->
    e ⊆ e' ->
    sub_cty (tannot t e) (tannot t' e')
  | U_texists : forall e t t',
    sub_cty t t' ->
    sub_cty (texists e t) (texists e t')
  | U_texists_remove : forall e t,
    closed_cty 0 t ->
    sub_cty (texists e t) t
  | U_texists_swap : forall e e' t,
    sub_cty
      (texists e (texists e' (swap_2_tinst_cty t)))
      (texists e' (texists e t))
  | U_cty_trans : forall a b c,
    sub_cty a b ->
    sub_cty b c ->
    sub_cty a c.

Scheme sub_ty_mut_ind := Induction for sub_ty Sort Prop
  with sub_cty_mut_ind := Induction for sub_cty Sort Prop.
Combined Scheme sub_mut_ind from sub_ty_mut_ind, sub_cty_mut_ind.

Hint Constructors sub_ty.
Hint Constructors sub_cty.

Notation sub_context := (Forall2 sub_ty).

(* wellformedness *)
Inductive wf_ty : env -> ty -> Prop :=
  | WF_tunit : forall e,
    wf_ty e tunit
  | WF_tinst : forall e i ef,
    nth_error e i = Some ef ->
    wf_ty e (tinst i)
  | WF_tarr : forall e a b,
    wf_ty e a ->
    wf_cty e b ->
    wf_ty e (tarr a b)
  | WF_thandler : forall e a b,
    wf_cty e a ->
    wf_cty e b ->
    wf_ty e (thandler a b)
with wf_cty : env -> cty -> Prop :=
  | WF_tannot : forall e t efs,
    wf_ty e t ->
    (forall i, i ∈ efs -> wf_ty e (tinst i)) ->
    wf_cty e (tannot t efs)
  | WF_texists : forall e ef t,
    wf_cty (ef :: e) t ->
    wf_cty e (texists ef t).

Scheme wf_ty_mut_ind := Induction for wf_ty Sort Prop
  with wf_cty_mut_ind := Induction for wf_cty Sort Prop.
Combined Scheme wf_mut_ind from wf_ty_mut_ind, wf_cty_mut_ind.

Hint Constructors wf_ty.
Hint Constructors wf_cty.

Notation wf_context E := (Forall (wf_ty E)).

(* typing rules *)
Inductive tc_val : eff_env -> env -> context -> val -> ty -> Prop :=
  | TC_unit : forall F E C,
    tc_val F E C unit tunit
  | TC_var : forall F E C i t,
    nth_error C i = Some t ->
    tc_val F E C (var i) t
  | TC_vinst : forall F E C i e,
    nth_error E i = Some e ->
    tc_val F E C (vinst i) (tinst i)
  | TC_abs : forall F E C c t1 t2,
    wf_ty E t1 ->
    tc_comp F E (t1 :: C) c t2 ->
    tc_val F E C (abs c) (tarr t1 t2)
  | TC_handler : forall F E C vi cr co i e t1 r1 t2 r2,
    tc_val F E C vi (tinst i) ->
    nth_error E i = Some e ->
    wf_ty E t1 ->
    tc_comp F E (t1 :: C) cr (tannot t2 r2) ->
    tc_comp F E (eff_env_paramty F e :: tarr (eff_env_returnty F e) (tannot t2 r2) :: C) co (tannot t2 r2) ->
    r1 ∖ {[ i ]} ⊆ r2 ->
    tc_val F E C (handler vi cr co) (thandler (tannot t1 r1) (tannot t2 r2))
  | TC_sub_val : forall F E C v t1 t2,
    tc_val F E C v t1 ->
    wf_ty E t2 ->
    sub_ty t1 t2 ->
    tc_val F E C v t2
with tc_comp : eff_env -> env -> context -> comp -> cty -> Prop :=
  | TC_ret : forall F E C v t,
    tc_val F E C v t ->
    tc_comp F E C (ret v) (tannot t empty)
  | TC_app : forall F E C v1 v2 t1 t2,
    tc_val F E C v1 (tarr t1 t2) ->
    tc_val F E C v2 t1 ->
    tc_comp F E C (app v1 v2) t2
  | TC_do : forall F E C c1 c2 is1 is2 t1 t2 r1 r2 t1c t2c tr,
    tc_comp F E C c1 t1c ->
    unwrap_cty is1 (tannot t1 r1) t1c ->
    tc_comp F (is1 ++ E) (t1 :: C) c2 t2c ->
    unwrap_cty is2 (tannot t2 r2) t2c ->
    unwrap_cty (is1 ++ is2) (tannot t2 (r1 ∪ r2)) tr ->
    tc_comp F E C (do c1 c2) tr
  | TC_handle : forall F E C v c tc tr is t1 t2,
    tc_comp F E C c tc ->
    unwrap_cty is t1 tc ->
    tc_val F (is ++ E) C v (thandler t1 t2) ->
    unwrap_cty is t2 tr ->
    tc_comp F E C (handle v c) tr
  | TC_opc : forall F E C vi vv cc i e tr t efs is,
    tc_val F E C vi (tinst i) ->
    nth_error E i = Some e ->
    tc_val F E C vv (eff_env_paramty F e) ->
    tc_comp F E (eff_env_returnty F e :: C) cc tr ->
    unwrap_cty is (tannot t efs) tr ->
    i ∈ efs ->
    tc_comp F E C (opc vi vv cc) tr
  | TC_new : forall F E C e,
    tc_comp F E C (new e) (texists e (tannot (tinst 0) empty))
  | TC_sub_comp : forall F E C c t1 t2,
    tc_comp F E C c t1 ->
    wf_cty E t2 ->
    sub_cty t1 t2 ->
    tc_comp F E C c t2.

Scheme tc_val_mut_ind := Induction for tc_val Sort Prop
  with tc_comp_mut_ind := Induction for tc_comp Sort Prop.
Combined Scheme tc_mut_ind from tc_val_mut_ind, tc_comp_mut_ind.

Hint Constructors tc_val.
Hint Constructors tc_comp.

(* theorems *)
Theorem step_deterministic:
  deterministic2 step.
Proof.
  unfold deterministic2.
  intros.
  generalize dependent a2.
  generalize dependent b2.
  induction H0; intros; try (inv H).
  - apply IHstep in H6.
    destruct H6.
    subst; split; auto.
  - apply IHstep in H8.
    destruct H8.
    subst; split; auto.
  - contradiction.
  - inv H0.
    contradiction.
Qed.

Theorem sub_refl :
  (forall t, sub_ty t t) /\
  (forall t, sub_cty t t).
Proof.
  apply ty_mut_ind; auto.
Qed.

Lemma sub_trans :
  (forall b a c, sub_ty a b -> sub_ty b c -> sub_ty a c) /\
  (forall b a c, sub_cty a b -> sub_cty b c -> sub_cty a c).
Proof.
  apply ty_mut_ind; intros;
    try (inv H);
    try (inv H1; inv H2).
  - apply U_cty_trans with (b := tannot t m); auto.
  - apply U_cty_trans with (b := texists e c); auto.
Qed.

Lemma subset_prop_holds : forall (P : inst -> Prop) (r1:annots) r2,
  (forall x, x ∈ r2 -> P x) ->
  r1 ⊆ r2 ->
  (forall x, x ∈ r1 -> P x).
Proof.
  set_solver.
Qed.

Lemma difference_prop_holds : forall (P : inst -> Prop) (r1:annots) r2,
  (forall x, x ∈ r1 -> P x) ->
  (forall x, x ∈ r2 -> P x) ->
  (forall x, x ∈ r1 ∖ r2 -> P x).
Proof.
  set_solver.
Qed.

Lemma partial_subset_prop_holds : forall (P : inst -> Prop) (r1:annots) r r2,
  (forall x, x ∈ r2 -> P x) ->
  (forall x, x ∈ r -> P x) ->
  r1 ∖ r ⊆ r2 ->
  (forall x, x ∈ r1 -> P x).
Proof.
  intros.
  destruct (decide (x ∈ r)); set_solver.
Qed.

Theorem tc_wf :
  (forall F E C v t, tc_val F E C v t -> wf_context E C -> wf_ty E t) /\
  (forall F E C v t, tc_comp F E C v t -> wf_context E C -> wf_cty E t).
Proof.
  apply tc_mut_ind; intros; auto.
  - rewrite Forall_forall in H.
    apply nth_error_In in e.
    rewrite <- elem_of_list_In in e.
    apply H in e.
    auto.
  - apply WF_tinst with (ef := e); auto.
  - assert (w' := w).
    assert (H2' := H2).
    apply Forall_cons_2 with (l := C) in w; auto.
    apply H0 in w.
    inv w.
    apply H in H2.
    apply WF_thandler; apply WF_tannot; auto.
    apply partial_subset_prop_holds with (r := {[i]}) (r2 := r2); auto.
    intros.
    assert (x = i). set_solver.
    subst; auto.
  - constructor; auto. set_solver.
  - apply H in H1.
    inv H1.
  - 

