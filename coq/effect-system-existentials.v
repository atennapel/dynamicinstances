Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.
Require Import Util.
From stdpp Require Import fin_collections gmap.

(* effects *)
Definition eff := nat.
Notation effs := (gset eff).
Definition op := nat.
Notation ops := (gset op).

Definition inst := nat.
Notation annots := (gset inst).

(* ast *)
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

Definition texists' es t := foldr (fun e t' => texists e t') t es.

Inductive val : Type :=
  | var : nat -> val
  | unit : val
  | abs : comp -> val
  | handler : val -> comp -> hlist -> val
with comp : Type :=
  | ret : val -> comp
  | app : val -> val -> comp
  | do : comp -> comp -> comp
  | handle : val -> comp -> comp
  | opc : val -> op -> val -> comp -> comp
  | new : eff -> comp
with hlist : Type :=
  | hnil : hlist
  | hcons : op -> comp -> hlist -> hlist.

Scheme val_mut_ind := Induction for val Sort Prop
  with comp_mut_ind := Induction for comp Sort Prop
  with hlist_mut_ind := Induction for hlist Sort Prop.
Combined Scheme ast_mut_ind from val_mut_ind, comp_mut_ind, hlist_mut_ind.

Hint Constructors val.
Hint Constructors comp.
Hint Constructors hlist.

Inductive unwrap_cty : list eff -> cty -> cty -> Prop :=
  | Ex_nil : forall t r,
    unwrap_cty [] (tannot t r) (tannot t r)
  | Ex_cons : forall E l t1 t2,
    unwrap_cty l t1 t2 ->
    unwrap_cty (E :: l) (texists E t1) t2.

Hint Constructors unwrap_cty.

Inductive hlist_has : hlist -> op -> comp -> Prop :=
  | H_head : forall o c r,
    hlist_has (hcons o c r) o c
  | H_tail : forall o o' c c' r,
    ~(o = o') ->
    hlist_has r o c ->
    hlist_has (hcons o' c' r) o c.

Hint Constructors hlist_has.

(* ty not free, ty does not contain the instance variable free *)
Inductive not_free_ty : inst -> ty -> Prop :=
  | F_tinst : forall i j,
    ~(i = j) ->
    not_free_ty i (tinst j)
  | F_tunit : forall i,
    not_free_ty i tunit
  | F_tarr : forall i a b,
    not_free_ty i a ->
    not_free_cty i b ->
    not_free_ty i (tarr a b)
  | F_thandler : forall i a b,
    not_free_cty i a ->
    not_free_cty i b ->
    not_free_ty i (thandler a b)
with not_free_cty : inst -> cty -> Prop :=
  | F_tannot : forall i t r,
    not_free_ty i t ->
    (forall j, j ∈ r -> j > i) ->
    not_free_cty i (tannot t r)
  | F_texists : forall i E t,
    not_free_cty (i + 1) t ->
    not_free_cty i (texists E t).

Scheme not_free_ty_mut_ind := Induction for not_free_ty Sort Prop
  with not_free_cty_mut_ind := Induction for not_free_cty Sort Prop.
Combined Scheme not_free_mut_ind from not_free_ty_mut_ind, not_free_cty_mut_ind.

Hint Constructors not_free_ty.
Hint Constructors not_free_cty.

(* effect env *)
Record env := Env {
  env_effs : effs;
  env_ops : eff -> ops;
  env_paramty : op -> ty;
  env_returnty : op -> ty;

  env_unique_ops : forall e e', (env_ops e) ∩ (env_ops e') = empty;
}.

(* subtyping *)
Inductive sub_ty : ty -> ty -> Prop :=
  | Sub_tinst : forall i,
    sub_ty (tinst i) (tinst i)
  | Sub_tunit :
    sub_ty tunit tunit
  | Sub_tarr : forall a b a' b',
    sub_ty a' a ->
    sub_cty b b' ->
    sub_ty (tarr a b) (tarr a' b')
  | Sub_thandler : forall a b a' b',
    sub_cty a' a ->
    sub_cty b b' ->
    sub_ty (thandler a b) (thandler a' b')
with sub_cty : cty -> cty -> Prop :=
  | Sub_tannot : forall t t' e e',
    sub_ty t t' ->
    e ⊆ e' ->
    sub_cty (tannot t e) (tannot t' e')
  | Sub_texists : forall e t t',
    sub_cty t t' ->
    sub_cty (texists e t) (texists e t').

Scheme sub_ty_mut_ind := Induction for sub_ty Sort Prop
  with sub_cty_mut_ind := Induction for sub_cty Sort Prop.
Combined Scheme sub_mut_ind from sub_ty_mut_ind, sub_cty_mut_ind.

Hint Constructors sub_ty.
Hint Constructors sub_cty.

(* type wf *)
Notation delta := (list eff).

Inductive wf_ty : delta -> ty -> Prop :=
  | WF_tinst : forall d i e,
    nth_error d i = Some e ->
    wf_ty d (tinst i)
  | WF_tunit : forall d,
    wf_ty d tunit
  | WF_tarr : forall d a b,
    wf_ty d a ->
    wf_cty d b ->
    wf_ty d (tarr a b)
  | WF_thandler : forall d a b,
    wf_cty d a ->
    wf_cty d b ->
    wf_ty d (thandler a b)
with wf_cty : delta -> cty -> Prop :=
  | WF_tannot : forall d t r,
    wf_ty d t ->
    (forall i, i ∈ r -> wf_ty d (tinst i)) ->
    wf_cty d (tannot t r)
  | WF_texists : forall d e t,
    wf_cty (e :: d) t ->
    wf_cty d (texists e t).

Scheme wf_ty_mut_ind := Induction for wf_ty Sort Prop
  with wf_cty_mut_ind := Induction for wf_cty Sort Prop.
Combined Scheme wf_mut_ind from wf_ty_mut_ind, wf_cty_mut_ind.

Hint Constructors wf_ty.
Hint Constructors wf_cty.

(* typing rules *)
Notation context := (list ty).

Notation wf_context E := (Forall (wf_ty E)).

Inductive has_type_val : env -> delta -> context -> val -> ty -> Prop :=
  | T_var : forall e d c i t,
    nth_error c i = Some t ->
    has_type_val e d c (var i) t
  | T_unit : forall e d c,
    has_type_val e d c unit tunit
  | T_abs : forall e d c b t1 t2,
    wf_ty d t1 ->
    has_type_comp e d (t1 :: c) b t2 ->
    has_type_val e d c (abs b) (tarr t1 t2)
  | T_handler : forall e d c E v r hl i t1 t2 r1 r2,
    wf_cty d (tannot t1 r1) ->
    has_type_val e d c v (tinst i) ->
    nth_error d i = Some E ->
    (forall o, o ∈ env_ops e E <-> exists c, hlist_has hl o c) ->
    has_type_comp e d (t1 :: c) r (tannot t2 r2) ->
    has_type_hlist e d c hl (tannot t2 r2) ->
    r1 ∖ {[ i ]} ⊆ r2 ->
    has_type_val e d c (handler v r hl) (thandler (tannot t1 r1) (tannot t2 r2))
  | T_sub_ty : forall e d c v t1 t2,
    has_type_val e d c v t1 ->
    wf_ty d t2 ->
    sub_ty t1 t2 ->
    has_type_val e d c v t2
with has_type_comp : env -> delta -> context -> comp -> cty -> Prop :=
  | T_ret : forall e d c v t,
    has_type_val e d c v t ->
    has_type_comp e d c (ret v) (tannot t ∅)
  | T_app : forall e d c v1 v2 t1 t2,
    has_type_val e d c v1 (tarr t1 t2) ->
    has_type_val e d c v2 t1 ->
    has_type_comp e d c (app v1 v2) t2
  | T_do : forall e d c c1 c2 es1 es2 t1 t2 t1' t2' r1 r2,
    unwrap_cty es1 t1 (tannot t1' r1) ->
    unwrap_cty es2 t2 (tannot t2' r2) ->
    has_type_comp e d c c1 t1 ->
    has_type_comp e (d ++ es1) (t1' :: c) c2 t2 ->
    has_type_comp e d c (do c1 c2) (texists' (es1 ++ es2) (tannot t2' (union r1 r2)))
  | T_handle : forall e d c v b t1 t2,
    has_type_val e d c v (thandler t1 t2) ->
    has_type_comp e d c b t1 ->
    has_type_comp e d c (handle v b) t2
  | T_opc : forall e d c v1 o v2 b t r i E,
    has_type_val e d c v1 (tinst i) ->
    nth_error d i = Some E ->
    o ∈ env_ops e E ->
    has_type_val e d c v2 (env_paramty e o) ->
    has_type_comp e d (env_returnty e o :: c) b (tannot t r) ->
    i ∈ r ->
    has_type_comp e d c (opc v1 o v2 b) (tannot t r)
  | T_new : forall e d c E,
    has_type_comp e d c (new E) (texists E (tannot (tinst 0) ∅))
  | T_exists : forall e d c b t E,
    has_type_comp e d c b (texists E t) ->
    not_free_cty 0 t ->
    has_type_comp e d c b t
  | T_sub_cty : forall e d c b t1 t2,
    has_type_comp e d c b t1 ->
    wf_cty d t2 ->
    sub_cty t1 t2 ->
    has_type_comp e d c b t2
with has_type_hlist : env -> delta -> context -> hlist -> cty -> Prop :=
  | T_hnil : forall e d c t,
    has_type_hlist e d c hnil t
  | T_hcons : forall e d c o b rl t r,
    has_type_comp e d (env_paramty e o :: (tarr (env_returnty e o) (tannot t r)) :: c) b (tannot t r) ->
    has_type_hlist e d c rl (tannot t r) ->
    has_type_hlist e d c (hcons o b rl) (tannot t r).

Scheme has_type_val_mut_ind := Induction for has_type_val Sort Prop
  with has_type_comp_mut_ind := Induction for has_type_comp Sort Prop
  with has_type_hlist_mut_ind := Induction for has_type_hlist Sort Prop.
Combined Scheme has_type_mut_ind from has_type_val_mut_ind, has_type_comp_mut_ind, has_type_hlist_mut_ind.

Hint Constructors has_type_val.
Hint Constructors has_type_comp.
Hint Constructors has_type_hlist.

(* lemmas & theorems *)
Lemma hlist_has_dec : forall hl o,
  (exists c, hlist_has hl o c) \/ (forall c, ~(hlist_has hl o c)).
Proof.
  induction hl as [| o' c' r IH ].
  - intros o.
    right.
    intros c.
    unfold not.
    intros H.
    inversion H.
  - intros o.
    destruct (Nat.eq_dec o o') as [ e | e ].
    + subst.
      left.
      exists c'.
      auto.
    + destruct IH with (o := o) as [ H | H ]; clear IH.
      * destruct H as [ c H ].
        left.
        exists c.
        auto.
      * right.
        unfold not.
        intros c H'.
        inversion H'; subst.
        { contradiction. }
        { specialize (H c). contradiction. }
Qed.

Lemma hlist_has_tail : forall o o' c c' r,
  ~(o = o') -> hlist_has (hcons o c r) o' c' -> hlist_has r o' c'.
Proof.
  intros o o' c c' r ineq H.
  inv H; try contradiction; auto.
Qed.

Lemma hlist_has_deterministic : forall hl o c,
  hlist_has hl o c -> forall c', hlist_has hl o c' -> c = c'.
Proof.
  intros hl o c H.
  induction H as [o c r | o o' c c' r ineq rhas IH].
  - intros c'.
    intros H.
    inv H; contradiction.
  - intros c'' H.
    specialize (IH c'').
    apply hlist_has_tail in H; auto.
Qed.

Lemma sub_refl :
  (forall t, sub_ty t t) /\
  (forall t, sub_cty t t).
Proof.
  apply ty_mut_ind; intros; auto.
Qed.

Lemma sub_trans :
  (forall b a c, sub_ty a b -> sub_ty b c -> sub_ty a c) /\
  (forall b a c, sub_cty a b -> sub_cty b c -> sub_cty a c).
Proof.
  apply ty_mut_ind; intros; auto; try (inv H).
  - inv H1.
    inv H2.
  - inv H1.
    inv H2.
  - inv H0.
    inv H1.
    apply Sub_tannot.
    + apply H with (c := t') in H5; auto.
    + set_solver.
  - inv H0.
    inv H1.
Qed.

Lemma ty_wellformed :
  (forall E D G v t, has_type_val E D G v t -> wf_context D G -> wf_ty D t) /\
  (forall E D G v t, has_type_comp E D G v t -> wf_context D G -> wf_cty D t) /\
  (forall E D G v t, has_type_hlist E D G v t -> wf_context D G -> wf_cty D t).
Proof.
  apply has_type_mut_ind; intros; auto.
  - 
