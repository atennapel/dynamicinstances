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

Inductive val : Type :=
  | var : nat -> val
  | unit : val
  | vinst :nat -> val
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

(* substitution in types *)
Fixpoint shiftty' (d:nat) (c:nat) (t:ty) : ty :=
  match t with
  | tinst k => if k <? c then t else tinst (k + d)
  | tunit => t
  | tarr a b => tarr (shiftty' d c a) (shiftcty' d c b)
  | thandler a b => thandler (shiftcty' d c a) (shiftcty' d c b)
  end
with shiftcty' (d:nat) (c:nat) (t:cty) : cty :=
  match t with
  | tannot t' r => tannot (shiftty' d c t') (fmap (fun k => if k <? c then k else k + d) r)
  | texists E t' => texists E (shiftcty' d (S c) t')
  end.

Search (gset _).

Definition shiftty d t := shiftty' d 0 t.
Definition shiftcty d t := shiftcty' d 0 t.

Hint Unfold shiftty.
Hint Unfold shiftcty.

(* substitution *)
Fixpoint shiftval' (d:nat) (c:nat) (t:val) : val :=
  match t with
  | unit => t
  | vinst _ =>t
  | var k => if k <? c then t else var (k + d)
  | abs t' => abs (shiftcomp' d (S c) t')
  | handler v cr hl => handler (shiftval' d c v) (shiftcomp' d (S c) cr) (shifthlist' d c hl)
  end
with shiftcomp' (d:nat) (c:nat) (t:comp) : comp :=
  match t with
  | ret t' => ret (shiftval' d c t')
  | app t1 t2 => app (shiftval' d c t1) (shiftval' d c t2)
  | do t1 t2 => do (shiftcomp' d c t1) (shiftcomp' d (S c) t2)
  | opc vi o v t => opc (shiftval' d c vi) o (shiftval' d c v) (shiftcomp' d (S c) t)
  | handle v t => handle (shiftval' d c v) (shiftcomp' d c t)
  | new E => t
  end
with shifthlist' (d:nat) (c:nat) (t:hlist) : hlist :=
  match t with
  | hnil => t
  | hcons o co r => hcons o (shiftcomp' d (S (S c)) co) (shifthlist' d c r)
  end.

Definition shiftval d t := shiftval' d 0 t.
Definition shiftcomp d t := shiftcomp' d 0 t.
Definition shifthlist d t := shifthlist' d 0 t.

Hint Unfold shiftval.
Hint Unfold shiftcomp.
Hint Unfold shifthlist.

Fixpoint substval' (j:nat) (s:val) (t:val) : val :=
  match t with
  | unit => t
  | vinst _ => t
  | var k => if k =? j then s
              else if k <? j then t else var (pred k)
  | abs t' => abs (substcomp' (S j) (shiftval 1 s) t')
  | handler v cr hl => handler (substval' j s v) (substcomp' (S j) (shiftval 1 s) cr) (substhlist' j s hl)
  end
with substcomp' (j:nat) (s:val) (t:comp) : comp :=
  match t with
  | ret t' => ret (substval' j s t')
  | app t1 t2 => app (substval' j s t1) (substval' j s t2)
  | do t1 t2 => do (substcomp' j s t1) (substcomp' (S j) (shiftval 1 s) t2)
  | opc vi o v t => opc (substval' j s vi) o (substval' j s v) (substcomp' (S j) (shiftval 1 s) t)
  | handle v t => handle (substval' j s v) (substcomp' j s t)
  | new E => t
  end
with substhlist' (j:nat) (s:val) (t:hlist) : hlist :=
  match t with
  | hnil => t
  | hcons o co r => hcons o (substcomp' (S (S j)) (shiftval 2 s) co) (substhlist' j s r)
  end.

Definition substval s t := substval' 0 s t.
Definition substcomp s t := substcomp' 0 s t.
Definition substhlist s t := substhlist' 0 s t.

Hint Unfold substval.
Hint Unfold substcomp.
Hint Unfold substhlist.

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
  | S_DoOp : forall vi o v c1 c2 i,
    step (do (opc vi o v c1) c2) i (opc vi o v (do c1 (shiftcomp' 1 1 c2))) i
  | S_Handle : forall v cr hl c c' i i',
    step c i c' i' ->
    step (handle (handler v cr hl) c) i (handle (handler v cr hl) c') i'
  | S_HandleReturn : forall vi cr hl v i,
    step (handle (handler vi cr hl) (ret v)) i (substcomp v cr) i
  | S_HandleOp1 : forall cr vi i o co hl v c,
    hlist_has hl o co ->
    step
      (handle (handler vi cr hl) (opc vi o v c))
      i
      (substcomp v
        (substcomp (abs (handle (shiftval 2 (handler vi cr hl)) (shiftcomp' 1 1 c))) co))
      i
  | S_HandleOp2 : forall cr hl i vi vi' o v c,
    (forall co, ~(hlist_has hl o co)) \/ ~(vi = vi') ->
    step
      (handle (handler vi cr hl) (opc vi' o v c))
      i
      (opc vi' o v (handle (shiftval 1 (handler vi cr hl)) c))
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

(* effect env *)
Record env := Env {
  env_effs : effs;
  env_ops : eff -> ops;
  env_paramty : op -> ty;
  env_returnty : op -> ty;
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
    sub_cty (texists e t) (texists e t')
  | Sub_texists_remove : forall e t t',
    sub_cty t t' ->
    not_free_cty 0 t' ->
    sub_cty (texists e t) t'
  | Sub_texists_swap : forall e f t,
    sub_cty (texists e (texists f t)) (texists f (texists e t)).

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
  | T_vinst : forall e d c i E,
    nth_error d i = Some E ->
    has_type_val e d c (vinst i) (tinst i)
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
  | T_do : forall e d c c1 c2 es1 es2 t1 t2 t3 t1' t2' r1 r2,
    unwrap_cty es1 t1 (tannot t1' r1) ->
    unwrap_cty es2 t2 (tannot t2' r2) ->
    has_type_comp e d c c1 t1 ->
    has_type_comp e (es1 ++ d) (t1' :: c) c2 t2 ->
    unwrap_cty (es1 ++ es2) t3 (tannot t2' (union r1 r2)) ->
    has_type_comp e d c (do c1 c2) t3
  | T_handle : forall e d c v b t1 es t1' t2 t3,
    unwrap_cty es t1 t1' ->
    has_type_val e (es ++ d) c v (thandler t1' t2) ->
    has_type_comp e d c b t1 ->
    unwrap_cty es t3 t2 ->
    has_type_comp e d c (handle v b) t3
  | T_opc : forall e d c v1 o v2 b t t' es tc r i E,
    unwrap_cty es tc (tannot t r) ->
    has_type_val e d c v1 (tinst i) ->
    nth_error d i = Some E ->
    o ∈ env_ops e E ->
    has_type_val e d c v2 (env_paramty e o) ->
    has_type_comp e d (env_returnty e o :: c) b tc ->
    i ∈ r ->
    unwrap_cty es t' (tannot t r) ->
    has_type_comp e d c (opc v1 o v2 b) t'
  | T_new : forall e d c E,
    has_type_comp e d c (new E) (texists E (tannot (tinst 0) ∅))
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

(* examples *)

(* effect E { op : () -> () } *)
Definition exE := 0.
Definition exOp := 0.
Definition exEnv: env := Env
  {[ exE ]}
  (fun e => match e with
    | 0 => {[ exOp ]}
    | _ => ∅
    end)
  (fun o => tunit)
  (fun o => tunit).

(* \() -> inst <- new E; inst#op () : () -> exists (i:E). ()!{i} *)
(*
Example ex1 :
  has_type_val exEnv [] []
    (abs (do (new exE) (opc (var 0) exOp unit (ret (var 0)))))
    (tarr tunit (texists exE (tannot tunit {[0]}))).
Proof.
  apply T_abs; auto.
  apply T_do with (es1 := ∅) (es2 := {[0]}) (t1 := texists exE (tannot (tinst 0) ∅))
    (t2 := tannot tunit {[0]}) (t1' := tinst 0) (t2' := tunit) (r1 := ∅) (r2 := {[0]}).
  replace {[0]} with (union ∅ {[0]} : annots); try set_solver.
  replace (texists exE (tannot tunit (∅ ∪ {[0]}))) with
    (texists' ([exE] ++ []) (tannot tunit (∅ ∪ {[0]}))); auto.
  apply T_do with (t1 := texists exE (tannot (tinst 0) ∅)) (t2 := tannot tunit {[0]}) (t1' := tinst 0); auto.
  simpl.
  replace (tannot tunit {[0]}) with (texists' [] (tannot tunit {[0]})); auto.
  apply T_opc with (i := 0) (E := exE) (tc := texists' [] (tannot tunit {[0]})); auto; try set_solver.
  apply Ex_nil.
  apply T_sub_cty with (t1 := tannot tunit ∅); auto.
  - simpl.
    apply WF_tannot; auto.
    intros.
    assert (i = 0); try set_solver; subst.
    apply WF_tinst with (e := 0); auto.
  - apply Sub_tannot; auto; try set_solver.
Qed.

(* \() -> inst <- new E; with handler(inst) { return x -> x, op x k -> k () } handle inst#op ()
  : () -> ()!{} *)
Example ex2 :
  has_type_val exEnv [] []
    (abs (do (new exE) (
      handle
        (handler (var 0) (ret (var 0)) (hcons exOp (app (var 1) unit) hnil))
        (opc (var 0) exOp unit (ret (var 0))))))
    (tarr tunit (tannot tunit ∅)).
Proof.
  apply T_abs; auto.
  apply T_exists with (E := exE); auto.
  - replace ∅ with (∅ ∪ ∅ : annots); try set_solver.
    replace (texists exE (tannot tunit (∅ ∪ ∅))) with
      (texists' ([exE] ++ []) (tannot tunit (∅ ∪ ∅))); auto.
    apply T_do with (t1 := texists exE (tannot (tinst 0) ∅)) (t2 := tannot tunit ∅) (t1' := tinst 0); auto.
    simpl.
    replace (tannot tunit ∅) with (texists' [] (tannot tunit ∅)); auto.
    apply T_handle with (t1 := tannot tunit {[0]}) (t1' := texists' [] (tannot tunit {[0]})); auto.
    apply Ex_nil.
    + apply T_handler with (E := exE) (i := 0); auto; try set_solver.
      * simpl.
        apply WF_tannot; auto.
        intros.
        assert (i = 0); try set_solver.
        subst.
        apply WF_tinst with (e := exE); auto.
      * intros.
        split; intros.
        { assert (o = exOp); try set_solver; subst.
          exists (app (var 1) unit); auto. }
        { simpl.
          destruct H as [c].
          inv H. }
      * apply T_hcons; auto.
        apply T_app with (t1 := tunit); auto.
    + replace (tannot tunit {[0]}) with (texists' [] (tannot tunit {[0]})); auto.
      apply T_opc with (i := 0) (E := exE) (tc := tannot tunit {[0]}); auto; try set_solver.
      apply T_sub_cty with (t1 := tannot tunit ∅); auto.
      * simpl.
        apply WF_tannot; auto.
        intros.
        assert (i = 0); try set_solver; subst; auto.
        apply WF_tinst with (e := exE); auto.
      * apply Sub_tannot; auto; try set_solver.
  - apply F_tannot; auto; try set_solver.
Qed.*)

(* \() -> inst <- new E; return () : () -> ()!{} *)
Example ex3 :
  has_type_val exEnv [] []
    (abs (do (new exE) (ret unit)))
    (tarr tunit (tannot tunit ∅)).
Proof.
  apply T_abs; auto.
  apply T_sub_cty with (t1 := texists exE (tannot tunit ∅)); auto.
  - apply T_do with (r1 := ∅) (r2 := ∅) (es1 := [exE]) (es2 := [])
      (t1 := texists exE (tannot (tinst 0) ∅)) (t2 := tannot tunit ∅)
      (t1' := tinst 0) (t2' := tunit); auto.
    replace (∅ ∪ ∅) with (∅ : gset nat); try set_solver.
    simpl; auto.
  - apply WF_tannot; auto.
    set_solver.
  - apply Sub_texists_remove; auto.
    apply F_tannot; auto.
    set_solver.
Qed.

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

Lemma not_free_sub :
  (forall i a, not_free_ty i a -> forall b, sub_ty a b -> not_free_ty i b) /\
  (forall i a, not_free_cty i a -> forall b, sub_cty a b -> not_free_cty i b).
Proof.
  apply not_free_mut_ind; intros; auto; try inv H.
  - inv H1.
    constructor.
    + { auto. }
    + apply H0 in H6; auto.
  - inv H1.
    constructor.
    + { auto. }
    + apply H0 in H6; auto.
  - inv H0.
    constructor.
    + apply H in H3; auto.
    + { auto. }
  - inv H0.
    + { auto. }
    + 

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
    + apply Sub_texists_remove.
  - inv H0.
    inv H1.
Qed.

Theorem step_deterministic : deterministic2 step.
Proof.
  unfold deterministic2.
  intros.
  generalize dependent a3.
  generalize dependent b3.
  induction H; intros; try (inv H0).
  - apply IHstep in H6.
    destruct H6; subst; auto.
  - apply IHstep in H8.
    destruct H8; subst; auto.
  - split; auto.
    apply hlist_has_deterministic with (c := co) in H11; subst; auto.
  - destruct H11; try contradiction.
    specialize (H1 co).
    contradiction.
  - destruct H; try contradiction.
    specialize (H co).
    contradiction.
Qed.

Lemma ctx_wellformed : forall i D G T,
  wf_context D G -> nth_error G i = Some T -> wf_ty D T.
Proof.
  intros.
  rewrite List.Forall_forall in H.
  apply nth_error_In in H0.
  apply H in H0.
  auto.
Qed.

Lemma wellformed_weakening :
  (forall D t, wf_ty D t -> forall D', wf_ty (D ++ D') t) /\
  (forall D t, wf_cty D t -> forall D', wf_cty (D ++ D') t).
Proof.
  apply wf_mut_ind; intros; auto.
  - apply WF_tinst with e.
    apply nth_error_weakening.
    auto.
  - constructor.
    rewrite app_comm_cons.
    auto.
Qed.

Lemma wf_context_prepend : forall D t C,
  wf_ty D t -> wf_context D C -> wf_context D (t :: C).
Proof.
  intros.
  constructor; auto.
Qed.

Lemma ty_wellformed :
  (forall E D G v t, has_type_val E D G v t -> wf_context D G -> wf_ty D t) /\
  (forall E D G v t, has_type_comp E D G v t -> wf_context D G -> wf_cty D t) /\
  (forall E D G v t, has_type_hlist E D G v t -> wf_context D G -> wf_cty D t).
Proof.
  apply has_type_mut_ind; intros; auto.
  - apply ctx_wellformed with (i := i) (T := t) in H; auto.
  - apply WF_tinst with (e := E); auto.
  - constructor; auto.
    set_solver.
  - apply H in H1.
    inv H1.
  - { auto. }
  - { auto. }
  - inv u0.
    + constructor.
      * 
