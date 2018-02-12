Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; 
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.
Ltac solve_by_invert :=
  solve_by_inverts 1.
Ltac inversion_try_solve H := inversion H; subst; try reflexivity; try solve_by_invert.
Ltac apply_rewrite_solve H H' := apply H in H'; rewrite H'; auto.
Ltac assert_rewrite H := assert (H_ := H); auto; rewrite H.

Lemma nth_error_nil : forall {t} i,
  @nth_error t nil i = None.
Proof.
  induction i; auto.
Qed.

Lemma skipn_cons : forall {t} n l x,
  @skipn t n l = skipn (S n) (x :: l).
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma nth_error_length : forall {t} l n x,
  @nth_error t l n = Some x -> n < length l.
Proof.
  intros.
  generalize dependent x.
  generalize dependent l.
  induction n.
  induction l.
  - intros.
    inversion H.
  - intros.
    simpl.
    apply PeanoNat.Nat.lt_0_succ.
  - intros.
    destruct l.
    rewrite nth_error_nil in H.
    inversion H.
    inversion H.
    apply IHn in H1.
    simpl.
    apply Lt.lt_n_S.
    assumption.
Qed.

Lemma nth_error_weakening : forall {t} l l' i x,
  @nth_error t l i = Some x ->
  @nth_error t (l ++ l') i = Some x.
Proof.
  intros.
  rewrite <- H.
  apply nth_error_app1.
  apply nth_error_length with (x0 := x).
  assumption.
Qed.

Lemma flip_lt : forall n m,
  n < m <-> m > n.
Proof.
  intros.
  split.
  - generalize dependent m; induction n; intros; auto.
  - generalize dependent m; induction n; intros; auto.
Qed.

Lemma gt_S : forall n m,
  n > m -> S n > m.
Proof.
  induction n; intros; auto.
Qed.

Lemma nth_error_app : forall {t} l h l',
  nth_error (l ++ h :: l') (@length t l) = Some h.
Proof.
  induction l; intros; auto.
  - simpl.
    apply IHl.
Qed.

Lemma nth_error_contraction : forall {t} i l l',
  i < length l ->
  nth_error (l ++ l') i = @nth_error t l i.
Proof.
  induction i; intros; induction l; auto.
  - inversion H.
  - inversion H.
  - simpl.
    simpl in H.
    apply lt_S_n in H.
    apply IHi with (l' := l') in H.
    auto.
Qed.

Lemma nth_error_extension : forall {t} i x l l',
  @nth_error t l i = Some x ->
  nth_error (l ++ l') i = Some x.
Proof.
  induction i; intros; induction l; auto.
  - inversion H.
  - inversion H.
  - simpl.
    simpl in H.
    apply IHi with (x := x) (l' := l') in H.
    auto.
Qed.

Lemma nth_error_pred : forall {t} n h l',
  n > 0 ->
  nth_error l' (pred n) = @nth_error t (h :: l') n.
Proof.
  induction l'; intros; simpl; auto.
  - induction n.
    + inversion H.
    + auto.
  - destruct n.
    + inversion H.
    + auto.
Qed.

Lemma nth_error_prefix : forall {t} l l' n,
  nth_error l n = @nth_error t (l' ++ l) (n + length l').
Proof.
  induction l; intros; simpl.
  - rewrite nth_error_nil.
    symmetry.
    rewrite nth_error_None.
    rewrite app_nil_r.
    omega.
  - induction n.
    + simpl.
      symmetry.
      rewrite nth_error_app.
      auto.
    + simpl.
      rewrite IHl with (l' := l' ++ (a :: nil)).
      rewrite <- app_assoc.
      simpl.
      rewrite app_length.
      simpl.
      rewrite plus_assoc.
      rewrite plus_comm.
      auto.
Qed.

Lemma nth_error_prefix_Some : forall {t} l l' n x,
  nth_error l n = Some x ->
  @nth_error t (l' ++ l) (n + length l') = Some x.
Proof.
  intros.
  rewrite <- H.
  symmetry.
  apply nth_error_prefix.
Qed.

Lemma nth_error_cons_l : forall {t} h l n x,
  n > 0 ->
  nth_error (h :: l) n = Some x ->
  @nth_error t l (pred n) = Some x.
Proof.
  induction n; intros.
  inversion H.
  simpl.
  simpl in H0.
  auto.
Qed.

Lemma nth_error_cons_r : forall {t} h l n x,
  @nth_error t l n = Some x ->
  nth_error (h :: l) (S n) = Some x.
Proof.
  induction n; intros.
  simpl.
  destruct l.
  rewrite nth_error_nil in H.
  inversion H.
  simpl in H.
  auto.
  simpl.
  simpl in H.
  auto.
Qed.


Lemma nth_error_pred_app : forall {t} l l' h n x,
  nth_error (l ++ h :: l') (S (n + length l)) = Some x ->
  @nth_error t (l ++ l') (n + length l) = Some x.
Proof.
  induction l; intros.
  - simpl.
    simpl in H.
    auto.
  - simpl in H.
    simpl.
    rewrite <- plus_n_Sm in H.
    apply IHl in H.
    rewrite <- plus_n_Sm.
    simpl.
    auto.
Qed.

Lemma nth_error_firstn : forall {t} n m l x,
  n < m ->
  @nth_error t l n = Some x ->
  nth_error (firstn m l) n = Some x.
Proof.
  induction n; intros.
  - induction l.
    + rewrite nth_error_nil in H0.
      inversion H0.
    + simpl in H0.
      inversion_try_solve H0.
      destruct m; simpl.
      * inversion H.
      * auto.
  - induction l.
    + rewrite nth_error_nil in H0.
      inversion H0.
    + simpl in H0.
      induction m.
      inversion H.
      simpl.
      apply IHn.
      omega.
      auto.
Qed.

Lemma nth_error_firstn_skipn : forall {t} l n x,
  @nth_error t l n = Some x ->
  nth_error (firstn n l ++ skipn n l) n = Some x.
Proof.
  intros.
  rewrite firstn_skipn.
  auto.
Qed.

Lemma geq_exists : forall n m,
  n >= m -> exists k, n = m + k.
Proof.
  intros.
  generalize dependent m.
  induction m; intros.
  - inversion H.
    exists 0.
    auto.
    exists (S m).
    auto.
  - assert (n >= m).
    omega.
    apply IHm in H0.
    inversion H0.
    exists (pred x).
    omega.
Qed.

Lemma nth_error_skipn : forall {t} i n l x,
  i >= n -> @nth_error t l i = Some x -> nth_error (skipn n l) (i - n) = Some x.
Proof.
  intros.
  generalize dependent n.
  generalize dependent i.
  induction l; intros.
  - rewrite nth_error_nil in H0.
    inversion H0.
  - induction n.
    + simpl.
      rewrite <- minus_n_O.
      auto.
    + simpl.
      assert (i - S n = pred i - n).
      omega.
      rewrite H1.
      apply IHl.
      induction i.
      * inversion H.
      * simpl in H0.
        rewrite Nat.pred_succ.
        auto.
      * omega.
Qed.

Lemma nth_error_firstn_cons_skipn : 
  (forall {t} l n i h x,
    i < n ->
    @nth_error t l i = Some x ->
    nth_error (firstn n l ++ h :: skipn n l) i = Some x) /\
  (forall {t} l n i h x,
    i >= n ->
    @nth_error t l i = Some x ->
    nth_error (firstn n l ++ h :: skipn n l) (S i) = Some x).
Proof.
  split.
  - intros.
    apply nth_error_extension.
    apply nth_error_firstn; auto.
  - intros.
    assert (Hd := ge_dec i (length l)).
    inversion Hd.
    + assert (length l <= i).
      omega.
      apply nth_error_None in H2.
      rewrite H2 in H0.
      inversion H0.
    + assert (i < length l).
      omega.
      clear Hd.
      clear H1.
      assert (n <= length l).
      omega.
      apply firstn_length_le in H1.
      assert (H' := H).
      apply geq_exists in H.
      inversion H.
      rewrite <- H1 in H3.
      rewrite H3.
      rewrite plus_n_Sm.
      rewrite plus_comm.
      rewrite <- nth_error_prefix.
      simpl.
      assert (x0 = i - n).
      omega.
      rewrite H4.
      apply nth_error_skipn.
      auto.
      auto.
Qed.

Lemma nth_error_skip : forall {t} a b i x,
  i >= length a ->
  @nth_error t (a ++ b) i = Some x ->
  nth_error b (i - length a) = Some x.
Proof.
  induction a; intros.
  - simpl.
    rewrite <- minus_n_O.
    simpl in H0.
    auto.
  - simpl.
    simpl in H0.
    apply nth_error_cons_l in H0.
    + assert (i - S (length a0) = pred i - length a0).
      omega.
      rewrite H1.
      apply IHa; auto.
      simpl in H.
      omega.
    + simpl in H.
      omega.
Qed.

Lemma nth_error_firstn_append_skipn_smaller : forall {t} l n i L x,
  i < n ->
  @nth_error t l i = Some x ->
  nth_error (firstn n l ++ L ++ skipn n l) i = Some x.
Proof.
  intros.
  apply nth_error_extension.
  apply nth_error_firstn; auto.
Qed.

Lemma lt_exists : forall a b,
  a <= b -> exists k, a = b - k.
Proof.
  intros.
  exists (b - a).
  induction b.
  + inversion H. auto.
  + omega.
Qed.

Lemma gt_exists : forall a b,
  a >= b -> exists k, b = a - k.
Proof.
  intros.
  exists (a - b).
  induction b.
  + inversion H.
    auto.
    omega.
  + omega.
Qed.

Lemma gt_exists' : forall a b,
  a >= b -> exists k, b + k = a.
Proof.
  intros.
  exists (a - b).
  induction a.
  inversion H.
  auto.
  omega.
Qed.

Lemma nth_error_firstn_append_skipn : forall {t} l n i L x,
  i >= n ->
  @nth_error t l i = Some x ->
  nth_error (firstn n l ++ L ++ skipn n l) (i + (length L)) = Some x.
Proof.
  intros.
  assert (Hd := ge_dec i (length l)).
  destruct Hd.
  + assert (length l <= i).
    omega.
    apply nth_error_None in H1.
    rewrite H1 in H0.
    inversion H0.
  + induction L; simpl.
    * rewrite firstn_skipn.
      rewrite <- plus_n_O.
      auto.
    * assert (i < length l).
      omega.
      assert (n <= length l).
      omega.
      apply firstn_length_le in H2.
      rewrite <- H2 in H.
      assert (H' := H).
      apply gt_exists' in H.
      inversion H.
      rewrite <- H3.
      rewrite plus_comm.
      rewrite plus_assoc.
      rewrite plus_comm.
      rewrite plus_assoc.
      apply nth_error_prefix_Some.
      rewrite plus_comm.
      simpl.
      rewrite plus_comm.
      apply nth_error_prefix_Some.
      rewrite H2 in H3.
      assert (S := @nth_error_skipn t).
      apply S with (l := l) (x := x) in H'; auto.
      rewrite H2 in H'.
      assert (x0 = i - n).
      omega.
      rewrite H4.
      auto.
Qed.
