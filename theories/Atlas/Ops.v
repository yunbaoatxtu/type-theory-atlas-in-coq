(** Binding operations for the shared syntax.

    Ordinary variables and temporal variables form separate namespaces.
    Ordinary binders affect only [tVar], while temporal substitution affects
    only [tTimeVar].
 *)

From Stdlib Require Import Arith.PeanoNat Lia.
From Atlas Require Import Syntax.

Definition shift_index (amount cutoff index : nat) : nat :=
  if Nat.leb cutoff index then amount + index else index.

Lemma shift_index_zero :
  forall cutoff index, shift_index 0 cutoff index = index.
Proof.
  intros cutoff index.
  unfold shift_index.
  destruct (Nat.leb cutoff index); reflexivity.
Qed.

Lemma shift_index_compose :
  forall amount_lower amount_upper lower upper index,
    lower <= upper ->
    shift_index amount_upper (amount_lower + upper)
      (shift_index amount_lower lower index) =
    shift_index amount_lower lower
      (shift_index amount_upper upper index).
Proof.
  intros amount_lower amount_upper lower upper index Hle.
  unfold shift_index.
  destruct (Nat.leb lower index) eqn:Hlower.
  - apply Nat.leb_le in Hlower.
    destruct (Nat.leb upper index) eqn:Hupper.
    + apply Nat.leb_le in Hupper.
      assert (Nat.leb (amount_lower + upper)
        (amount_lower + index) = true) as Hleft.
      { apply Nat.leb_le. lia. }
      assert (Nat.leb lower (amount_upper + index) = true) as Hright.
      { apply Nat.leb_le. lia. }
      rewrite Hleft, Hright.
      lia.
    + apply Nat.leb_gt in Hupper.
      assert (Nat.leb (amount_lower + upper)
        (amount_lower + index) = false) as Hleft.
      { apply Nat.leb_gt. lia. }
      assert (Nat.leb lower index = true) as Hright.
      { apply Nat.leb_le. lia. }
      rewrite Hleft, Hright.
      reflexivity.
  - apply Nat.leb_gt in Hlower.
    assert (Nat.leb upper index = false) as Hupper.
    { apply Nat.leb_gt. lia. }
    assert (Nat.leb (amount_lower + upper) index = false) as Hleft.
    { apply Nat.leb_gt. lia. }
    assert (Nat.leb lower index = false) as Hright.
    { apply Nat.leb_gt. lia. }
    rewrite Hupper, Hleft, Hright.
    reflexivity.
Qed.

Fixpoint shift_term (amount cutoff : nat) (t : term) : term :=
  match t with
  | tVar index => tVar (shift_index amount cutoff index)
  | tUniverse level => tUniverse level
  | tProp => tProp
  | tPi a b => tPi (shift_term amount cutoff a)
                   (shift_term amount (S cutoff) b)
  | tLam body => tLam (shift_term amount (S cutoff) body)
  | tApp f a => tApp (shift_term amount cutoff f)
                    (shift_term amount cutoff a)
  | tSigma a b => tSigma (shift_term amount cutoff a)
                         (shift_term amount (S cutoff) b)
  | tPair a b => tPair (shift_term amount cutoff a)
                       (shift_term amount cutoff b)
  | tFst p => tFst (shift_term amount cutoff p)
  | tSnd p => tSnd (shift_term amount cutoff p)
  | tId a x y => tId (shift_term amount cutoff a)
                     (shift_term amount cutoff x)
                     (shift_term amount cutoff y)
  | tRefl x => tRefl (shift_term amount cutoff x)
  | tTimeVar index => tTimeVar index
  | tAt a time => tAt (shift_term amount cutoff a)
                      (shift_term amount cutoff time)
  | tLater a => tLater (shift_term amount cutoff a)
  | tNext a => tNext (shift_term amount cutoff a)
  | tFix body => tFix (shift_term amount (S cutoff) body)
  | tLaterAt clock a => tLaterAt (shift_term amount cutoff clock)
                                (shift_term amount cutoff a)
  | tNextAt clock t => tNextAt (shift_term amount cutoff clock)
                               (shift_term amount cutoff t)
  | tFixAt clock body => tFixAt (shift_term amount cutoff clock)
                                (shift_term amount (S cutoff) body)
  | tClockPi body => tClockPi (shift_term amount cutoff body)
  | tClockLam body => tClockLam (shift_term amount cutoff body)
  | tClockApp f clock => tClockApp (shift_term amount cutoff f)
                                  (shift_term amount cutoff clock)
  | tDelayedSubst clock body =>
      tDelayedSubst (shift_term amount cutoff clock)
        (shift_term amount cutoff body)
  end.

Fixpoint shift_time (amount cutoff : nat) (t : term) : term :=
  match t with
  | tVar index => tVar index
  | tUniverse level => tUniverse level
  | tProp => tProp
  | tPi a b => tPi (shift_time amount cutoff a)
                   (shift_time amount cutoff b)
  | tLam body => tLam (shift_time amount cutoff body)
  | tApp f a => tApp (shift_time amount cutoff f)
                    (shift_time amount cutoff a)
  | tSigma a b => tSigma (shift_time amount cutoff a)
                         (shift_time amount cutoff b)
  | tPair a b => tPair (shift_time amount cutoff a)
                       (shift_time amount cutoff b)
  | tFst p => tFst (shift_time amount cutoff p)
  | tSnd p => tSnd (shift_time amount cutoff p)
  | tId a x y => tId (shift_time amount cutoff a)
                     (shift_time amount cutoff x)
                     (shift_time amount cutoff y)
  | tRefl x => tRefl (shift_time amount cutoff x)
  | tTimeVar index => tTimeVar (shift_index amount cutoff index)
  | tAt a time => tAt (shift_time amount cutoff a)
                      (shift_time amount cutoff time)
  | tLater a => tLater (shift_time amount cutoff a)
  | tNext a => tNext (shift_time amount cutoff a)
  | tFix body => tFix (shift_time amount cutoff body)
  | tLaterAt clock a => tLaterAt (shift_time amount cutoff clock)
                                (shift_time amount cutoff a)
  | tNextAt clock t => tNextAt (shift_time amount cutoff clock)
                               (shift_time amount cutoff t)
  | tFixAt clock body => tFixAt (shift_time amount cutoff clock)
                                (shift_time amount cutoff body)
  | tClockPi body => tClockPi (shift_time amount (S cutoff) body)
  | tClockLam body => tClockLam (shift_time amount (S cutoff) body)
  | tClockApp f clock => tClockApp (shift_time amount cutoff f)
                                  (shift_time amount cutoff clock)
  | tDelayedSubst clock body =>
      tDelayedSubst (shift_time amount cutoff clock)
        (shift_time amount (S cutoff) body)
  end.

Lemma shift_time_compose :
  forall amount_lower amount_upper lower upper t,
    lower <= upper ->
    shift_time amount_upper (amount_lower + upper)
      (shift_time amount_lower lower t) =
    shift_time amount_lower lower
      (shift_time amount_upper upper t).
Proof.
  intros amount_lower amount_upper lower upper t.
  revert lower upper.
  induction t; intros lower upper Hle; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3 by exact Hle;
    try reflexivity.
  - f_equal.
    apply shift_index_compose.
    exact Hle.
  - rewrite <- Nat.add_succ_r.
    rewrite IHt by lia.
    reflexivity.
  - rewrite <- Nat.add_succ_r.
    rewrite IHt by lia.
    reflexivity.
  - rewrite <- Nat.add_succ_r.
    rewrite IHt2 by lia.
    reflexivity.
Qed.

Lemma shift_time_shift_term_commute :
  forall time_amount time_cutoff term_amount term_cutoff t,
    shift_time time_amount time_cutoff
      (shift_term term_amount term_cutoff t) =
    shift_term term_amount term_cutoff
      (shift_time time_amount time_cutoff t).
Proof.
  intros time_amount time_cutoff term_amount term_cutoff t.
  revert time_cutoff term_cutoff.
  induction t; intros time_cutoff term_cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    reflexivity.
Qed.

Definition substitute_term_index
    (replacement : term) (cutoff index : nat) : term :=
  if Nat.ltb index cutoff then tVar index
  else if Nat.eqb index cutoff then shift_term cutoff 0 replacement
       else tVar (Nat.pred index).

Lemma substitute_term_index_here :
  forall replacement cutoff,
    substitute_term_index replacement cutoff cutoff =
    shift_term cutoff 0 replacement.
Proof.
  intros replacement cutoff.
  unfold substitute_term_index.
  rewrite Nat.ltb_irrefl, Nat.eqb_refl.
  reflexivity.
Qed.

Fixpoint subst_term (replacement : term) (cutoff : nat) (t : term) : term :=
  match t with
  | tVar index => substitute_term_index replacement cutoff index
  | tUniverse level => tUniverse level
  | tProp => tProp
  | tPi a b => tPi (subst_term replacement cutoff a)
                   (subst_term replacement (S cutoff) b)
  | tLam body => tLam (subst_term replacement (S cutoff) body)
  | tApp f a => tApp (subst_term replacement cutoff f)
                    (subst_term replacement cutoff a)
  | tSigma a b => tSigma (subst_term replacement cutoff a)
                         (subst_term replacement (S cutoff) b)
  | tPair a b => tPair (subst_term replacement cutoff a)
                       (subst_term replacement cutoff b)
  | tFst p => tFst (subst_term replacement cutoff p)
  | tSnd p => tSnd (subst_term replacement cutoff p)
  | tId a x y => tId (subst_term replacement cutoff a)
                     (subst_term replacement cutoff x)
                     (subst_term replacement cutoff y)
  | tRefl x => tRefl (subst_term replacement cutoff x)
  | tTimeVar index => tTimeVar index
  | tAt a time => tAt (subst_term replacement cutoff a)
                      (subst_term replacement cutoff time)
  | tLater a => tLater (subst_term replacement cutoff a)
  | tNext a => tNext (subst_term replacement cutoff a)
  | tFix body => tFix (subst_term replacement (S cutoff) body)
  | tLaterAt clock a => tLaterAt (subst_term replacement cutoff clock)
                                (subst_term replacement cutoff a)
  | tNextAt clock t => tNextAt (subst_term replacement cutoff clock)
                               (subst_term replacement cutoff t)
  | tFixAt clock body => tFixAt (subst_term replacement cutoff clock)
                                (subst_term replacement (S cutoff) body)
  | tClockPi body =>
      tClockPi (subst_term (shift_time 1 0 replacement) cutoff body)
  | tClockLam body =>
      tClockLam (subst_term (shift_time 1 0 replacement) cutoff body)
  | tClockApp f clock => tClockApp (subst_term replacement cutoff f)
                                  (subst_term replacement cutoff clock)
  | tDelayedSubst clock body =>
      tDelayedSubst (subst_term replacement cutoff clock)
        (subst_term (shift_time 1 0 replacement) cutoff body)
  end.

Lemma shift_time_substitute_term_index :
  forall time_amount time_cutoff replacement term_cutoff index,
    shift_time time_amount time_cutoff
      (substitute_term_index replacement term_cutoff index) =
    substitute_term_index
      (shift_time time_amount time_cutoff replacement)
      term_cutoff
      index.
Proof.
  intros time_amount time_cutoff replacement term_cutoff index.
  unfold substitute_term_index.
  destruct (Nat.ltb index term_cutoff).
  - reflexivity.
  - destruct (Nat.eqb index term_cutoff).
    + apply shift_time_shift_term_commute.
    + reflexivity.
Qed.

Lemma shift_time_subst_term_commute :
  forall time_amount time_cutoff replacement term_cutoff t,
    shift_time time_amount time_cutoff
      (subst_term replacement term_cutoff t) =
    subst_term
      (shift_time time_amount time_cutoff replacement)
      term_cutoff
      (shift_time time_amount time_cutoff t).
Proof.
  intros time_amount time_cutoff replacement term_cutoff t.
  revert time_cutoff replacement term_cutoff.
  induction t; intros time_cutoff replacement term_cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - apply shift_time_substitute_term_index.
  - rewrite <-
      (shift_time_compose 1 time_amount 0 time_cutoff replacement) by lia.
    reflexivity.
  - rewrite <-
      (shift_time_compose 1 time_amount 0 time_cutoff replacement) by lia.
    reflexivity.
  - rewrite <-
      (shift_time_compose 1 time_amount 0 time_cutoff replacement) by lia.
    reflexivity.
Qed.

Definition substitute_time_index
    (replacement : term) (cutoff index : nat) : term :=
  if Nat.ltb index cutoff then tTimeVar index
  else if Nat.eqb index cutoff then shift_time cutoff 0 replacement
       else tTimeVar (Nat.pred index).

Lemma substitute_time_index_here :
  forall replacement cutoff,
    substitute_time_index replacement cutoff cutoff =
    shift_time cutoff 0 replacement.
Proof.
  intros replacement cutoff.
  unfold substitute_time_index.
  rewrite Nat.ltb_irrefl, Nat.eqb_refl.
  reflexivity.
Qed.

Fixpoint subst_time (replacement : term) (cutoff : nat) (t : term) : term :=
  match t with
  | tVar index => tVar index
  | tUniverse level => tUniverse level
  | tProp => tProp
  | tPi a b => tPi (subst_time replacement cutoff a)
                   (subst_time replacement cutoff b)
  | tLam body => tLam (subst_time replacement cutoff body)
  | tApp f a => tApp (subst_time replacement cutoff f)
                    (subst_time replacement cutoff a)
  | tSigma a b => tSigma (subst_time replacement cutoff a)
                         (subst_time replacement cutoff b)
  | tPair a b => tPair (subst_time replacement cutoff a)
                       (subst_time replacement cutoff b)
  | tFst p => tFst (subst_time replacement cutoff p)
  | tSnd p => tSnd (subst_time replacement cutoff p)
  | tId a x y => tId (subst_time replacement cutoff a)
                     (subst_time replacement cutoff x)
                     (subst_time replacement cutoff y)
  | tRefl x => tRefl (subst_time replacement cutoff x)
  | tTimeVar index => substitute_time_index replacement cutoff index
  | tAt a time => tAt (subst_time replacement cutoff a)
                      (subst_time replacement cutoff time)
  | tLater a => tLater (subst_time replacement cutoff a)
  | tNext a => tNext (subst_time replacement cutoff a)
  | tFix body => tFix (subst_time replacement cutoff body)
  | tLaterAt clock a => tLaterAt (subst_time replacement cutoff clock)
                                (subst_time replacement cutoff a)
  | tNextAt clock t => tNextAt (subst_time replacement cutoff clock)
                               (subst_time replacement cutoff t)
  | tFixAt clock body => tFixAt (subst_time replacement cutoff clock)
                                (subst_time replacement cutoff body)
  | tClockPi body => tClockPi (subst_time replacement (S cutoff) body)
  | tClockLam body => tClockLam (subst_time replacement (S cutoff) body)
  | tClockApp f clock => tClockApp (subst_time replacement cutoff f)
                                  (subst_time replacement cutoff clock)
  | tDelayedSubst clock body =>
      tDelayedSubst (subst_time replacement cutoff clock)
        (subst_time replacement (S cutoff) body)
  end.

Lemma shift_term_zero :
  forall cutoff t, shift_term 0 cutoff t = t.
Proof.
  intros cutoff t.
  revert cutoff.
  induction t; intros cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  now rewrite shift_index_zero.
Qed.

Lemma shift_time_zero :
  forall cutoff t, shift_time 0 cutoff t = t.
Proof.
  intros cutoff t.
  revert cutoff.
  induction t; intros cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  now rewrite shift_index_zero.
Qed.

Lemma supports_shift_term :
  forall s amount cutoff t,
    supports s (shift_term amount cutoff t) = supports s t.
Proof.
  intros s amount cutoff t.
  revert cutoff.
  induction t; intros cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    reflexivity.
Qed.

Lemma supports_shift_time :
  forall s amount cutoff t,
    supports s (shift_time amount cutoff t) = supports s t.
Proof.
  intros s amount cutoff t.
  revert cutoff.
  induction t; intros cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    reflexivity.
Qed.

Lemma supports_substitute_term_index :
  forall s replacement cutoff index,
    supports s replacement = true ->
    supports s (substitute_term_index replacement cutoff index) = true.
Proof.
  intros s replacement cutoff index Hreplacement.
  unfold substitute_term_index.
  destruct (Nat.ltb index cutoff).
  - reflexivity.
  - destruct (Nat.eqb index cutoff).
    + rewrite supports_shift_term.
      exact Hreplacement.
    + reflexivity.
Qed.

Lemma supports_subst_term :
  forall s replacement cutoff t,
    supports s replacement = true ->
    supports s t = true ->
    supports s (subst_term replacement cutoff t) = true.
Proof.
  intros s replacement cutoff t Hreplacement Hsupport.
  revert replacement cutoff Hreplacement Hsupport.
  induction t; intros replacement cutoff Hreplacement Hsupport; simpl in *;
    repeat rewrite Bool.andb_true_iff in *;
    assert (Hshifted :
      supports s (shift_time 1 0 replacement) = true)
      by (rewrite supports_shift_time; exact Hreplacement);
    intuition eauto using supports_substitute_term_index.
Qed.

Lemma supports_substitute_time_index :
  forall s replacement cutoff index,
    has_temporal_dependency s = true ->
    supports s replacement = true ->
    supports s (substitute_time_index replacement cutoff index) = true.
Proof.
  intros s replacement cutoff index Htemporal Hreplacement.
  unfold substitute_time_index.
  destruct (Nat.ltb index cutoff).
  - exact Htemporal.
  - destruct (Nat.eqb index cutoff).
    + rewrite supports_shift_time.
      exact Hreplacement.
    + exact Htemporal.
Qed.

Lemma supports_subst_time :
  forall s replacement cutoff t,
    has_temporal_dependency s = true ->
    supports s replacement = true ->
    supports s t = true ->
    supports s (subst_time replacement cutoff t) = true.
Proof.
  intros s replacement cutoff t Htemporal Hreplacement.
  revert cutoff.
  induction t; intros cutoff Hsupport; simpl in *;
    repeat rewrite Bool.andb_true_iff in *;
    intuition eauto using supports_substitute_time_index.
Qed.

Lemma subst_term_var_zero :
  forall replacement,
    subst_term replacement 0 (tVar 0) = replacement.
Proof.
  intros replacement.
  simpl.
  apply shift_term_zero.
Qed.

Lemma subst_time_var_zero :
  forall replacement,
    subst_time replacement 0 (tTimeVar 0) = replacement.
Proof.
  intros replacement.
  simpl.
  apply shift_time_zero.
Qed.

Example beta_substitution_example :
  subst_term (tUniverse 0) 0 (tApp (tVar 1) (tVar 0)) =
  tApp (tVar 0) (tUniverse 0).
Proof. reflexivity. Qed.

Example time_substitution_example :
  subst_time (tTimeVar 2) 0 (tLater (tTimeVar 0)) =
  tLater (tTimeVar 2).
Proof. reflexivity. Qed.
