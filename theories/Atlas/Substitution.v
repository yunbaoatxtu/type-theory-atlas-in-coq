(** Substitution for MLTT typing derivations.

    This file first establishes the De Bruijn algebra needed to remove a
    declaration from a context, then lifts substitution from lookups to full
    typing derivations.
 *)

From Stdlib Require Import Arith.PeanoNat Lia List.
From Atlas Require Import Syntax Ops Context DefEq MLTT Weakening.

Import ListNotations.

Lemma shift_index_same_cutoff_add :
  forall first second cutoff index,
    shift_index second cutoff (shift_index first cutoff index) =
    shift_index (second + first) cutoff index.
Proof.
  intros first second cutoff index.
  unfold shift_index.
  destruct (Nat.leb cutoff index) eqn:Hindex.
  - apply Nat.leb_le in Hindex.
    assert (Nat.leb cutoff (first + index) = true) as Hshifted.
    { apply Nat.leb_le. lia. }
    rewrite Hshifted.
    lia.
  - rewrite Hindex.
    reflexivity.
Qed.

Lemma shift_term_same_cutoff_add :
  forall first second cutoff t,
    shift_term second cutoff (shift_term first cutoff t) =
    shift_term (second + first) cutoff t.
Proof.
  intros first second cutoff t.
  revert cutoff.
  induction t; intros cutoff; simpl.
  - f_equal.
    apply shift_index_same_cutoff_add.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - rewrite IHt1, IHt2, IHt3.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - rewrite IHt.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
Qed.

Lemma substitute_term_index_shift_cancel :
  forall replacement cutoff index,
    substitute_term_index replacement cutoff
      (shift_index 1 cutoff index) =
    tVar index.
Proof.
  intros replacement cutoff index.
  unfold shift_index, substitute_term_index.
  destruct (Nat.leb cutoff index) eqn:Hindex.
  - apply Nat.leb_le in Hindex.
    assert (Nat.ltb (1 + index) cutoff = false) as Hlt.
    { apply Nat.ltb_ge. lia. }
    assert (Nat.eqb (1 + index) cutoff = false) as Heq.
    { apply Nat.eqb_neq. lia. }
    rewrite Hlt, Heq.
    f_equal.
  - apply Nat.leb_gt in Hindex.
    assert (Nat.ltb index cutoff = true) as Hlt.
    { apply Nat.ltb_lt. lia. }
    rewrite Hlt.
    reflexivity.
Qed.

Lemma subst_term_shift_cancel :
  forall replacement cutoff t,
    subst_term replacement cutoff (shift_term 1 cutoff t) = t.
Proof.
  intros replacement cutoff t.
  revert replacement cutoff.
  induction t; intros replacement cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  apply substitute_term_index_shift_cancel.
Qed.

Lemma shift_index_zero_cutoff :
  forall amount index,
    shift_index amount 0 index = amount + index.
Proof.
  intros amount index.
  unfold shift_index.
  simpl.
  reflexivity.
Qed.

Lemma shift_index_prefix_add :
  forall amount prefix offset depth index,
    offset <= prefix ->
    shift_index amount (offset + depth)
      (shift_index prefix depth index) =
    shift_index (amount + prefix) depth index.
Proof.
  intros amount prefix offset depth index Hoffset.
  unfold shift_index.
  destruct (Nat.leb depth index) eqn:Hdepth.
  - apply Nat.leb_le in Hdepth.
    assert (Nat.leb (offset + depth) (prefix + index) = true)
      as Hshifted.
    { apply Nat.leb_le. lia. }
    rewrite Hshifted.
    lia.
  - apply Nat.leb_gt in Hdepth.
    assert (Nat.leb (offset + depth) index = false) as Hbelow.
    { apply Nat.leb_gt. lia. }
    rewrite Hbelow.
    reflexivity.
Qed.

Lemma shift_term_prefix_add :
  forall amount prefix offset depth t,
    offset <= prefix ->
    shift_term amount (offset + depth) (shift_term prefix depth t) =
    shift_term (amount + prefix) depth t.
Proof.
  intros amount prefix offset depth t.
  revert depth.
  induction t; intros depth Hoffset; simpl.
  - f_equal.
    apply shift_index_prefix_add.
    exact Hoffset.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1 by exact Hoffset.
    replace (S (offset + depth)) with (offset + S depth) by lia.
    rewrite IHt2 by exact Hoffset.
    reflexivity.
  - replace (S (offset + depth)) with (offset + S depth) by lia.
    rewrite IHt by exact Hoffset.
    reflexivity.
  - rewrite IHt1, IHt2 by exact Hoffset.
    reflexivity.
  - rewrite IHt1 by exact Hoffset.
    replace (S (offset + depth)) with (offset + S depth) by lia.
    rewrite IHt2 by exact Hoffset.
    reflexivity.
  - rewrite IHt1, IHt2 by exact Hoffset.
    reflexivity.
  - rewrite IHt by exact Hoffset.
    reflexivity.
  - rewrite IHt by exact Hoffset.
    reflexivity.
  - rewrite IHt1, IHt2, IHt3 by exact Hoffset.
    reflexivity.
  - rewrite IHt by exact Hoffset.
    reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2 by exact Hoffset.
    reflexivity.
  - rewrite IHt by exact Hoffset.
    reflexivity.
  - rewrite IHt by exact Hoffset.
    reflexivity.
  - replace (S (offset + depth)) with (offset + S depth) by lia.
    rewrite IHt by exact Hoffset.
    reflexivity.
  - rewrite IHt1, IHt2 by exact Hoffset.
    reflexivity.
  - rewrite IHt1, IHt2 by exact Hoffset.
    reflexivity.
  - rewrite IHt1 by exact Hoffset.
    replace (S (offset + depth)) with (offset + S depth) by lia.
    rewrite IHt2 by exact Hoffset.
    reflexivity.
  - rewrite IHt by exact Hoffset.
    reflexivity.
  - rewrite IHt by exact Hoffset.
    reflexivity.
  - rewrite IHt1, IHt2 by exact Hoffset.
    reflexivity.
  - rewrite IHt1, IHt2 by exact Hoffset.
    reflexivity.
Qed.

Lemma substitute_term_index_shift_prefix_depth :
  forall replacement amount cutoff depth index,
    substitute_term_index replacement (amount + cutoff + depth)
      (shift_index amount depth index) =
    shift_term amount depth
      (substitute_term_index replacement (cutoff + depth) index).
Proof.
  intros replacement amount cutoff depth index.
  unfold shift_index at 1.
  destruct (Nat.leb depth index) eqn:Hdepth.
  - apply Nat.leb_le in Hdepth.
    unfold substitute_term_index.
    destruct (Nat.ltb index (cutoff + depth)) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      assert (Nat.ltb (amount + index) (amount + cutoff + depth) = true)
        as Hlt_shifted.
      { apply Nat.ltb_lt. lia. }
      rewrite Hlt_shifted.
      simpl.
      unfold shift_index.
      assert (Nat.leb depth index = true) as Hdepth_bool.
      { apply Nat.leb_le. lia. }
      rewrite Hdepth_bool.
      reflexivity.
    + destruct (Nat.eqb index (cutoff + depth)) eqn:Heq.
      * apply Nat.eqb_eq in Heq.
        subst index.
        assert (Nat.ltb (amount + (cutoff + depth))
          (amount + cutoff + depth) = false) as Hlt_shifted.
        { apply Nat.ltb_ge. lia. }
        assert (Nat.eqb (amount + (cutoff + depth))
          (amount + cutoff + depth) = true) as Heq_shifted.
        { apply Nat.eqb_eq. lia. }
        rewrite Hlt_shifted, Heq_shifted.
        replace (amount + cutoff + depth)
          with (amount + (cutoff + depth)) by lia.
        symmetry.
        pose proof (shift_term_prefix_add
          amount (cutoff + depth) depth 0 replacement ltac:(lia))
          as Hprefix.
        replace (depth + 0) with depth in Hprefix by lia.
        exact Hprefix.
      * apply Nat.ltb_ge in Hlt.
        apply Nat.eqb_neq in Heq.
        assert (cutoff + depth < index) as Hgt by lia.
        assert (Nat.ltb (amount + index) (amount + cutoff + depth) = false)
          as Hlt_shifted.
        { apply Nat.ltb_ge. lia. }
        assert (Nat.eqb (amount + index) (amount + cutoff + depth) = false)
          as Heq_shifted.
        { apply Nat.eqb_neq. lia. }
        rewrite Hlt_shifted, Heq_shifted.
        simpl.
        unfold shift_index.
        assert (Nat.leb depth (Nat.pred index) = true) as Hdepth_pred.
        { apply Nat.leb_le. lia. }
        rewrite Hdepth_pred.
        f_equal.
        lia.
  - apply Nat.leb_gt in Hdepth.
    unfold substitute_term_index.
    assert (Nat.ltb index (amount + cutoff + depth) = true)
      as Hlt_left.
    { apply Nat.ltb_lt. lia. }
    assert (Nat.ltb index (cutoff + depth) = true) as Hlt_right.
    { apply Nat.ltb_lt. lia. }
    rewrite Hlt_left, Hlt_right.
    simpl.
    unfold shift_index.
    assert (Nat.leb depth index = false) as Hdepth_bool.
    { apply Nat.leb_gt. lia. }
    rewrite Hdepth_bool.
    reflexivity.
Qed.

Lemma subst_term_shift_prefix_depth :
  forall replacement amount cutoff depth t,
    subst_term replacement (amount + cutoff + depth)
      (shift_term amount depth t) =
    shift_term amount depth
      (subst_term replacement (cutoff + depth) t).
Proof.
  intros replacement amount cutoff depth t.
  revert replacement depth.
  induction t; intros replacement depth; simpl.
  - apply substitute_term_index_shift_prefix_depth.
  - reflexivity.
  - reflexivity.
  - rewrite (IHt1 replacement depth).
    replace (S (amount + cutoff + depth))
      with (amount + cutoff + S depth) by lia.
    replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite (IHt2 replacement (S depth)).
    reflexivity.
  - replace (S (amount + cutoff + depth))
      with (amount + cutoff + S depth) by lia.
    replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite (IHt replacement (S depth)).
    reflexivity.
  - rewrite (IHt1 replacement depth), (IHt2 replacement depth).
    reflexivity.
  - rewrite (IHt1 replacement depth).
    replace (S (amount + cutoff + depth))
      with (amount + cutoff + S depth) by lia.
    replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite (IHt2 replacement (S depth)).
    reflexivity.
  - rewrite (IHt1 replacement depth), (IHt2 replacement depth).
    reflexivity.
  - rewrite (IHt replacement depth).
    reflexivity.
  - rewrite (IHt replacement depth).
    reflexivity.
  - rewrite (IHt1 replacement depth), (IHt2 replacement depth),
      (IHt3 replacement depth).
    reflexivity.
  - rewrite (IHt replacement depth).
    reflexivity.
  - reflexivity.
  - rewrite (IHt1 replacement depth), (IHt2 replacement depth).
    reflexivity.
  - rewrite (IHt replacement depth).
    reflexivity.
  - rewrite (IHt replacement depth).
    reflexivity.
  - replace (S (amount + cutoff + depth))
      with (amount + cutoff + S depth) by lia.
    replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite (IHt replacement (S depth)).
    reflexivity.
  - rewrite (IHt1 replacement depth), (IHt2 replacement depth).
    reflexivity.
  - rewrite (IHt1 replacement depth), (IHt2 replacement depth).
    reflexivity.
  - rewrite (IHt1 replacement depth).
    replace (S (amount + cutoff + depth))
      with (amount + cutoff + S depth) by lia.
    replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite (IHt2 replacement (S depth)).
    reflexivity.
  - rewrite (IHt (shift_time 1 0 replacement) depth).
    reflexivity.
  - rewrite (IHt (shift_time 1 0 replacement) depth).
    reflexivity.
  - rewrite (IHt1 replacement depth), (IHt2 replacement depth).
    reflexivity.
  - rewrite (IHt1 replacement depth).
    rewrite (IHt2 (shift_time 1 0 replacement) depth).
    reflexivity.
Qed.

Corollary subst_term_shift_prefix :
  forall replacement amount cutoff t,
    subst_term replacement (amount + cutoff) (shift_term amount 0 t) =
    shift_term amount 0 (subst_term replacement cutoff t).
Proof.
  intros replacement amount cutoff t.
  pose proof (subst_term_shift_prefix_depth
    replacement amount cutoff 0 t) as Hprefix.
  replace (amount + cutoff + 0) with (amount + cutoff) in Hprefix by lia.
  replace (cutoff + 0) with cutoff in Hprefix by lia.
  exact Hprefix.
Qed.

Lemma subst_term_shift_prefix_drop :
  forall replacement cutoff extra t,
    subst_term replacement cutoff
      (shift_term (S (cutoff + extra)) 0 t) =
    shift_term (cutoff + extra) 0 t.
Proof.
  intros replacement cutoff extra t.
  pose proof (subst_term_shift_prefix
    replacement cutoff 0 (shift_term (S extra) 0 t)) as Hprefix.
  replace (cutoff + 0) with cutoff in Hprefix by lia.
  rewrite shift_term_same_cutoff_add in Hprefix.
  replace (cutoff + S extra) with (S (cutoff + extra)) in Hprefix by lia.
  pose proof (subst_term_shift_cancel
    replacement 0 (shift_term extra 0 t)) as Hcancel.
  rewrite shift_term_same_cutoff_add in Hcancel.
  replace (1 + extra) with (S extra) in Hcancel by lia.
  rewrite Hcancel in Hprefix.
  rewrite shift_term_same_cutoff_add in Hprefix.
  exact Hprefix.
Qed.

Lemma substitute_term_index_compose :
  forall replacement argument outer_cutoff inner_cutoff index,
    subst_term replacement (inner_cutoff + outer_cutoff)
      (substitute_term_index argument inner_cutoff index) =
    subst_term
      (subst_term replacement outer_cutoff argument)
      inner_cutoff
      (substitute_term_index replacement
        (S (inner_cutoff + outer_cutoff)) index).
Proof.
  intros replacement argument outer_cutoff inner_cutoff index.
  destruct (Nat.lt_trichotomy index inner_cutoff)
    as [Hlt | [Heq | Hgt]].
  - assert (Nat.ltb index inner_cutoff = true) as Hinner.
    { apply Nat.ltb_lt. lia. }
    assert (Nat.ltb index (inner_cutoff + outer_cutoff) = true)
      as Houter.
    { apply Nat.ltb_lt. lia. }
    assert (Nat.ltb index (S (inner_cutoff + outer_cutoff)) = true)
      as Houter_deeper.
    { apply Nat.ltb_lt. lia. }
    cbn [subst_term].
    unfold substitute_term_index.
    rewrite Hinner, Houter_deeper.
    cbn [subst_term].
    unfold substitute_term_index.
    rewrite Houter, Hinner.
    reflexivity.
  - subst index.
    assert (Nat.ltb inner_cutoff inner_cutoff = false) as Hinner_lt.
    { apply Nat.ltb_irrefl. }
    assert (Nat.eqb inner_cutoff inner_cutoff = true) as Hinner_eq.
    { apply Nat.eqb_refl. }
    assert (Nat.ltb inner_cutoff (S (inner_cutoff + outer_cutoff)) = true)
      as Houter_deeper.
    { apply Nat.ltb_lt. lia. }
    cbn [subst_term].
    unfold substitute_term_index.
    rewrite Hinner_lt, Hinner_eq, Houter_deeper.
    cbn [subst_term].
    unfold substitute_term_index.
    rewrite Hinner_lt, Hinner_eq.
    apply subst_term_shift_prefix.
  - destruct (Nat.lt_trichotomy index (S (inner_cutoff + outer_cutoff)))
      as [Hbelow | [Heq | Habove]].
    + assert (Nat.ltb index inner_cutoff = false) as Hinner_lt.
      { apply Nat.ltb_ge. lia. }
      assert (Nat.eqb index inner_cutoff = false) as Hinner_eq.
      { apply Nat.eqb_neq. lia. }
      assert (Nat.ltb index (S (inner_cutoff + outer_cutoff)) = true)
        as Houter_deeper.
      { apply Nat.ltb_lt. lia. }
      assert (Nat.ltb (Nat.pred index) (inner_cutoff + outer_cutoff) = true)
        as Houter.
      { apply Nat.ltb_lt. lia. }
      cbn [subst_term].
      unfold substitute_term_index.
      rewrite Hinner_lt, Hinner_eq, Houter_deeper.
      cbn [subst_term].
      unfold substitute_term_index.
      rewrite Houter.
      rewrite Hinner_lt, Hinner_eq.
      reflexivity.
    + subst index.
      assert (Nat.ltb (S (inner_cutoff + outer_cutoff)) inner_cutoff = false)
        as Hinner_lt.
      { apply Nat.ltb_ge. lia. }
      assert (Nat.eqb (S (inner_cutoff + outer_cutoff)) inner_cutoff = false)
        as Hinner_eq.
      { apply Nat.eqb_neq. lia. }
      assert (Nat.ltb (S (inner_cutoff + outer_cutoff))
        (S (inner_cutoff + outer_cutoff)) = false) as Houter_lt.
      { apply Nat.ltb_irrefl. }
      assert (Nat.eqb (S (inner_cutoff + outer_cutoff))
        (S (inner_cutoff + outer_cutoff)) = true) as Houter_eq.
      { apply Nat.eqb_refl. }
      assert (Nat.ltb (inner_cutoff + outer_cutoff)
        (inner_cutoff + outer_cutoff) = false) as Hleft_lt.
      { apply Nat.ltb_irrefl. }
      assert (Nat.eqb (inner_cutoff + outer_cutoff)
        (inner_cutoff + outer_cutoff) = true) as Hleft_eq.
      { apply Nat.eqb_refl. }
      cbn [subst_term].
      unfold substitute_term_index.
      rewrite Hinner_lt, Hinner_eq, Houter_lt, Houter_eq.
      cbn [subst_term].
      unfold substitute_term_index.
      replace (Nat.pred (S (inner_cutoff + outer_cutoff)))
        with (inner_cutoff + outer_cutoff) by reflexivity.
      rewrite Hleft_lt, Hleft_eq.
      symmetry.
      apply subst_term_shift_prefix_drop.
    + assert (Nat.ltb index inner_cutoff = false) as Hinner_lt.
      { apply Nat.ltb_ge. lia. }
      assert (Nat.eqb index inner_cutoff = false) as Hinner_eq.
      { apply Nat.eqb_neq. lia. }
      assert (Nat.ltb index (S (inner_cutoff + outer_cutoff)) = false)
        as Houter_deeper_lt.
      { apply Nat.ltb_ge. lia. }
      assert (Nat.eqb index (S (inner_cutoff + outer_cutoff)) = false)
        as Houter_deeper_eq.
      { apply Nat.eqb_neq. lia. }
      assert (Nat.ltb (Nat.pred index) (inner_cutoff + outer_cutoff) = false)
        as Houter_lt.
      { apply Nat.ltb_ge. lia. }
      assert (Nat.eqb (Nat.pred index) (inner_cutoff + outer_cutoff) = false)
        as Houter_eq.
      { apply Nat.eqb_neq. lia. }
      assert (Nat.ltb (Nat.pred index) inner_cutoff = false)
        as Hinner_pred_lt.
      { apply Nat.ltb_ge. lia. }
      assert (Nat.eqb (Nat.pred index) inner_cutoff = false)
        as Hinner_pred_eq.
      { apply Nat.eqb_neq. lia. }
      cbn [subst_term].
      unfold substitute_term_index.
      rewrite Hinner_lt, Hinner_eq, Houter_deeper_lt, Houter_deeper_eq.
      cbn [subst_term].
      unfold substitute_term_index.
      rewrite Houter_lt, Houter_eq, Hinner_pred_lt, Hinner_pred_eq.
      reflexivity.
Qed.

Lemma subst_term_compose :
  forall replacement argument outer_cutoff inner_cutoff t,
    subst_term replacement (inner_cutoff + outer_cutoff)
      (subst_term argument inner_cutoff t) =
    subst_term
      (subst_term replacement outer_cutoff argument)
      inner_cutoff
      (subst_term replacement (S (inner_cutoff + outer_cutoff)) t).
Proof.
  intros replacement argument outer_cutoff inner_cutoff t.
  revert replacement argument inner_cutoff.
  induction t; intros replacement argument inner_cutoff; simpl.
  - apply substitute_term_index_compose.
  - reflexivity.
  - reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff).
    replace (S (inner_cutoff + outer_cutoff))
      with (S inner_cutoff + outer_cutoff) by lia.
    rewrite (IHt2 replacement argument (S inner_cutoff)).
    reflexivity.
  - replace (S (inner_cutoff + outer_cutoff))
      with (S inner_cutoff + outer_cutoff) by lia.
    rewrite (IHt replacement argument (S inner_cutoff)).
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff),
      (IHt2 replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff).
    replace (S (inner_cutoff + outer_cutoff))
      with (S inner_cutoff + outer_cutoff) by lia.
    rewrite (IHt2 replacement argument (S inner_cutoff)).
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff),
      (IHt2 replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff),
      (IHt2 replacement argument inner_cutoff),
      (IHt3 replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt replacement argument inner_cutoff).
    reflexivity.
  - reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff),
      (IHt2 replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt replacement argument inner_cutoff).
    reflexivity.
  - replace (S (inner_cutoff + outer_cutoff))
      with (S inner_cutoff + outer_cutoff) by lia.
    rewrite (IHt replacement argument (S inner_cutoff)).
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff),
      (IHt2 replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff),
      (IHt2 replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff).
    replace (S (inner_cutoff + outer_cutoff))
      with (S inner_cutoff + outer_cutoff) by lia.
    rewrite (IHt2 replacement argument (S inner_cutoff)).
    reflexivity.
  - rewrite (IHt (shift_time 1 0 replacement)
      (shift_time 1 0 argument) inner_cutoff).
    rewrite <- shift_time_subst_term_commute.
    reflexivity.
  - rewrite (IHt (shift_time 1 0 replacement)
      (shift_time 1 0 argument) inner_cutoff).
    rewrite <- shift_time_subst_term_commute.
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff),
      (IHt2 replacement argument inner_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement argument inner_cutoff).
    rewrite (IHt2 (shift_time 1 0 replacement)
      (shift_time 1 0 argument) inner_cutoff).
    rewrite <- shift_time_subst_term_commute.
    reflexivity.
Qed.

Corollary subst_term_compose_zero :
  forall replacement argument cutoff t,
    subst_term replacement cutoff (subst_term argument 0 t) =
    subst_term
      (subst_term replacement cutoff argument)
      0
      (subst_term replacement (S cutoff) t).
Proof.
  intros replacement argument cutoff t.
  pose proof (subst_term_compose replacement argument cutoff 0 t)
    as Hcompose.
  replace (0 + cutoff) with cutoff in Hcompose by lia.
  exact Hcompose.
Qed.

Lemma shift_time_same_cutoff_add_for_substitution :
  forall first second cutoff t,
    shift_time second cutoff (shift_time first cutoff t) =
    shift_time (second + first) cutoff t.
Proof.
  intros first second cutoff t.
  revert cutoff.
  induction t; intros cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  f_equal.
  apply shift_index_same_cutoff_add.
Qed.

Lemma subst_time_var_shift_succ_depth_cancel :
  forall clock_index cutoff depth t,
    subst_time (tTimeVar clock_index) (cutoff + depth)
      (shift_time (S cutoff) depth t) =
    shift_time cutoff depth t.
Proof.
  intros clock_index cutoff depth t.
  revert cutoff depth.
  induction t; intros cutoff depth; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - unfold substitute_time_index, shift_index.
    destruct (Nat.leb depth n) eqn:Hdepth.
    + apply Nat.leb_le in Hdepth.
      assert (Nat.ltb (S cutoff + n) (cutoff + depth) = false) as Hlt.
      { apply Nat.ltb_ge. lia. }
      assert (Nat.eqb (S cutoff + n) (cutoff + depth) = false) as Heq.
      { apply Nat.eqb_neq. lia. }
      rewrite Hlt, Heq.
      f_equal; lia.
    + apply Nat.leb_gt in Hdepth.
      assert (Nat.ltb n (cutoff + depth) = true) as Hlt.
      { apply Nat.ltb_lt. lia. }
      rewrite Hlt.
      reflexivity.
  - replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite IHt.
    reflexivity.
  - replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite IHt.
    reflexivity.
  - replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite IHt2.
    reflexivity.
Qed.

Corollary subst_time_var_shift_succ_zero_cancel :
  forall clock_index cutoff t,
    subst_time (tTimeVar clock_index) cutoff
      (shift_time (S cutoff) 0 t) =
    shift_time cutoff 0 t.
Proof.
  intros clock_index cutoff t.
  pose proof (subst_time_var_shift_succ_depth_cancel
    clock_index cutoff 0 t) as Hcancel.
  replace (cutoff + 0) with cutoff in Hcancel by lia.
  exact Hcancel.
Qed.

Lemma substitute_term_index_clock_beta_commute :
  forall replacement term_cutoff clock_index time_cutoff index,
    substitute_term_index
      (shift_time time_cutoff 0 replacement)
      term_cutoff
      index =
    subst_time
      (tTimeVar clock_index)
      time_cutoff
      (substitute_term_index
        (shift_time (S time_cutoff) 0 replacement)
        term_cutoff
        index).
Proof.
  intros replacement term_cutoff clock_index time_cutoff index.
  unfold substitute_term_index.
  destruct (Nat.ltb index term_cutoff).
  - reflexivity.
  - destruct (Nat.eqb index term_cutoff).
    + rewrite <- shift_term_subst_time_var_commute.
      rewrite subst_time_var_shift_succ_zero_cancel.
      reflexivity.
    + reflexivity.
Qed.

Lemma subst_term_clock_beta_commute :
  forall replacement term_cutoff clock_index time_cutoff t,
    subst_term
      (shift_time time_cutoff 0 replacement)
      term_cutoff
      (subst_time (tTimeVar clock_index) time_cutoff t) =
    subst_time
      (tTimeVar clock_index)
      time_cutoff
      (subst_term
        (shift_time (S time_cutoff) 0 replacement)
        term_cutoff
        t).
Proof.
  intros replacement term_cutoff clock_index time_cutoff t.
  revert replacement term_cutoff time_cutoff.
  induction t; intros replacement term_cutoff time_cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - apply substitute_term_index_clock_beta_commute.
  - unfold substitute_time_index.
    repeat
      match goal with
      | |- context [Nat.ltb ?left ?right] =>
          destruct (Nat.ltb left right) eqn:?
      | |- context [Nat.eqb ?left ?right] =>
          destruct (Nat.eqb left right) eqn:?
      end;
      reflexivity.
  - rewrite !shift_time_same_cutoff_add_for_substitution.
    replace (1 + time_cutoff) with (S time_cutoff) by lia.
    replace (1 + S time_cutoff) with (S (S time_cutoff)) by lia.
    f_equal.
    apply IHt.
  - rewrite !shift_time_same_cutoff_add_for_substitution.
    replace (1 + time_cutoff) with (S time_cutoff) by lia.
    replace (1 + S time_cutoff) with (S (S time_cutoff)) by lia.
    f_equal.
    apply IHt.
  - rewrite !shift_time_same_cutoff_add_for_substitution.
    replace (1 + time_cutoff) with (S time_cutoff) by lia.
    replace (1 + S time_cutoff) with (S (S time_cutoff)) by lia.
    f_equal.
    apply IHt2.
Qed.

Corollary subst_term_clock_beta_zero :
  forall replacement cutoff clock_index body,
    subst_term replacement cutoff
      (subst_time (tTimeVar clock_index) 0 body) =
    subst_time
      (tTimeVar clock_index)
      0
      (subst_term (shift_time 1 0 replacement) cutoff body).
Proof.
  intros replacement cutoff clock_index body.
  pose proof (subst_term_clock_beta_commute
    replacement cutoff clock_index 0 body) as Hcommute.
  rewrite shift_time_zero in Hcommute.
  exact Hcommute.
Qed.

Corollary subst_term_shift_one :
  forall replacement cutoff t,
    subst_term replacement (S cutoff) (shift_term 1 0 t) =
    shift_term 1 0 (subst_term replacement cutoff t).
Proof.
  intros replacement cutoff t.
  pose proof (subst_term_shift_prefix replacement 1 cutoff t) as Hprefix.
  replace (1 + cutoff) with (S cutoff) in Hprefix by lia.
  exact Hprefix.
Qed.

Corollary substitute_term_index_shift_one :
  forall replacement cutoff index,
    substitute_term_index replacement (S cutoff) (S index) =
    shift_term 1 0
      (substitute_term_index replacement cutoff index).
Proof.
  intros replacement cutoff index.
  change (subst_term replacement (S cutoff)
    (shift_term 1 0 (tVar index)) =
    shift_term 1 0 (subst_term replacement cutoff (tVar index))).
  apply subst_term_shift_one.
Qed.

Lemma defeq_subst_term :
  forall t u,
    defeq t u ->
    forall replacement cutoff,
      defeq
        (subst_term replacement cutoff t)
        (subst_term replacement cutoff u).
Proof.
  intros t u Heq.
  induction Heq; intros replacement cutoff; simpl.
  - apply de_refl.
  - apply de_sym.
    apply IHHeq.
  - eapply de_trans.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite subst_term_compose_zero.
    apply de_beta.
  - apply de_fst_pair.
  - apply de_snd_pair.
  - apply de_pi.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_lam.
    apply IHHeq.
  - apply de_app.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_sigma.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_pair.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_fst.
    apply IHHeq.
  - apply de_snd.
    apply IHHeq.
  - apply de_id.
    + apply IHHeq1.
    + apply IHHeq2.
    + apply IHHeq3.
  - apply de_refl_term.
    apply IHHeq.
  - apply de_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_later.
    apply IHHeq.
  - apply de_next.
    apply IHHeq.
  - rewrite subst_term_compose_zero.
    apply de_fix_unfold.
  - apply de_fix.
    apply IHHeq.
  - apply de_later_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_next_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite subst_term_compose_zero.
    apply de_fix_at_unfold.
  - apply de_fix_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite subst_term_clock_beta_zero.
    apply de_clock_beta.
  - apply de_clock_pi.
    apply IHHeq.
  - apply de_clock_lam.
    apply IHHeq.
  - apply de_clock_app.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite subst_term_clock_beta_zero.
    apply de_delayed_subst_compute.
  - apply de_delayed_subst.
    + apply IHHeq1.
    + apply IHHeq2.
Qed.

Inductive substitute_context (replacement : term) :
    nat -> context -> context -> Prop :=
| substitute_context_here :
    forall gamma a,
      wf_context gamma ->
      has_type gamma replacement a ->
      substitute_context replacement 0 (a :: gamma) gamma
| substitute_context_there :
    forall cutoff gamma delta a level,
      substitute_context replacement cutoff gamma delta ->
      has_type delta
        (subst_term replacement cutoff a)
        (tUniverse level) ->
      substitute_context replacement (S cutoff) (a :: gamma)
        (subst_term replacement cutoff a :: delta).

Lemma substitute_context_target_wf :
  forall replacement cutoff gamma delta,
    substitute_context replacement cutoff gamma delta ->
    wf_context delta.
Proof.
  intros replacement cutoff gamma delta Hcontext.
  induction Hcontext.
  - exact H.
  - apply wf_extend with (level := level).
    + exact IHHcontext.
    + exact H.
Qed.

Lemma lookup_substitute :
  forall replacement cutoff gamma delta index a,
    substitute_context replacement cutoff gamma delta ->
    lookup gamma index a ->
    has_type delta
      (subst_term replacement cutoff (tVar index))
      (subst_term replacement cutoff a).
Proof.
  intros replacement cutoff gamma delta index a Hcontext.
  revert index a.
  induction Hcontext; intros index b Hlookup.
  - inversion Hlookup; subst.
    + simpl.
      rewrite subst_term_shift_cancel.
      unfold substitute_term_index.
      simpl.
      rewrite shift_term_zero.
      exact H0.
    + simpl.
      rewrite subst_term_shift_cancel.
      apply ty_var.
      * exact H.
      * assumption.
  - inversion Hlookup; subst.
    + simpl.
      rewrite subst_term_shift_one.
      apply ty_var.
      * apply wf_extend with (level := level).
        -- apply substitute_context_target_wf in Hcontext.
           exact Hcontext.
        -- exact H.
      * apply lookup_here.
    + simpl.
      rewrite subst_term_shift_one.
      rewrite substitute_term_index_shift_one.
      apply has_type_weaken_top with
          (gamma := delta)
          (level := level).
      * apply substitute_context_target_wf in Hcontext.
        exact Hcontext.
      * exact H.
      * apply IHHcontext.
        assumption.
Qed.

Example lookup_substitution_removes_nearest_variable :
  has_type []
    (subst_term (tUniverse 0) 0 (tVar 0))
    (subst_term (tUniverse 0) 0 (tUniverse 1)).
Proof.
  apply lookup_substitute with
      (gamma := [tUniverse 1])
      (index := 0).
  - apply substitute_context_here.
    + apply wf_empty.
    + apply ty_universe.
      apply wf_empty.
  - apply lookup_here.
Qed.

Lemma has_type_substitute :
  forall gamma t a,
    has_type gamma t a ->
    forall replacement cutoff delta,
      substitute_context replacement cutoff gamma delta ->
      has_type delta
        (subst_term replacement cutoff t)
        (subst_term replacement cutoff a).
Proof.
  intros gamma t a Htyping.
  induction Htyping using has_type_ind'
    with (P := fun _ _ => True).
  - exact I.
  - exact I.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_universe.
    apply substitute_context_target_wf in Hcontext.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    apply lookup_substitute with
        (gamma := gamma)
        (index := index).
    + exact Hcontext.
    + exact l.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_pi with (level_a := level_a) (level_b := level_b).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      apply substitute_context_there with (level := level_a).
      * exact Hcontext.
      * apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_lam with (level_a := level_a) (level_b := level_b).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      apply substitute_context_there with (level := level_a).
      * exact Hcontext.
      * apply IHHtyping1.
        exact Hcontext.
    + apply IHHtyping3.
      apply substitute_context_there with (level := level_a).
      * exact Hcontext.
      * apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_compose_zero.
    apply ty_app with
        (a := subst_term replacement cutoff a)
        (b := subst_term replacement (S cutoff) b).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_sigma with (level_a := level_a) (level_b := level_b).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      apply substitute_context_there with (level := level_a).
      * exact Hcontext.
      * apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_pair with (level_a := level_a) (level_b := level_b).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      apply substitute_context_there with (level := level_a).
      * exact Hcontext.
      * apply IHHtyping1.
        exact Hcontext.
    + apply IHHtyping3.
      exact Hcontext.
    + rewrite <- subst_term_compose_zero.
      apply IHHtyping4.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_fst with
        (b := subst_term replacement (S cutoff) b).
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_compose_zero.
    apply ty_snd with
        (a := subst_term replacement cutoff a)
        (b := subst_term replacement (S cutoff) b).
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_id with (level := level).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      exact Hcontext.
    + apply IHHtyping3.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_refl.
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply ty_conv with
        (a := subst_term replacement cutoff a)
        (level := level).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      exact Hcontext.
    + apply defeq_subst_term.
      exact d.
Qed.

Corollary has_type_substitute_top :
  forall gamma replacement domain t a,
    wf_context gamma ->
    has_type gamma replacement domain ->
    has_type (domain :: gamma) t a ->
    has_type gamma
      (subst_term replacement 0 t)
      (subst_term replacement 0 a).
Proof.
  intros gamma replacement domain t a Hwf Hreplacement Htyping.
  apply has_type_substitute with
      (gamma := domain :: gamma)
      (replacement := replacement)
      (cutoff := 0).
  - exact Htyping.
  - apply substitute_context_here.
    + exact Hwf.
    + exact Hreplacement.
Qed.

Example reflexivity_substitution_example :
  has_type []
    (subst_term (tUniverse 0) 0 (tRefl (tVar 0)))
    (subst_term (tUniverse 0) 0
      (tId (tUniverse 1) (tVar 0) (tVar 0))).
Proof.
  apply has_type_substitute_top with
      (domain := tUniverse 1).
  - apply wf_empty.
  - apply ty_universe.
    apply wf_empty.
  - apply ty_refl.
    apply ty_var.
    + apply wf_extend with (level := 2).
      * apply wf_empty.
      * apply ty_universe.
        apply wf_empty.
    + apply lookup_here.
Qed.
