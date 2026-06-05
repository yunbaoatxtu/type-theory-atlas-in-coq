(** Substitution for TDTT temporal parameters.

    Removing a temporal parameter substitutes an abstract time variable
    throughout the ordinary context, term, and type.  The replacement is
    required to be a well-formed temporal parameter.
 *)

From Stdlib Require Import Arith.PeanoNat Lia List.
From Atlas Require Import Syntax Ops Context DefEq Substitution UTT
  TemporalContext TDTT TDTTTemporalWeakening.

Import ListNotations.

Lemma subst_time_shift_term_commute :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall time_cutoff term_amount term_cutoff t,
      subst_time replacement time_cutoff
        (shift_term term_amount term_cutoff t) =
      shift_term term_amount term_cutoff
        (subst_time replacement time_cutoff t).
Proof.
  intros replacement_theta replacement Hreplacement.
  inversion Hreplacement; subst.
  intros time_cutoff term_amount term_cutoff t.
  revert time_cutoff term_cutoff.
  induction t; intros time_cutoff term_cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  unfold substitute_time_index.
  destruct (Nat.ltb n time_cutoff).
  - reflexivity.
  - destruct (Nat.eqb n time_cutoff); reflexivity.
Qed.

Lemma subst_time_substitute_term_index :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall time_cutoff argument term_cutoff index,
      subst_time replacement time_cutoff
        (substitute_term_index argument term_cutoff index) =
      substitute_term_index
        (subst_time replacement time_cutoff argument)
        term_cutoff
        index.
Proof.
  intros replacement_theta replacement Hreplacement
    time_cutoff argument term_cutoff index.
  unfold substitute_term_index.
  destruct (Nat.ltb index term_cutoff).
  - reflexivity.
  - destruct (Nat.eqb index term_cutoff).
    + apply subst_time_shift_term_commute with
          (replacement_theta := replacement_theta).
      exact Hreplacement.
    + reflexivity.
Qed.

Lemma subst_term_substitute_time_index :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall argument term_cutoff time_cutoff index,
      subst_term argument term_cutoff
        (substitute_time_index replacement time_cutoff index) =
      substitute_time_index replacement time_cutoff index.
Proof.
  intros replacement_theta replacement Hreplacement
    argument term_cutoff time_cutoff index.
  inversion Hreplacement; subst.
  unfold substitute_time_index.
  destruct (Nat.ltb index time_cutoff).
  - reflexivity.
  - destruct (Nat.eqb index time_cutoff); reflexivity.
Qed.

Lemma substitute_time_index_shift_depth :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall cutoff depth index,
      substitute_time_index replacement (S (cutoff + depth))
        (shift_index 1 depth index) =
      shift_time 1 depth
        (substitute_time_index replacement (cutoff + depth) index).
Proof.
  intros replacement_theta replacement Hreplacement.
  inversion Hreplacement; subst.
  intros cutoff depth subject_index.
  unfold substitute_time_index, shift_index.
  repeat
    match goal with
    | |- context [Nat.leb ?left ?right] =>
        destruct (Nat.leb left right) eqn:?
    | |- context [Nat.ltb ?left ?right] =>
        destruct (Nat.ltb left right) eqn:?
    | |- context [Nat.eqb ?left ?right] =>
        destruct (Nat.eqb left right) eqn:?
    end;
    simpl in *;
    repeat
      match goal with
      | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
      | H : Nat.leb _ _ = false |- _ => apply Nat.leb_gt in H
      | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
      | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
      end;
    try reflexivity;
    try f_equal;
    try congruence;
    try lia.
  all: unfold shift_index.
  all:
    repeat
      match goal with
      | |- context [Nat.leb ?left ?right] =>
          destruct (Nat.leb left right) eqn:?
      end;
      simpl in *;
      repeat
        match goal with
        | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
        | H : Nat.leb _ _ = false |- _ => apply Nat.leb_gt in H
        end;
      try reflexivity;
      try f_equal;
      lia.
Qed.

Lemma subst_time_shift_time_one_depth :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall cutoff depth t,
      subst_time replacement (S (cutoff + depth))
        (shift_time 1 depth t) =
      shift_time 1 depth
        (subst_time replacement (cutoff + depth) t).
Proof.
  intros replacement_theta replacement Hreplacement cutoff depth t.
  revert cutoff depth.
  induction t; intros cutoff depth; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - apply substitute_time_index_shift_depth with
        (replacement_theta := replacement_theta).
    exact Hreplacement.
  - replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    f_equal.
    apply IHt.
  - replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    f_equal.
    apply IHt.
  - replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    f_equal.
    apply IHt2.
Qed.

Corollary subst_time_shift_time_one :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall cutoff t,
      subst_time replacement (S cutoff) (shift_time 1 0 t) =
      shift_time 1 0 (subst_time replacement cutoff t).
Proof.
  intros replacement_theta replacement Hreplacement cutoff t.
  pose proof (subst_time_shift_time_one_depth
    replacement_theta replacement Hreplacement cutoff 0 t) as Hshift.
  replace (cutoff + 0) with cutoff in Hshift by lia.
  exact Hshift.
Qed.

Lemma substitute_time_index_shift_cancel :
  forall replacement cutoff index,
    substitute_time_index replacement cutoff
      (shift_index 1 cutoff index) =
    tTimeVar index.
Proof.
  intros replacement cutoff index.
  unfold shift_index, substitute_time_index.
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

Lemma subst_time_shift_cancel :
  forall replacement cutoff t,
    subst_time replacement cutoff (shift_time 1 cutoff t) = t.
Proof.
  intros replacement cutoff t.
  revert replacement cutoff.
  induction t; intros replacement cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - apply substitute_time_index_shift_cancel.
Qed.

Lemma subst_time_subst_term_commute :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall time_cutoff argument term_cutoff t,
      subst_time replacement time_cutoff
        (subst_term argument term_cutoff t) =
      subst_term
        (subst_time replacement time_cutoff argument)
        term_cutoff
        (subst_time replacement time_cutoff t).
Proof.
  intros replacement_theta replacement Hreplacement
    time_cutoff argument term_cutoff t.
  revert time_cutoff argument term_cutoff.
  induction t; intros time_cutoff argument term_cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - apply subst_time_substitute_term_index with
      (replacement_theta := replacement_theta);
    exact Hreplacement.
  - symmetry.
    apply subst_term_substitute_time_index with
        (replacement_theta := replacement_theta).
    exact Hreplacement.
  -
    rewrite (subst_time_shift_time_one
      replacement_theta replacement Hreplacement).
    reflexivity.
  - rewrite (subst_time_shift_time_one
      replacement_theta replacement Hreplacement).
    reflexivity.
  - rewrite (subst_time_shift_time_one
      replacement_theta replacement Hreplacement).
    reflexivity.
Qed.

Lemma shift_time_same_cutoff_add :
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

Lemma substitute_time_index_shift_one :
  forall replacement cutoff index,
    substitute_time_index replacement (S cutoff) (S index) =
    shift_time 1 0
      (substitute_time_index replacement cutoff index).
Proof.
  intros replacement cutoff index.
  unfold substitute_time_index.
  destruct (Nat.lt_trichotomy index cutoff) as [Hlt | [Heq | Hgt]].
  - assert (Nat.ltb index cutoff = true) as Hbelow.
    { apply Nat.ltb_lt. exact Hlt. }
    assert (Nat.ltb (S index) (S cutoff) = true) as Hbelow_succ.
    { apply Nat.ltb_lt. lia. }
    rewrite Hbelow, Hbelow_succ.
    reflexivity.
  - subst index.
    rewrite Nat.ltb_irrefl, Nat.eqb_refl.
    rewrite Nat.ltb_irrefl, Nat.eqb_refl.
    rewrite shift_time_same_cutoff_add.
    replace (1 + cutoff) with (S cutoff) by lia.
    reflexivity.
  - assert (Nat.ltb index cutoff = false) as Hbelow.
    { apply Nat.ltb_ge. lia. }
    assert (Nat.eqb index cutoff = false) as Hequal.
    { apply Nat.eqb_neq. lia. }
    assert (Nat.ltb (S index) (S cutoff) = false) as Hbelow_succ.
    { apply Nat.ltb_ge. lia. }
    assert (Nat.eqb (S index) (S cutoff) = false) as Hequal_succ.
    { apply Nat.eqb_neq. lia. }
    rewrite Hbelow, Hequal, Hbelow_succ, Hequal_succ.
    simpl.
    unfold shift_index.
    simpl.
    f_equal.
    lia.
Qed.

Lemma shift_time_prefix_add :
  forall amount prefix offset depth t,
    offset <= prefix ->
    shift_time amount (offset + depth) (shift_time prefix depth t) =
    shift_time (amount + prefix) depth t.
Proof.
  intros amount prefix offset depth t.
  revert depth.
  induction t; intros depth Hoffset; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3 by exact Hoffset;
    try reflexivity.
  - f_equal.
    apply shift_index_prefix_add.
    exact Hoffset.
  - replace (S (offset + depth)) with (offset + S depth) by lia.
    rewrite IHt by exact Hoffset.
    reflexivity.
  - replace (S (offset + depth)) with (offset + S depth) by lia.
    rewrite IHt by exact Hoffset.
    reflexivity.
  - replace (S (offset + depth)) with (offset + S depth) by lia.
    rewrite IHt2 by exact Hoffset.
    reflexivity.
Qed.

Lemma substitute_time_index_shift_prefix_depth :
  forall replacement amount cutoff depth index,
    substitute_time_index replacement (amount + cutoff + depth)
      (shift_index amount depth index) =
    shift_time amount depth
      (substitute_time_index replacement (cutoff + depth) index).
Proof.
  intros replacement amount cutoff depth index.
  unfold shift_index at 1.
  destruct (Nat.leb depth index) eqn:Hdepth.
  - apply Nat.leb_le in Hdepth.
    unfold substitute_time_index.
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
        pose proof (shift_time_prefix_add
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
    unfold substitute_time_index.
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

Lemma subst_time_shift_prefix_depth :
  forall replacement amount cutoff depth t,
    subst_time replacement (amount + cutoff + depth)
      (shift_time amount depth t) =
    shift_time amount depth
      (subst_time replacement (cutoff + depth) t).
Proof.
  intros replacement amount cutoff depth t.
  revert replacement depth.
  induction t; intros replacement depth; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - apply substitute_time_index_shift_prefix_depth.
  - replace (S (amount + cutoff + depth))
      with (amount + cutoff + S depth) by lia.
    replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite (IHt replacement (S depth)).
    reflexivity.
  - replace (S (amount + cutoff + depth))
      with (amount + cutoff + S depth) by lia.
    replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite (IHt replacement (S depth)).
    reflexivity.
  - replace (S (amount + cutoff + depth))
      with (amount + cutoff + S depth) by lia.
    replace (S (cutoff + depth)) with (cutoff + S depth) by lia.
    rewrite (IHt2 replacement (S depth)).
    reflexivity.
Qed.

Corollary subst_time_shift_prefix :
  forall replacement amount cutoff t,
    subst_time replacement (amount + cutoff) (shift_time amount 0 t) =
    shift_time amount 0 (subst_time replacement cutoff t).
Proof.
  intros replacement amount cutoff t.
  pose proof (subst_time_shift_prefix_depth
    replacement amount cutoff 0 t) as Hprefix.
  replace (amount + cutoff + 0) with (amount + cutoff) in Hprefix by lia.
  replace (cutoff + 0) with cutoff in Hprefix by lia.
  exact Hprefix.
Qed.

Lemma subst_time_shift_prefix_drop :
  forall replacement cutoff extra t,
    subst_time replacement cutoff
      (shift_time (S (cutoff + extra)) 0 t) =
    shift_time (cutoff + extra) 0 t.
Proof.
  intros replacement cutoff extra t.
  pose proof (subst_time_shift_prefix
    replacement cutoff 0 (shift_time (S extra) 0 t)) as Hprefix.
  replace (cutoff + 0) with cutoff in Hprefix by lia.
  rewrite shift_time_same_cutoff_add in Hprefix.
  replace (cutoff + S extra) with (S (cutoff + extra)) in Hprefix by lia.
  pose proof (subst_time_shift_cancel
    replacement 0 (shift_time extra 0 t)) as Hcancel.
  rewrite shift_time_same_cutoff_add in Hcancel.
  replace (1 + extra) with (S extra) in Hcancel by lia.
  rewrite Hcancel in Hprefix.
  rewrite shift_time_same_cutoff_add in Hprefix.
  exact Hprefix.
Qed.

Lemma substitute_time_index_compose :
  forall replacement argument outer_cutoff inner_cutoff index,
    subst_time replacement (inner_cutoff + outer_cutoff)
      (substitute_time_index argument inner_cutoff index) =
    subst_time
      (subst_time replacement outer_cutoff argument)
      inner_cutoff
      (substitute_time_index replacement
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
    cbn [subst_time].
    unfold substitute_time_index.
    rewrite Hinner, Houter_deeper.
    cbn [subst_time].
    unfold substitute_time_index.
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
    cbn [subst_time].
    unfold substitute_time_index.
    rewrite Hinner_lt, Hinner_eq, Houter_deeper.
    cbn [subst_time].
    unfold substitute_time_index.
    rewrite Hinner_lt, Hinner_eq.
    apply subst_time_shift_prefix.
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
      cbn [subst_time].
      unfold substitute_time_index.
      rewrite Hinner_lt, Hinner_eq, Houter_deeper.
      cbn [subst_time].
      unfold substitute_time_index.
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
      cbn [subst_time].
      unfold substitute_time_index.
      rewrite Hinner_lt, Hinner_eq, Houter_lt, Houter_eq.
      cbn [subst_time].
      unfold substitute_time_index.
      replace (Nat.pred (S (inner_cutoff + outer_cutoff)))
        with (inner_cutoff + outer_cutoff) by reflexivity.
      rewrite Hleft_lt, Hleft_eq.
      symmetry.
      apply subst_time_shift_prefix_drop.
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
      cbn [subst_time].
      unfold substitute_time_index.
      rewrite Hinner_lt, Hinner_eq, Houter_deeper_lt, Houter_deeper_eq.
      cbn [subst_time].
      unfold substitute_time_index.
      rewrite Houter_lt, Houter_eq, Hinner_pred_lt, Hinner_pred_eq.
      reflexivity.
Qed.

Lemma subst_time_compose :
  forall replacement argument outer_cutoff inner_cutoff t,
    subst_time replacement (inner_cutoff + outer_cutoff)
      (subst_time argument inner_cutoff t) =
    subst_time
      (subst_time replacement outer_cutoff argument)
      inner_cutoff
      (subst_time replacement (S (inner_cutoff + outer_cutoff)) t).
Proof.
  intros replacement argument outer_cutoff inner_cutoff t.
  revert replacement argument inner_cutoff.
  induction t; intros replacement argument inner_cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - apply substitute_time_index_compose.
  - replace (S (inner_cutoff + outer_cutoff))
      with (S inner_cutoff + outer_cutoff) by lia.
    rewrite (IHt replacement argument (S inner_cutoff)).
    reflexivity.
  - replace (S (inner_cutoff + outer_cutoff))
      with (S inner_cutoff + outer_cutoff) by lia.
    rewrite (IHt replacement argument (S inner_cutoff)).
    reflexivity.
  - replace (S (inner_cutoff + outer_cutoff))
      with (S inner_cutoff + outer_cutoff) by lia.
    rewrite (IHt2 replacement argument (S inner_cutoff)).
    reflexivity.
Qed.

Corollary subst_time_compose_zero :
  forall replacement argument cutoff t,
    subst_time replacement cutoff (subst_time argument 0 t) =
    subst_time
      (subst_time replacement cutoff argument)
      0
      (subst_time replacement (S cutoff) t).
Proof.
  intros replacement argument cutoff t.
  pose proof (subst_time_compose replacement argument cutoff 0 t)
    as Hcompose.
  replace (0 + cutoff) with cutoff in Hcompose by lia.
  exact Hcompose.
Qed.

Lemma defeq_subst_time :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall t u,
      defeq t u ->
      forall cutoff,
        defeq
          (subst_time replacement cutoff t)
          (subst_time replacement cutoff u).
Proof.
  intros replacement_theta replacement Hreplacement t u Heq.
  induction Heq; intros cutoff; simpl.
  - apply de_refl.
  - apply de_sym.
    apply IHHeq.
  - eapply de_trans.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite (subst_time_subst_term_commute
      replacement_theta replacement Hreplacement).
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
  - rewrite (subst_time_subst_term_commute
      replacement_theta replacement Hreplacement).
    apply de_fix_unfold.
  - apply de_fix.
    apply IHHeq.
  - apply de_later_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_next_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite (subst_time_subst_term_commute
      replacement_theta replacement Hreplacement).
    apply de_fix_at_unfold.
  - apply de_fix_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite subst_time_compose_zero.
    inversion Hreplacement; subst.
    cbn [subst_time].
    unfold substitute_time_index.
    repeat
      match goal with
      | |- context [Nat.ltb ?left ?right] =>
          destruct (Nat.ltb left right) eqn:?
      | |- context [Nat.eqb ?left ?right] =>
          destruct (Nat.eqb left right) eqn:?
      end;
      apply de_clock_beta.
  - apply de_clock_pi.
    apply IHHeq.
  - apply de_clock_lam.
    apply IHHeq.
  - apply de_clock_app.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite subst_time_compose_zero.
    inversion Hreplacement; subst.
    cbn [subst_time].
    unfold substitute_time_index.
    repeat
      match goal with
      | |- context [Nat.ltb ?left ?right] =>
          destruct (Nat.ltb left right) eqn:?
      | |- context [Nat.eqb ?left ?right] =>
          destruct (Nat.eqb left right) eqn:?
      end;
      apply de_delayed_subst_compute.
  - apply de_delayed_subst.
    + apply IHHeq1.
    + apply IHHeq2.
Qed.

Inductive temporal_substitute_context (replacement : term) :
    nat -> temporal_context -> temporal_context -> Prop :=
| temporal_substitute_here :
    forall theta,
      temporal_wf theta replacement ->
      temporal_substitute_context replacement 0 (tc_extend theta) theta
| temporal_substitute_there :
    forall cutoff theta delta,
      temporal_substitute_context replacement cutoff theta delta ->
      temporal_substitute_context replacement (S cutoff)
        (tc_extend theta)
        (tc_extend delta).

Lemma temporal_substitute_context_replacement_wf :
  forall replacement cutoff theta delta,
    temporal_substitute_context replacement cutoff theta delta ->
    exists replacement_theta,
      temporal_wf replacement_theta replacement.
Proof.
  intros replacement cutoff theta delta Hcontext.
  induction Hcontext.
  - exists theta.
    exact H.
  - exact IHHcontext.
Qed.

Lemma temporal_lookup_substitute :
  forall replacement cutoff theta delta index,
    temporal_substitute_context replacement cutoff theta delta ->
    temporal_lookup theta index ->
    temporal_wf delta
      (subst_time replacement cutoff (tTimeVar index)).
Proof.
  intros replacement cutoff theta delta index Hcontext.
  revert index.
  induction Hcontext; intros index Hlookup.
  - inversion Hlookup; subst.
    + rewrite subst_time_var_zero.
      exact H.
    + simpl.
      apply temporal_wf_var.
      assumption.
  - inversion Hlookup; subst.
    + simpl.
      unfold substitute_time_index.
      simpl.
      apply temporal_wf_var.
      apply temporal_lookup_here.
    + simpl.
      rewrite substitute_time_index_shift_one.
      apply temporal_wf_weaken_top.
      apply IHHcontext.
      assumption.
Qed.

Lemma lookup_subst_time_context :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall cutoff gamma index a,
      lookup gamma index a ->
      lookup (subst_time_context replacement cutoff gamma)
        index
        (subst_time replacement cutoff a).
Proof.
  intros replacement_theta replacement Hreplacement
    cutoff gamma index a Hlookup.
  induction Hlookup; simpl.
  - rewrite (subst_time_shift_term_commute
      replacement_theta replacement Hreplacement).
    apply lookup_here.
  - rewrite (subst_time_shift_term_commute
      replacement_theta replacement Hreplacement).
    apply lookup_there.
      exact IHHlookup.
Qed.

Lemma subst_time_context_shift_time_one :
  forall replacement_theta replacement,
    temporal_wf replacement_theta replacement ->
    forall cutoff gamma,
      subst_time_context replacement (S cutoff)
        (shift_time_context 1 0 gamma) =
      shift_time_context 1 0
        (subst_time_context replacement cutoff gamma).
Proof.
  intros replacement_theta replacement Hreplacement cutoff gamma.
  induction gamma as [| a gamma IHgamma]; simpl.
  - reflexivity.
  - rewrite (subst_time_shift_time_one
      replacement_theta replacement Hreplacement).
    rewrite IHgamma.
    reflexivity.
Qed.

Theorem tdtt_typing_substitute_time_general :
  (forall theta gamma,
      tdtt_wf_context theta gamma ->
      forall replacement cutoff delta,
        temporal_substitute_context replacement cutoff theta delta ->
        tdtt_wf_context delta
          (subst_time_context replacement cutoff gamma)) /\
  (forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      forall replacement cutoff delta,
        temporal_substitute_context replacement cutoff theta delta ->
        tdtt_has_type delta
          (subst_time_context replacement cutoff gamma)
          (subst_time replacement cutoff t)
          (subst_time replacement cutoff a)).
Proof.
  apply tdtt_typing_mutind
    with
      (P := fun theta gamma _ =>
        forall replacement cutoff delta,
          temporal_substitute_context replacement cutoff theta delta ->
          tdtt_wf_context delta
            (subst_time_context replacement cutoff gamma))
      (P0 := fun theta gamma t a _ =>
        forall replacement cutoff delta,
          temporal_substitute_context replacement cutoff theta delta ->
          tdtt_has_type delta
            (subst_time_context replacement cutoff gamma)
            (subst_time replacement cutoff t)
            (subst_time replacement cutoff a)).
  - intros theta replacement cutoff delta Hcontext.
    apply tdtt_wf_empty.
  - intros theta gamma a sort _ Hgamma _ Ha replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_wf_extend with (sort := sort).
    + apply Hgamma.
      exact Hcontext.
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
  - intros theta gamma _ Hgamma replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_prop.
    apply Hgamma.
    exact Hcontext.
  - intros theta gamma level _ Hgamma replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_universe.
    apply Hgamma.
    exact Hcontext.
  - intros theta gamma index a _ Hgamma Hlookup replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_var.
    + apply Hgamma.
      exact Hcontext.
    + destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      apply lookup_subst_time_context with
          (replacement_theta := replacement_theta).
      * exact Hreplacement.
      * exact Hlookup.
  - intros theta gamma a b domain_sort codomain_sort
      _ Ha _ Hb replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_time_utt_sort_term.
    apply tdtt_ty_pi with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
    + specialize (Hb replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Hb.
      exact Hb.
  - intros theta gamma a body b domain_sort codomain_sort
      _ Ha _ Hb _ Hbody replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_lam with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
    + specialize (Hb replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Hb.
      exact Hb.
    + apply Hbody.
      exact Hcontext.
  - intros theta gamma f argument a b
      _ Hf _ Hargument replacement cutoff delta Hcontext.
    simpl.
    destruct (temporal_substitute_context_replacement_wf
      replacement cutoff theta delta Hcontext)
      as [replacement_theta Hreplacement].
    rewrite (subst_time_subst_term_commute
      replacement_theta replacement Hreplacement).
    apply tdtt_ty_app with
        (a := subst_time replacement cutoff a)
        (b := subst_time replacement cutoff b).
    + apply Hf.
      exact Hcontext.
    + apply Hargument.
      exact Hcontext.
  - intros theta gamma a b domain_sort level_b
      _ Ha _ Hb replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_sigma with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
    + apply Hb.
      exact Hcontext.
  - intros theta gamma a b first second domain_sort level_b
      _ Ha _ Hb _ Hfirst _ Hsecond replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_pair with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
    + apply Hb.
      exact Hcontext.
    + apply Hfirst.
      exact Hcontext.
    + specialize (Hsecond replacement cutoff delta Hcontext).
      destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      rewrite (subst_time_subst_term_commute
        replacement_theta replacement Hreplacement) in Hsecond.
      exact Hsecond.
  - intros theta gamma pair a b _ Hpair replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_fst with (b := subst_time replacement cutoff b).
    apply Hpair.
    exact Hcontext.
  - intros theta gamma pair a b _ Hpair replacement cutoff delta Hcontext.
    simpl.
    destruct (temporal_substitute_context_replacement_wf
      replacement cutoff theta delta Hcontext)
      as [replacement_theta Hreplacement].
    rewrite (subst_time_subst_term_commute
      replacement_theta replacement Hreplacement).
    apply tdtt_ty_snd with
        (a := subst_time replacement cutoff a)
        (b := subst_time replacement cutoff b).
    apply Hpair.
    exact Hcontext.
  - intros theta gamma a x y level
      _ Ha _ Hx _ Hy replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_id with (level := level).
    + apply Ha.
      exact Hcontext.
    + apply Hx.
      exact Hcontext.
    + apply Hy.
      exact Hcontext.
  - intros theta gamma a x _ Hx replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_refl.
    apply Hx.
    exact Hcontext.
  - intros theta gamma t a b sort _ Ht _ Hb Heq replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_conv with
        (a := subst_time replacement cutoff a)
        (sort := sort).
    + apply Ht.
      exact Hcontext.
    + specialize (Hb replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Hb.
      exact Hb.
    + destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      apply defeq_subst_time with
          (replacement_theta := replacement_theta).
      * exact Hreplacement.
      * exact Heq.
  - intros theta gamma proposition level
      _ Hproposition replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_prop_lift.
    apply Hproposition.
    exact Hcontext.
  - intros theta gamma a lower upper _ Ha Hle replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_type_lift with (lower := lower).
    + apply Ha.
      exact Hcontext.
    + exact Hle.
  - intros theta gamma a time sort _ Ha Htime replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_time_utt_sort_term.
    apply tdtt_ty_at with (sort := sort).
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
    + inversion Htime; subst.
      apply temporal_lookup_substitute with
          (theta := theta)
          (index := index).
      * exact Hcontext.
      * assumption.
  - intros theta gamma a sort _ Ha replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_time_utt_sort_term.
    apply tdtt_ty_later with (sort := sort).
    specialize (Ha replacement cutoff delta Hcontext).
    + rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
  - intros theta gamma t a _ Ht replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_next.
    apply Ht.
    exact Hcontext.
  - intros theta gamma a body sort _ Ha _ Hbody replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_fix with (sort := sort).
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
    + specialize (Hbody replacement cutoff delta Hcontext).
      destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      rewrite (subst_time_shift_term_commute
        replacement_theta replacement Hreplacement) in Hbody.
      exact Hbody.
  - intros theta gamma clock a sort Hclock _ Ha replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_time_utt_sort_term.
    apply tdtt_ty_later_at with (sort := sort).
    + inversion Hclock; subst.
      apply temporal_lookup_substitute with
          (theta := theta)
          (index := index).
      * exact Hcontext.
      * assumption.
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
  - intros theta gamma clock t a Hclock _ Ht replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_next_at.
    + inversion Hclock; subst.
      apply temporal_lookup_substitute with
          (theta := theta)
          (index := index).
      * exact Hcontext.
      * assumption.
    + apply Ht.
      exact Hcontext.
  - intros theta gamma clock a body sort Hclock
      _ Ha _ Hbody replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_fix_at with (sort := sort).
    + inversion Hclock; subst.
      apply temporal_lookup_substitute with
          (theta := theta)
          (index := index).
      * exact Hcontext.
      * assumption.
    + specialize (Ha replacement cutoff delta Hcontext).
      rewrite subst_time_utt_sort_term in Ha.
      exact Ha.
    + specialize (Hbody replacement cutoff delta Hcontext).
      destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      rewrite (subst_time_shift_term_commute
        replacement_theta replacement Hreplacement) in Hbody.
      exact Hbody.
  - intros theta gamma a sort _ Hgamma _ Ha replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_time_utt_sort_term.
    apply tdtt_ty_clock_pi with (sort := sort).
    + apply Hgamma.
      exact Hcontext.
    + destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      rewrite <- (subst_time_context_shift_time_one
        replacement_theta replacement Hreplacement).
      rewrite <- (subst_time_utt_sort_term replacement (S cutoff) sort).
      apply Ha.
      apply temporal_substitute_there.
      exact Hcontext.
  - intros theta gamma body a sort _ Hgamma _ Ha _ Hbody
      replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_clock_lam with (sort := sort).
    + apply Hgamma.
      exact Hcontext.
    + destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      rewrite <- (subst_time_context_shift_time_one
        replacement_theta replacement Hreplacement).
      rewrite <- (subst_time_utt_sort_term replacement (S cutoff) sort).
      apply Ha.
      apply temporal_substitute_there.
      exact Hcontext.
    + destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      rewrite <- (subst_time_context_shift_time_one
        replacement_theta replacement Hreplacement).
      apply Hbody.
      apply temporal_substitute_there.
      exact Hcontext.
  - intros theta gamma f clock a _ Hf Hclock replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_time_compose_zero.
    apply tdtt_ty_clock_app with
        (a := subst_time replacement (S cutoff) a).
    + apply Hf.
      exact Hcontext.
    + inversion Hclock; subst.
      apply temporal_lookup_substitute with
          (theta := theta)
          (index := index).
      * exact Hcontext.
      * assumption.
  - intros theta gamma clock body a _ Hgamma Hclock _ Hbody
      replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_time_compose_zero.
    apply tdtt_ty_delayed_subst.
    + apply Hgamma.
      exact Hcontext.
    + inversion Hclock; subst.
      apply temporal_lookup_substitute with
          (theta := theta)
          (index := index).
      * exact Hcontext.
      * assumption.
    + destruct (temporal_substitute_context_replacement_wf
        replacement cutoff theta delta Hcontext)
        as [replacement_theta Hreplacement].
      rewrite <- (subst_time_context_shift_time_one
        replacement_theta replacement Hreplacement).
      apply Hbody.
      apply temporal_substitute_there.
      exact Hcontext.
Qed.

Theorem tdtt_typing_substitute_time :
  forall replacement cutoff theta delta,
    temporal_substitute_context replacement cutoff theta delta ->
    (forall gamma,
        tdtt_wf_context theta gamma ->
        tdtt_wf_context delta
          (subst_time_context replacement cutoff gamma)) /\
    (forall gamma t a,
        tdtt_has_type theta gamma t a ->
        tdtt_has_type delta
          (subst_time_context replacement cutoff gamma)
          (subst_time replacement cutoff t)
          (subst_time replacement cutoff a)).
Proof.
  intros replacement cutoff theta delta Hcontext.
  split.
  - intros gamma Hgamma.
    apply tdtt_typing_substitute_time_general with (theta := theta).
    + exact Hgamma.
    + exact Hcontext.
  - intros gamma t a Htyping.
    apply tdtt_typing_substitute_time_general with (theta := theta).
    + exact Htyping.
    + exact Hcontext.
Qed.

Corollary tdtt_context_substitute_time_top :
  forall theta replacement gamma,
    temporal_wf theta replacement ->
    tdtt_wf_context (tc_extend theta) gamma ->
    tdtt_wf_context theta (subst_time_context replacement 0 gamma).
Proof.
  intros theta replacement gamma Hreplacement Hgamma.
  apply (tdtt_typing_substitute_time
    replacement 0 (tc_extend theta) theta).
  - apply temporal_substitute_here.
    exact Hreplacement.
  - exact Hgamma.
Qed.

Corollary tdtt_has_type_substitute_time_top :
  forall theta replacement gamma t a,
    temporal_wf theta replacement ->
    tdtt_has_type (tc_extend theta) gamma t a ->
    tdtt_has_type theta
      (subst_time_context replacement 0 gamma)
      (subst_time replacement 0 t)
      (subst_time replacement 0 a).
Proof.
  intros theta replacement gamma t a Hreplacement Htyping.
  apply (tdtt_typing_substitute_time
    replacement 0 (tc_extend theta) theta).
  - apply temporal_substitute_here.
    exact Hreplacement.
  - exact Htyping.
Qed.

Example tdtt_at_typing_substitutes_current_time :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tAt tProp (tTimeVar 0))
    (tUniverse 0).
Proof.
  change (tdtt_has_type
    (tc_extend tc_empty)
    (subst_time_context (tTimeVar 0) 0 [])
    (subst_time (tTimeVar 0) 0 (tAt tProp (tTimeVar 0)))
    (subst_time (tTimeVar 0) 0 (tUniverse 0))).
  apply tdtt_has_type_substitute_time_top.
  - apply temporal_wf_var.
    apply temporal_lookup_here.
  - apply tdtt_ty_at with (sort := usType 0).
    + apply tdtt_ty_prop.
      apply tdtt_wf_empty.
    + apply temporal_wf_var.
      apply temporal_lookup_here.
Qed.
