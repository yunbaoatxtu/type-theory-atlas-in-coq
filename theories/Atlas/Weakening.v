(** Structural weakening for ordinary variable contexts.

    Inserting a declaration below [cutoff] existing declarations shifts the
    declarations above it.  Lookup weakening is the variable case needed by
    the typing weakening theorem.
 *)

From Stdlib Require Import Arith.PeanoNat Lia List.
From Atlas Require Import Syntax Ops Context DefEq MLTT.

Import ListNotations.

Lemma shift_index_one_commute :
  forall lower upper index,
    lower <= upper ->
    shift_index 1 (S upper) (shift_index 1 lower index) =
    shift_index 1 lower (shift_index 1 upper index).
Proof.
  intros lower upper index Hle.
  unfold shift_index.
  destruct (Nat.leb lower index) eqn:Hlower.
  - apply Nat.leb_le in Hlower.
    destruct (Nat.leb upper index) eqn:Hupper.
    + apply Nat.leb_le in Hupper.
      assert (Nat.leb (S upper) (1 + index) = true) as Hleft.
      { apply Nat.leb_le. lia. }
      assert (Nat.leb lower (1 + index) = true) as Hright.
      { apply Nat.leb_le. lia. }
      rewrite Hleft, Hright.
      lia.
    + apply Nat.leb_gt in Hupper.
      assert (Nat.leb (S upper) (1 + index) = false) as Hleft.
      { apply Nat.leb_gt. lia. }
      assert (Nat.leb lower index = true) as Hright.
      { apply Nat.leb_le. lia. }
      rewrite Hleft, Hright.
      lia.
  - apply Nat.leb_gt in Hlower.
    assert (Nat.leb upper index = false) as Hupper.
    { apply Nat.leb_gt. lia. }
    assert (Nat.leb (S upper) index = false) as Hleft.
    { apply Nat.leb_gt. lia. }
    assert (Nat.leb lower index = false) as Hright.
    { apply Nat.leb_gt. lia. }
    rewrite Hupper, Hleft, Hright.
    reflexivity.
Qed.

Lemma shift_term_one_commute :
  forall lower upper t,
    lower <= upper ->
    shift_term 1 (S upper) (shift_term 1 lower t) =
    shift_term 1 lower (shift_term 1 upper t).
Proof.
  intros lower upper t.
  revert lower upper.
  induction t; intros lower upper Hle; simpl.
  - f_equal.
    apply shift_index_one_commute.
    exact Hle.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by lia.
    reflexivity.
  - rewrite IHt by lia.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by lia.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    rewrite IHt3 by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt by lia.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by lia.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
Qed.

Lemma shift_term_compose :
  forall amount_lower amount_upper lower upper t,
    lower <= upper ->
    shift_term amount_upper (amount_lower + upper)
      (shift_term amount_lower lower t) =
    shift_term amount_lower lower
      (shift_term amount_upper upper t).
Proof.
  intros amount_lower amount_upper lower upper t.
  revert lower upper.
  induction t; intros lower upper Hle; simpl.
  - f_equal.
    apply shift_index_compose.
    exact Hle.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite <- Nat.add_succ_r.
    rewrite IHt2 by lia.
    reflexivity.
  - rewrite <- Nat.add_succ_r.
    rewrite IHt by lia.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite <- Nat.add_succ_r.
    rewrite IHt2 by lia.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    rewrite IHt3 by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite <- Nat.add_succ_r.
    rewrite IHt by lia.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite <- Nat.add_succ_r.
    rewrite IHt2 by lia.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
  - rewrite IHt1 by exact Hle.
    rewrite IHt2 by exact Hle.
    reflexivity.
Qed.

Lemma shift_index_below :
  forall amount cutoff index,
    index < cutoff ->
    shift_index amount cutoff index = index.
Proof.
  intros amount cutoff index Hlt.
  unfold shift_index.
  assert (Nat.leb cutoff index = false) as Hbelow.
  { apply Nat.leb_gt. lia. }
  rewrite Hbelow.
  reflexivity.
Qed.

Lemma shift_index_not_decrease :
  forall amount cutoff index,
    index <= shift_index amount cutoff index.
Proof.
  intros amount cutoff index.
  unfold shift_index.
  destruct (Nat.leb cutoff index); lia.
Qed.

Lemma shift_index_pred_commute :
  forall cutoff index,
    0 < index ->
    shift_index 1 cutoff (Nat.pred index) =
    Nat.pred (shift_index 1 (S cutoff) index).
Proof.
  intros cutoff [| index] Hpositive.
  - lia.
  - unfold shift_index.
    simpl.
    destruct (Nat.leb cutoff index); reflexivity.
Qed.

Lemma shift_substitute_term_index :
  forall replacement substitution_cutoff weakening_cutoff index,
    shift_term 1 (substitution_cutoff + weakening_cutoff)
      (substitute_term_index replacement substitution_cutoff index) =
    substitute_term_index
      (shift_term 1 weakening_cutoff replacement)
      substitution_cutoff
      (shift_index 1 (S (substitution_cutoff + weakening_cutoff)) index).
Proof.
  intros replacement substitution_cutoff weakening_cutoff index.
  unfold substitute_term_index.
  destruct (Nat.ltb index substitution_cutoff) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    assert (shift_index 1 (substitution_cutoff + weakening_cutoff) index =
      index) as Hshift.
    { apply shift_index_below. lia. }
    assert (shift_index 1 (S (substitution_cutoff + weakening_cutoff)) index =
      index) as Hshift_deeper.
    { apply shift_index_below. lia. }
    simpl.
    rewrite Hshift, Hshift_deeper.
    apply Nat.ltb_lt in Hlt.
    rewrite Hlt.
    reflexivity.
  - destruct (Nat.eqb index substitution_cutoff) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      subst index.
      assert (shift_index 1 (S (substitution_cutoff + weakening_cutoff))
        substitution_cutoff = substitution_cutoff) as Hshift_deeper.
      { apply shift_index_below. lia. }
      simpl.
      rewrite Hshift_deeper, Nat.ltb_irrefl, Nat.eqb_refl.
      apply shift_term_compose.
      lia.
    + apply Nat.ltb_ge in Hlt.
      apply Nat.eqb_neq in Heq.
      assert (substitution_cutoff < index) as Hgt by lia.
      assert (substitution_cutoff <
        shift_index 1 (S (substitution_cutoff + weakening_cutoff)) index)
        as Hshift_gt.
      { eapply Nat.lt_le_trans.
        - exact Hgt.
        - apply shift_index_not_decrease. }
      assert (Nat.ltb
        (shift_index 1 (S (substitution_cutoff + weakening_cutoff)) index)
        substitution_cutoff = false) as Hlt_shifted.
      { apply Nat.ltb_ge. lia. }
      assert (Nat.eqb
        (shift_index 1 (S (substitution_cutoff + weakening_cutoff)) index)
        substitution_cutoff = false) as Heq_shifted.
      { apply Nat.eqb_neq. lia. }
      simpl.
      rewrite Hlt_shifted, Heq_shifted.
      f_equal.
      apply shift_index_pred_commute.
      lia.
Qed.

Lemma shift_term_subst_commute :
  forall replacement substitution_cutoff weakening_cutoff t,
    shift_term 1 (substitution_cutoff + weakening_cutoff)
      (subst_term replacement substitution_cutoff t) =
    subst_term
      (shift_term 1 weakening_cutoff replacement)
      substitution_cutoff
      (shift_term 1 (S (substitution_cutoff + weakening_cutoff)) t).
Proof.
  intros replacement substitution_cutoff weakening_cutoff t.
  revert replacement substitution_cutoff.
  induction t; intros replacement substitution_cutoff; simpl.
  - apply shift_substitute_term_index.
  - reflexivity.
  - reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff).
    replace (S (substitution_cutoff + weakening_cutoff))
      with (S substitution_cutoff + weakening_cutoff) by lia.
    rewrite (IHt2 replacement (S substitution_cutoff)).
    reflexivity.
  - replace (S (substitution_cutoff + weakening_cutoff))
      with (S substitution_cutoff + weakening_cutoff) by lia.
    rewrite (IHt replacement (S substitution_cutoff)).
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff),
      (IHt2 replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff).
    replace (S (substitution_cutoff + weakening_cutoff))
      with (S substitution_cutoff + weakening_cutoff) by lia.
    rewrite (IHt2 replacement (S substitution_cutoff)).
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff),
      (IHt2 replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff),
      (IHt2 replacement substitution_cutoff),
      (IHt3 replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt replacement substitution_cutoff).
    reflexivity.
  - reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff),
      (IHt2 replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt replacement substitution_cutoff).
    reflexivity.
  - replace (S (substitution_cutoff + weakening_cutoff))
      with (S substitution_cutoff + weakening_cutoff) by lia.
    rewrite (IHt replacement (S substitution_cutoff)).
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff),
      (IHt2 replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff),
      (IHt2 replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff).
    replace (S (substitution_cutoff + weakening_cutoff))
      with (S substitution_cutoff + weakening_cutoff) by lia.
    rewrite (IHt2 replacement (S substitution_cutoff)).
    reflexivity.
  - rewrite (IHt (shift_time 1 0 replacement) substitution_cutoff).
    rewrite shift_time_shift_term_commute.
    reflexivity.
  - rewrite (IHt (shift_time 1 0 replacement) substitution_cutoff).
    rewrite shift_time_shift_term_commute.
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff),
      (IHt2 replacement substitution_cutoff).
    reflexivity.
  - rewrite (IHt1 replacement substitution_cutoff).
    rewrite (IHt2 (shift_time 1 0 replacement) substitution_cutoff).
    rewrite shift_time_shift_term_commute.
    reflexivity.
Qed.

Corollary shift_term_subst_zero :
  forall replacement weakening_cutoff t,
    shift_term 1 weakening_cutoff (subst_term replacement 0 t) =
    subst_term
      (shift_term 1 weakening_cutoff replacement)
      0
      (shift_term 1 (S weakening_cutoff) t).
Proof.
  intros replacement weakening_cutoff t.
  pose proof (shift_term_subst_commute
    replacement 0 weakening_cutoff t) as Hcommute.
  replace (0 + weakening_cutoff) with weakening_cutoff in Hcommute by lia.
  exact Hcommute.
Qed.

Lemma shift_term_subst_time_var_commute :
  forall amount term_cutoff clock_index time_cutoff t,
    shift_term amount term_cutoff
      (subst_time (tTimeVar clock_index) time_cutoff t) =
    subst_time
      (tTimeVar clock_index)
      time_cutoff
      (shift_term amount term_cutoff t).
Proof.
  intros amount term_cutoff clock_index time_cutoff t.
  revert time_cutoff term_cutoff.
  induction t; intros time_cutoff term_cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  unfold substitute_time_index.
  repeat
    match goal with
    | |- context [Nat.ltb ?left ?right] =>
        destruct (Nat.ltb left right) eqn:?
    | |- context [Nat.eqb ?left ?right] =>
        destruct (Nat.eqb left right) eqn:?
    end;
    reflexivity.
Qed.

Lemma defeq_shift_term :
  forall t u,
    defeq t u ->
    forall cutoff,
      defeq (shift_term 1 cutoff t) (shift_term 1 cutoff u).
Proof.
  intros t u Heq.
  induction Heq; intros cutoff; simpl.
  - apply de_refl.
  - apply de_sym.
    apply IHHeq.
  - eapply de_trans.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite shift_term_subst_zero.
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
  - rewrite shift_term_subst_zero.
    apply de_fix_unfold.
  - apply de_fix.
    apply IHHeq.
  - apply de_later_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_next_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite shift_term_subst_zero.
    apply de_fix_at_unfold.
  - apply de_fix_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite shift_term_subst_time_var_commute.
    apply de_clock_beta.
  - apply de_clock_pi.
    apply IHHeq.
  - apply de_clock_lam.
    apply IHHeq.
  - apply de_clock_app.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite shift_term_subst_time_var_commute.
    apply de_delayed_subst_compute.
  - apply de_delayed_subst.
    + apply IHHeq1.
    + apply IHHeq2.
Qed.

Inductive insert_context : nat -> term -> context -> context -> Prop :=
| insert_here :
    forall gamma inserted,
      insert_context 0 inserted gamma (inserted :: gamma)
| insert_there :
    forall cutoff inserted gamma delta a,
      insert_context cutoff inserted gamma delta ->
      insert_context (S cutoff) inserted (a :: gamma)
        (shift_term 1 cutoff a :: delta).

Lemma shift_index_one_zero :
  forall index,
    shift_index 1 0 index = S index.
Proof.
  intros index.
  unfold shift_index.
  simpl.
  lia.
Qed.

Lemma shift_index_one_succ :
  forall cutoff index,
    shift_index 1 (S cutoff) (S index) =
    S (shift_index 1 cutoff index).
Proof.
  intros cutoff index.
  unfold shift_index.
  simpl.
  destruct (Nat.leb cutoff index); lia.
Qed.

Lemma lookup_weaken :
  forall cutoff inserted gamma delta index a,
    insert_context cutoff inserted gamma delta ->
    lookup gamma index a ->
    lookup delta
      (shift_index 1 cutoff index)
      (shift_term 1 cutoff a).
Proof.
  intros cutoff inserted gamma delta index a Hinsert.
  revert index a.
  induction Hinsert; intros index b Hlookup.
  - rewrite shift_index_one_zero.
    apply lookup_there.
    exact Hlookup.
  - inversion Hlookup; subst.
    + simpl.
      rewrite shift_term_one_commute by lia.
      apply lookup_here.
    + rewrite shift_index_one_succ.
      rewrite shift_term_one_commute by lia.
      apply lookup_there.
      apply IHHinsert.
      assumption.
Qed.

Example insert_below_nearest_declaration :
  insert_context 1
    (tUniverse 0)
    [tUniverse 1]
    [tUniverse 1; tUniverse 0].
Proof.
  change (insert_context 1
    (tUniverse 0)
    [tUniverse 1]
    [shift_term 1 0 (tUniverse 1); tUniverse 0]).
  apply insert_there.
  apply insert_here.
Qed.

Example lookup_survives_top_insertion :
  lookup [tUniverse 0; tUniverse 1] 1 (tUniverse 1) ->
  lookup [tUniverse 2; tUniverse 0; tUniverse 1] 2 (tUniverse 1).
Proof.
  intros Hlookup.
  change (lookup [tUniverse 2; tUniverse 0; tUniverse 1]
    (shift_index 1 0 1)
    (shift_term 1 0 (tUniverse 1))).
  apply lookup_weaken with
      (inserted := tUniverse 2)
      (gamma := [tUniverse 0; tUniverse 1]).
  - apply insert_here.
  - exact Hlookup.
Qed.

Lemma has_type_weaken :
  forall gamma t a,
    has_type gamma t a ->
    forall cutoff inserted delta,
      insert_context cutoff inserted gamma delta ->
      wf_context delta ->
      has_type delta
        (shift_term 1 cutoff t)
        (shift_term 1 cutoff a).
Proof.
  intros gamma t a Htyping.
  induction Htyping using has_type_ind'
    with (P := fun _ _ => True).
  - exact I.
  - exact I.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_universe.
    exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_var.
    + exact Hwf.
    + apply lookup_weaken with
          (inserted := inserted)
          (gamma := gamma).
      * exact Hinsert.
      * exact l.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_pi with (level_a := level_a) (level_b := level_b).
    + apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply wf_extend with (level := level_a).
        -- exact Hwf.
        -- apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_lam with (level_a := level_a) (level_b := level_b).
    + apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply wf_extend with (level := level_a).
        -- exact Hwf.
        -- apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
    + apply IHHtyping3 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply wf_extend with (level := level_a).
        -- exact Hwf.
        -- apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_subst_zero.
    apply ty_app with
        (a := shift_term 1 cutoff a)
        (b := shift_term 1 (S cutoff) b).
    + apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_sigma with (level_a := level_a) (level_b := level_b).
    + apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply wf_extend with (level := level_a).
        -- exact Hwf.
        -- apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_pair with (level_a := level_a) (level_b := level_b).
    + apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply wf_extend with (level := level_a).
        -- exact Hwf.
        -- apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
    + apply IHHtyping3 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + rewrite <- shift_term_subst_zero.
      apply IHHtyping4 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_fst with
        (b := shift_term 1 (S cutoff) b).
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_subst_zero.
    apply ty_snd with
        (a := shift_term 1 cutoff a)
        (b := shift_term 1 (S cutoff) b).
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_id with (level := level).
    + apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping3 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_refl.
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply ty_conv with
        (a := shift_term 1 cutoff a)
        (level := level).
    + apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply defeq_shift_term.
      exact d.
Qed.

Corollary has_type_weaken_top :
  forall gamma inserted t a level,
    wf_context gamma ->
    has_type gamma inserted (tUniverse level) ->
    has_type gamma t a ->
    has_type (inserted :: gamma)
      (shift_term 1 0 t)
      (shift_term 1 0 a).
Proof.
  intros gamma inserted t a level Hwf Hinserted Htyping.
  apply has_type_weaken with
      (gamma := gamma)
      (inserted := inserted)
      (cutoff := 0).
  - exact Htyping.
  - apply insert_here.
  - apply wf_extend with (level := level).
    + exact Hwf.
    + exact Hinserted.
Qed.

Example universe_typing_survives_extension :
  has_type [tUniverse 0]
    (tUniverse 0)
    (tUniverse 1).
Proof.
  change (has_type [tUniverse 0]
    (shift_term 1 0 (tUniverse 0))
    (shift_term 1 0 (tUniverse 1))).
  apply has_type_weaken_top with
      (gamma := [])
      (level := 1).
  - apply wf_empty.
  - apply ty_universe.
    apply wf_empty.
  - apply ty_universe.
    apply wf_empty.
Qed.
