(** Weakening for TDTT temporal parameters.

    Temporal parameters use a De Bruijn namespace independent from ordinary
    term variables.  Extending the temporal context shifts every temporal
    occurrence in the ordinary context, term, and type.
 *)

From Stdlib Require Import Arith.PeanoNat Lia List.
From Atlas Require Import Syntax Ops Context DefEq Weakening UTT
  TemporalContext TDTT.

Import ListNotations.

Inductive temporal_insert_context :
    nat -> temporal_context -> temporal_context -> Prop :=
| temporal_insert_here :
    forall theta,
      temporal_insert_context 0 theta (tc_extend theta)
| temporal_insert_there :
    forall cutoff theta delta,
      temporal_insert_context cutoff theta delta ->
      temporal_insert_context (S cutoff) (tc_extend theta) (tc_extend delta).

Lemma temporal_lookup_weaken :
  forall cutoff theta delta index,
    temporal_insert_context cutoff theta delta ->
    temporal_lookup theta index ->
    temporal_lookup delta (shift_index 1 cutoff index).
Proof.
  intros cutoff theta delta index Hinsert.
  revert index.
  induction Hinsert; intros index Hlookup.
  - rewrite shift_index_one_zero.
    apply temporal_lookup_there.
    exact Hlookup.
  - inversion Hlookup; subst.
    + simpl.
      apply temporal_lookup_here.
    + rewrite shift_index_one_succ.
      apply temporal_lookup_there.
      apply IHHinsert.
      assumption.
Qed.

Lemma temporal_wf_weaken :
  forall cutoff theta delta time,
    temporal_insert_context cutoff theta delta ->
    temporal_wf theta time ->
    temporal_wf delta (shift_time 1 cutoff time).
Proof.
  intros cutoff theta delta time Hinsert Htime.
  inversion Htime; subst.
  simpl.
  apply temporal_wf_var.
  apply temporal_lookup_weaken with (theta := theta).
  - exact Hinsert.
  - assumption.
Qed.

Corollary temporal_wf_weaken_top :
  forall theta time,
    temporal_wf theta time ->
    temporal_wf (tc_extend theta) (shift_time 1 0 time).
Proof.
  intros theta time Htime.
  apply temporal_wf_weaken with
      (cutoff := 0)
      (theta := theta).
  - apply temporal_insert_here.
  - exact Htime.
Qed.

Lemma lookup_shift_time_context :
  forall amount cutoff gamma index a,
    lookup gamma index a ->
    lookup (shift_time_context amount cutoff gamma)
      index
      (shift_time amount cutoff a).
Proof.
  intros amount cutoff gamma index a Hlookup.
  induction Hlookup; simpl.
  - rewrite shift_time_shift_term_commute.
    apply lookup_here.
  - rewrite shift_time_shift_term_commute.
    apply lookup_there.
      exact IHHlookup.
Qed.

Lemma shift_time_substitute_time_index :
  forall replacement substitution_cutoff weakening_cutoff index,
    shift_time 1 (substitution_cutoff + weakening_cutoff)
      (substitute_time_index replacement substitution_cutoff index) =
    substitute_time_index
      (shift_time 1 weakening_cutoff replacement)
      substitution_cutoff
      (shift_index 1 (S (substitution_cutoff + weakening_cutoff)) index).
Proof.
  intros replacement substitution_cutoff weakening_cutoff index.
  unfold substitute_time_index.
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
      apply shift_time_compose.
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

Lemma shift_time_subst_time_commute :
  forall replacement substitution_cutoff weakening_cutoff t,
    shift_time 1 (substitution_cutoff + weakening_cutoff)
      (subst_time replacement substitution_cutoff t) =
    subst_time
      (shift_time 1 weakening_cutoff replacement)
      substitution_cutoff
      (shift_time 1 (S (substitution_cutoff + weakening_cutoff)) t).
Proof.
  intros replacement substitution_cutoff weakening_cutoff t.
  revert replacement substitution_cutoff.
  induction t; intros replacement substitution_cutoff; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  - apply shift_time_substitute_time_index.
  - replace (S (substitution_cutoff + weakening_cutoff))
      with (S substitution_cutoff + weakening_cutoff) by lia.
    rewrite (IHt replacement (S substitution_cutoff)).
    reflexivity.
  - replace (S (substitution_cutoff + weakening_cutoff))
      with (S substitution_cutoff + weakening_cutoff) by lia.
    rewrite (IHt replacement (S substitution_cutoff)).
    reflexivity.
  - replace (S (substitution_cutoff + weakening_cutoff))
      with (S substitution_cutoff + weakening_cutoff) by lia.
    rewrite (IHt2 replacement (S substitution_cutoff)).
    reflexivity.
Qed.

Corollary shift_time_subst_time_zero :
  forall replacement weakening_cutoff t,
    shift_time 1 weakening_cutoff (subst_time replacement 0 t) =
    subst_time
      (shift_time 1 weakening_cutoff replacement)
      0
      (shift_time 1 (S weakening_cutoff) t).
Proof.
  intros replacement weakening_cutoff t.
  pose proof (shift_time_subst_time_commute
    replacement 0 weakening_cutoff t) as Hcommute.
  replace (0 + weakening_cutoff) with weakening_cutoff in Hcommute by lia.
  exact Hcommute.
Qed.

Lemma defeq_shift_time :
  forall t u,
    defeq t u ->
    forall cutoff,
      defeq (shift_time 1 cutoff t) (shift_time 1 cutoff u).
Proof.
  intros t u Heq.
  induction Heq; intros cutoff; simpl.
  - apply de_refl.
  - apply de_sym.
    apply IHHeq.
  - eapply de_trans.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite shift_time_subst_term_commute.
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
  - rewrite shift_time_subst_term_commute.
    apply de_fix_unfold.
  - apply de_fix.
    apply IHHeq.
  - apply de_later_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - apply de_next_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite shift_time_subst_term_commute.
    apply de_fix_at_unfold.
  - apply de_fix_at.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite shift_time_subst_time_zero.
    apply de_clock_beta.
  - apply de_clock_pi.
    apply IHHeq.
  - apply de_clock_lam.
    apply IHHeq.
  - apply de_clock_app.
    + apply IHHeq1.
    + apply IHHeq2.
  - rewrite shift_time_subst_time_zero.
    apply de_delayed_subst_compute.
  - apply de_delayed_subst.
    + apply IHHeq1.
    + apply IHHeq2.
Qed.

Lemma shift_time_context_one_commute :
  forall cutoff gamma,
    shift_time_context 1 0 (shift_time_context 1 cutoff gamma) =
    shift_time_context 1 (S cutoff) (shift_time_context 1 0 gamma).
Proof.
  intros cutoff gamma.
  induction gamma as [| a gamma IHgamma]; simpl.
  - reflexivity.
  - rewrite IHgamma.
    f_equal.
    symmetry.
    replace (S cutoff) with (1 + cutoff) by lia.
    apply shift_time_compose.
    lia.
Qed.

Theorem tdtt_typing_weaken_time_general :
  (forall theta gamma,
      tdtt_wf_context theta gamma ->
      forall cutoff delta,
        temporal_insert_context cutoff theta delta ->
        tdtt_wf_context delta (shift_time_context 1 cutoff gamma)) /\
  (forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      forall cutoff delta,
        temporal_insert_context cutoff theta delta ->
        tdtt_has_type delta
          (shift_time_context 1 cutoff gamma)
          (shift_time 1 cutoff t)
          (shift_time 1 cutoff a)).
Proof.
  apply tdtt_typing_mutind
    with
      (P := fun theta gamma _ =>
        forall cutoff delta,
          temporal_insert_context cutoff theta delta ->
          tdtt_wf_context delta (shift_time_context 1 cutoff gamma))
      (P0 := fun theta gamma t a _ =>
        forall cutoff delta,
          temporal_insert_context cutoff theta delta ->
          tdtt_has_type delta
            (shift_time_context 1 cutoff gamma)
            (shift_time 1 cutoff t)
            (shift_time 1 cutoff a)).
  - intros theta cutoff delta Hinsert.
    apply tdtt_wf_empty.
  - intros theta gamma a sort _ Hgamma _ Ha cutoff delta Hinsert.
    simpl.
    apply tdtt_wf_extend with (sort := sort).
    + apply Hgamma.
      exact Hinsert.
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
  - intros theta gamma _ Hgamma cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_prop.
    apply Hgamma.
    exact Hinsert.
  - intros theta gamma level _ Hgamma cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_universe.
    apply Hgamma.
    exact Hinsert.
  - intros theta gamma index a _ Hgamma Hlookup cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_var.
    + apply Hgamma.
      exact Hinsert.
    + apply lookup_shift_time_context.
      exact Hlookup.
  - intros theta gamma a b domain_sort codomain_sort
      _ Ha _ Hb cutoff delta Hinsert.
    simpl.
    rewrite shift_time_utt_sort_term.
    apply tdtt_ty_pi with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
    + specialize (Hb cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Hb.
      exact Hb.
  - intros theta gamma a body b domain_sort codomain_sort
      _ Ha _ Hb _ Hbody cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_lam with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
    + specialize (Hb cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Hb.
      exact Hb.
    + apply Hbody.
      exact Hinsert.
  - intros theta gamma f argument a b
      _ Hf _ Hargument cutoff delta Hinsert.
    simpl.
    rewrite shift_time_subst_term_commute.
    apply tdtt_ty_app with
        (a := shift_time 1 cutoff a)
        (b := shift_time 1 cutoff b).
    + apply Hf.
      exact Hinsert.
    + apply Hargument.
      exact Hinsert.
  - intros theta gamma a b domain_sort level_b
      _ Ha _ Hb cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_sigma with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
    + apply Hb.
      exact Hinsert.
  - intros theta gamma a b first second domain_sort level_b
      _ Ha _ Hb _ Hfirst _ Hsecond cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_pair with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
    + apply Hb.
      exact Hinsert.
    + apply Hfirst.
      exact Hinsert.
    + specialize (Hsecond cutoff delta Hinsert).
      rewrite shift_time_subst_term_commute in Hsecond.
      exact Hsecond.
  - intros theta gamma pair a b _ Hpair cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_fst with (b := shift_time 1 cutoff b).
    apply Hpair.
    exact Hinsert.
  - intros theta gamma pair a b _ Hpair cutoff delta Hinsert.
    simpl.
    rewrite shift_time_subst_term_commute.
    apply tdtt_ty_snd with
        (a := shift_time 1 cutoff a)
        (b := shift_time 1 cutoff b).
    apply Hpair.
    exact Hinsert.
  - intros theta gamma a x y level
      _ Ha _ Hx _ Hy cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_id with (level := level).
    + apply Ha.
      exact Hinsert.
    + apply Hx.
      exact Hinsert.
    + apply Hy.
      exact Hinsert.
  - intros theta gamma a x _ Hx cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_refl.
    apply Hx.
    exact Hinsert.
  - intros theta gamma t a b sort _ Ht _ Hb Heq cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_conv with
        (a := shift_time 1 cutoff a)
        (sort := sort).
    + apply Ht.
      exact Hinsert.
    + specialize (Hb cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Hb.
      exact Hb.
    + apply defeq_shift_time.
      exact Heq.
  - intros theta gamma proposition level
      _ Hproposition cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_prop_lift.
    apply Hproposition.
    exact Hinsert.
  - intros theta gamma a lower upper _ Ha Hle cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_type_lift with (lower := lower).
    + apply Ha.
      exact Hinsert.
    + exact Hle.
  - intros theta gamma a time sort _ Ha Htime cutoff delta Hinsert.
    simpl.
    rewrite shift_time_utt_sort_term.
    apply tdtt_ty_at with (sort := sort).
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
    + apply temporal_wf_weaken with (theta := theta).
      * exact Hinsert.
      * exact Htime.
  - intros theta gamma a sort _ Ha cutoff delta Hinsert.
    simpl.
    rewrite shift_time_utt_sort_term.
    apply tdtt_ty_later with (sort := sort).
    specialize (Ha cutoff delta Hinsert).
    rewrite shift_time_utt_sort_term in Ha.
    exact Ha.
  - intros theta gamma t a _ Ht cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_next.
    apply Ht.
    exact Hinsert.
  - intros theta gamma a body sort _ Ha _ Hbody cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_fix with (sort := sort).
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
    + specialize (Hbody cutoff delta Hinsert).
      rewrite shift_time_shift_term_commute in Hbody.
      exact Hbody.
  - intros theta gamma clock a sort Hclock _ Ha cutoff delta Hinsert.
    simpl.
    rewrite shift_time_utt_sort_term.
    apply tdtt_ty_later_at with (sort := sort).
    + apply temporal_wf_weaken with (theta := theta).
      * exact Hinsert.
      * exact Hclock.
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
  - intros theta gamma clock t a Hclock _ Ht cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_next_at.
    + apply temporal_wf_weaken with (theta := theta).
      * exact Hinsert.
      * exact Hclock.
    + apply Ht.
      exact Hinsert.
  - intros theta gamma clock a body sort Hclock
      _ Ha _ Hbody cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_fix_at with (sort := sort).
    + apply temporal_wf_weaken with (theta := theta).
      * exact Hinsert.
      * exact Hclock.
    + specialize (Ha cutoff delta Hinsert).
      rewrite shift_time_utt_sort_term in Ha.
      exact Ha.
    + specialize (Hbody cutoff delta Hinsert).
      rewrite shift_time_shift_term_commute in Hbody.
      exact Hbody.
  - intros theta gamma a sort _ Hgamma _ Ha cutoff delta Hinsert.
    simpl.
    rewrite shift_time_utt_sort_term.
    apply tdtt_ty_clock_pi with (sort := sort).
    + apply Hgamma.
      exact Hinsert.
    + rewrite shift_time_context_one_commute.
      rewrite <- (shift_time_utt_sort_term 1 (S cutoff) sort).
      apply Ha.
      apply temporal_insert_there.
      exact Hinsert.
  - intros theta gamma body a sort _ Hgamma _ Ha _ Hbody cutoff delta Hinsert.
    simpl.
    apply tdtt_ty_clock_lam with (sort := sort).
    + apply Hgamma.
      exact Hinsert.
    + rewrite shift_time_context_one_commute.
      rewrite <- (shift_time_utt_sort_term 1 (S cutoff) sort).
      apply Ha.
      apply temporal_insert_there.
      exact Hinsert.
    + rewrite shift_time_context_one_commute.
      apply Hbody.
      apply temporal_insert_there.
      exact Hinsert.
  - intros theta gamma f clock a _ Hf Hclock cutoff delta Hinsert.
    simpl.
    rewrite shift_time_subst_time_zero.
    apply tdtt_ty_clock_app with (a := shift_time 1 (S cutoff) a).
    + apply Hf.
      exact Hinsert.
    + apply temporal_wf_weaken with (theta := theta).
      * exact Hinsert.
      * exact Hclock.
  - intros theta gamma clock body a _ Hgamma Hclock _ Hbody
      cutoff delta Hinsert.
    simpl.
    rewrite shift_time_subst_time_zero.
    apply tdtt_ty_delayed_subst.
    + apply Hgamma.
      exact Hinsert.
    + apply temporal_wf_weaken with (theta := theta).
      * exact Hinsert.
      * exact Hclock.
    + rewrite shift_time_context_one_commute.
      apply Hbody.
      apply temporal_insert_there.
      exact Hinsert.
Qed.

Theorem tdtt_typing_weaken_time :
  forall cutoff theta delta,
    temporal_insert_context cutoff theta delta ->
    (forall gamma,
        tdtt_wf_context theta gamma ->
        tdtt_wf_context delta (shift_time_context 1 cutoff gamma)) /\
    (forall gamma t a,
        tdtt_has_type theta gamma t a ->
        tdtt_has_type delta
          (shift_time_context 1 cutoff gamma)
          (shift_time 1 cutoff t)
          (shift_time 1 cutoff a)).
Proof.
  intros cutoff theta delta Hinsert.
  split.
  - intros gamma Hgamma.
    apply tdtt_typing_weaken_time_general with (theta := theta).
    + exact Hgamma.
    + exact Hinsert.
  - intros gamma t a Htyping.
    apply tdtt_typing_weaken_time_general with (theta := theta).
    + exact Htyping.
    + exact Hinsert.
Qed.

Corollary tdtt_context_weaken_time_top :
  forall theta gamma,
    tdtt_wf_context theta gamma ->
    tdtt_wf_context
      (tc_extend theta)
      (shift_time_context 1 0 gamma).
Proof.
  intros theta gamma Hgamma.
  apply (tdtt_typing_weaken_time 0 theta (tc_extend theta)).
  - apply temporal_insert_here.
  - exact Hgamma.
Qed.

Corollary tdtt_has_type_weaken_time_top :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      (shift_time 1 0 t)
      (shift_time 1 0 a).
Proof.
  intros theta gamma t a Htyping.
  apply (tdtt_typing_weaken_time 0 theta (tc_extend theta)).
  - apply temporal_insert_here.
  - exact Htyping.
Qed.

Example tdtt_at_typing_survives_time_extension :
  tdtt_has_type
    (tc_extend (tc_extend tc_empty))
    []
    (tAt tProp (tTimeVar 1))
    (tUniverse 0).
Proof.
  change (tdtt_has_type
    (tc_extend (tc_extend tc_empty))
    (shift_time_context 1 0 [])
    (shift_time 1 0 (tAt tProp (tTimeVar 0)))
    (shift_time 1 0 (tUniverse 0))).
  apply tdtt_has_type_weaken_time_top.
  apply tdtt_prop_at_current_time.
Qed.
