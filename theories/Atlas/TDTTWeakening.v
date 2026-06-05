(** Structural weakening for TDTT typing derivations.

    The ordinary-variable algebra is shared with MLTT.  This file lifts it
    through the TDTT-specific temporal rules.
 *)

From Stdlib Require Import Lia List.
From Atlas Require Import Syntax Ops Context DefEq Weakening UTT TemporalContext TDTT
  TDTTTemporalWeakening.

Import ListNotations.

#[local] Hint Rewrite shift_term_utt_sort_term : utt_sort.

Lemma insert_context_shift_time :
  forall amount time_cutoff cutoff inserted gamma delta,
    insert_context cutoff inserted gamma delta ->
    insert_context cutoff
      (shift_time amount time_cutoff inserted)
      (shift_time_context amount time_cutoff gamma)
      (shift_time_context amount time_cutoff delta).
Proof.
  intros amount time_cutoff cutoff inserted gamma delta Hinsert.
  induction Hinsert; simpl.
  - apply insert_here.
  - rewrite shift_time_shift_term_commute.
    apply insert_there.
    exact IHHinsert.
Qed.

Lemma subst_time_shift_term_commute_wf :
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

Lemma temporal_wf_shift_term_identity :
  forall theta time,
    temporal_wf theta time ->
    forall amount cutoff,
      shift_term amount cutoff time = time.
Proof.
  intros theta time Htime amount cutoff.
  inversion Htime; subst.
  reflexivity.
Qed.

Lemma tdtt_has_type_weaken :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    forall cutoff inserted delta,
      insert_context cutoff inserted gamma delta ->
      tdtt_wf_context theta delta ->
      tdtt_has_type theta delta
        (shift_term 1 cutoff t)
        (shift_term 1 cutoff a).
Proof.
  intros theta gamma t a Htyping.
  induction Htyping using tdtt_has_type_ind'
    with (P := fun _ _ _ => True).
  all: autorewrite with utt_sort in *.
  - exact I.
  - exact I.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_prop.
    exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_universe.
    exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_var.
    + exact Hwf.
    + apply lookup_weaken with
          (inserted := inserted)
          (gamma := gamma).
      * exact Hinsert.
      * exact l.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_utt_sort_term.
    apply tdtt_ty_pi with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
      apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + rewrite <- (shift_term_utt_sort_term 1 (S cutoff) codomain_sort).
      apply IHHtyping2 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply tdtt_wf_extend with (sort := domain_sort).
        -- exact Hwf.
        -- rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
           apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_lam with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
      apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + rewrite <- (shift_term_utt_sort_term 1 (S cutoff) codomain_sort).
      apply IHHtyping2 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply tdtt_wf_extend with (sort := domain_sort).
        -- exact Hwf.
        -- rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
           apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
    + apply IHHtyping3 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply tdtt_wf_extend with (sort := domain_sort).
        -- exact Hwf.
        -- rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
           apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_subst_zero.
    apply tdtt_ty_app with
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
    apply tdtt_ty_sigma with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
      apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply tdtt_wf_extend with (sort := domain_sort).
        -- exact Hwf.
        -- rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
           apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_pair with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
      apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply IHHtyping2 with
          (inserted := inserted)
          (delta := shift_term 1 cutoff a :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply tdtt_wf_extend with (sort := domain_sort).
        -- exact Hwf.
        -- rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
           apply IHHtyping1 with
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
    apply tdtt_ty_fst with
        (b := shift_term 1 (S cutoff) b).
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_subst_zero.
    apply tdtt_ty_snd with
        (a := shift_term 1 cutoff a)
        (b := shift_term 1 (S cutoff) b).
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_id with (level := level).
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
    apply tdtt_ty_refl.
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_conv with
        (a := shift_term 1 cutoff a)
        (sort := sort).
    + apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
      apply IHHtyping2 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply defeq_shift_term.
      exact d.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_prop_lift.
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_type_lift with (lower := lower).
    + apply IHHtyping with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + exact l.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_utt_sort_term.
    apply tdtt_ty_at with (sort := sort).
    + rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
      apply IHHtyping with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + apply temporal_wf_shift_term.
      assumption.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_utt_sort_term.
    apply tdtt_ty_later with (sort := sort).
    rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_next.
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_fix with (sort := sort).
    + rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
      apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + rewrite <- shift_term_one_commute by lia.
      apply IHHtyping2 with
          (inserted := inserted)
          (delta := tLater (shift_term 1 cutoff a) :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply tdtt_wf_extend with (sort := sort).
        -- exact Hwf.
        -- apply tdtt_ty_later with (sort := sort).
           rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
           apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_utt_sort_term.
    apply tdtt_ty_later_at with (sort := sort).
    + apply temporal_wf_shift_term.
      assumption.
    + rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
      apply IHHtyping with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_next_at.
    + apply temporal_wf_shift_term.
      assumption.
    + apply IHHtyping with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_fix_at with (sort := sort).
    + apply temporal_wf_shift_term.
      assumption.
    + rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
      apply IHHtyping1 with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + rewrite <- shift_term_one_commute by lia.
      apply IHHtyping2 with
          (inserted := inserted)
          (delta := tLaterAt
            (shift_term 1 cutoff clock)
            (shift_term 1 cutoff a) :: delta).
      * apply insert_there.
        exact Hinsert.
      * apply tdtt_wf_extend with (sort := sort).
        -- exact Hwf.
        -- apply tdtt_ty_later_at with (sort := sort).
           ++ apply temporal_wf_shift_term.
              assumption.
           ++ rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
              apply IHHtyping1 with
                  (inserted := inserted)
                  (delta := delta).
              ** exact Hinsert.
              ** exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_utt_sort_term.
    apply tdtt_ty_clock_pi with (sort := sort).
    + exact Hwf.
    + rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
      match goal with
      | H : forall cutoff0 inserted0 delta0,
          insert_context cutoff0 inserted0
            (shift_time_context 1 0 gamma) delta0 ->
          tdtt_wf_context (tc_extend theta) delta0 ->
          tdtt_has_type (tc_extend theta) delta0
            (shift_term 1 cutoff0 a) _ |- _ =>
          apply H with
            (inserted := shift_time 1 0 inserted)
            (delta := shift_time_context 1 0 delta)
      end.
      * apply insert_context_shift_time.
        exact Hinsert.
      * apply tdtt_context_weaken_time_top.
        exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply tdtt_ty_clock_lam with (sort := sort).
    + exact Hwf.
    + rewrite <- (shift_term_utt_sort_term 1 cutoff sort).
      match goal with
      | H : forall cutoff0 inserted0 delta0,
          insert_context cutoff0 inserted0
            (shift_time_context 1 0 gamma) delta0 ->
          tdtt_wf_context (tc_extend theta) delta0 ->
          tdtt_has_type (tc_extend theta) delta0
            (shift_term 1 cutoff0 a) _ |- _ =>
          apply H with
            (inserted := shift_time 1 0 inserted)
            (delta := shift_time_context 1 0 delta)
      end.
      * apply insert_context_shift_time.
        exact Hinsert.
      * apply tdtt_context_weaken_time_top.
        exact Hwf.
    + match goal with
      | H : forall cutoff0 inserted0 delta0,
          insert_context cutoff0 inserted0
            (shift_time_context 1 0 gamma) delta0 ->
          tdtt_wf_context (tc_extend theta) delta0 ->
          tdtt_has_type (tc_extend theta) delta0
            (shift_term 1 cutoff0 body) (shift_term 1 cutoff0 a) |- _ =>
          apply H with
            (inserted := shift_time 1 0 inserted)
            (delta := shift_time_context 1 0 delta)
      end.
      * apply insert_context_shift_time.
        exact Hinsert.
      * apply tdtt_context_weaken_time_top.
        exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    match goal with
    | Hclock : temporal_wf theta clock |- _ =>
        rewrite (temporal_wf_shift_term_identity theta clock Hclock 1 cutoff);
        rewrite <- (subst_time_shift_term_commute_wf theta clock Hclock)
    end.
    apply tdtt_ty_clock_app with (a := shift_term 1 cutoff a).
    + apply IHHtyping with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + match goal with
      | Hclock : temporal_wf theta clock |- _ => exact Hclock
      end.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    match goal with
    | Hclock : temporal_wf theta clock |- _ =>
        rewrite (temporal_wf_shift_term_identity theta clock Hclock 1 cutoff);
        rewrite <- (subst_time_shift_term_commute_wf theta clock Hclock)
    end.
    apply tdtt_ty_delayed_subst.
    + exact Hwf.
    + match goal with
      | Hclock : temporal_wf theta clock |- _ => exact Hclock
      end.
    + match goal with
      | H : forall cutoff0 inserted0 delta0,
          insert_context cutoff0 inserted0
            (shift_time_context 1 0 gamma) delta0 ->
          tdtt_wf_context (tc_extend theta) delta0 ->
          tdtt_has_type (tc_extend theta) delta0
            (shift_term 1 cutoff0 body) (shift_term 1 cutoff0 a) |- _ =>
          apply H with
            (inserted := shift_time 1 0 inserted)
            (delta := shift_time_context 1 0 delta)
      end.
      * apply insert_context_shift_time.
        exact Hinsert.
      * apply tdtt_context_weaken_time_top.
        exact Hwf.
Qed.

Corollary tdtt_has_type_weaken_top :
  forall theta gamma inserted t a sort,
    tdtt_wf_context theta gamma ->
    tdtt_has_type theta gamma inserted (utt_sort_term sort) ->
    tdtt_has_type theta gamma t a ->
    tdtt_has_type theta (inserted :: gamma)
      (shift_term 1 0 t)
      (shift_term 1 0 a).
Proof.
  intros theta gamma inserted t a sort Hwf Hinserted Htyping.
  apply tdtt_has_type_weaken with
      (gamma := gamma)
      (inserted := inserted)
      (cutoff := 0).
  - exact Htyping.
  - apply insert_here.
  - apply tdtt_wf_extend with (sort := sort).
    + exact Hwf.
    + exact Hinserted.
Qed.

Example tdtt_prop_typing_survives_term_extension :
  tdtt_has_type tc_empty [tProp]
    tProp
    (tUniverse 0).
Proof.
  change (tdtt_has_type tc_empty [tProp]
    (shift_term 1 0 tProp)
    (shift_term 1 0 (tUniverse 0))).
  apply tdtt_has_type_weaken_top with
      (gamma := [])
      (sort := usType 0).
  - apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
Qed.

Example tdtt_at_typing_survives_term_extension :
  tdtt_has_type
    (tc_extend tc_empty)
    [tProp]
    (tAt tProp (tTimeVar 0))
    (tUniverse 0).
Proof.
  change (tdtt_has_type
    (tc_extend tc_empty)
    [tProp]
    (shift_term 1 0 (tAt tProp (tTimeVar 0)))
    (shift_term 1 0 (tUniverse 0))).
  apply tdtt_has_type_weaken_top with
      (gamma := [])
      (sort := usType 0).
  - apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
  - apply tdtt_prop_at_current_time.
Qed.
