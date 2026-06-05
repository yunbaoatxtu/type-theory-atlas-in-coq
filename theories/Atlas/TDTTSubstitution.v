(** Substitution for TDTT typing derivations.

    The De Bruijn equations are imported from the shared MLTT development.
    Only the typing layer is restated for TDTT's temporal rules and
    cumulative rules.
 *)

From Stdlib Require Import List.
From Atlas Require Import Syntax Ops Context UTT TemporalContext TDTT Weakening Substitution
  TDTTTemporalWeakening TDTTTemporalSubstitution TDTTWeakening.

Import ListNotations.

#[local] Hint Rewrite subst_term_utt_sort_term : utt_sort.

Inductive tdtt_substitute_context (theta : temporal_context) (replacement : term) :
    nat -> context -> context -> Prop :=
| tdtt_substitute_context_here :
    forall gamma a,
      tdtt_wf_context theta gamma ->
      tdtt_has_type theta gamma replacement a ->
      tdtt_substitute_context theta replacement 0 (a :: gamma) gamma
| tdtt_substitute_context_there :
    forall cutoff gamma delta a sort,
      tdtt_substitute_context theta replacement cutoff gamma delta ->
      tdtt_has_type theta delta
        (subst_term replacement cutoff a)
        (utt_sort_term sort) ->
      tdtt_substitute_context theta replacement (S cutoff) (a :: gamma)
        (subst_term replacement cutoff a :: delta).

Lemma tdtt_substitute_context_target_wf :
  forall theta replacement cutoff gamma delta,
    tdtt_substitute_context theta replacement cutoff gamma delta ->
    tdtt_wf_context theta delta.
Proof.
  intros theta replacement cutoff gamma delta Hcontext.
  induction Hcontext.
  - exact H.
  - apply tdtt_wf_extend with (sort := sort).
    + exact IHHcontext.
    + exact H.
Qed.

Lemma tdtt_substitute_context_weaken_time_top :
  forall theta replacement cutoff gamma delta,
    tdtt_substitute_context theta replacement cutoff gamma delta ->
    tdtt_substitute_context
      (tc_extend theta)
      (shift_time 1 0 replacement)
      cutoff
      (shift_time_context 1 0 gamma)
      (shift_time_context 1 0 delta).
Proof.
  intros theta replacement cutoff gamma delta Hcontext.
  induction Hcontext; simpl.
  - apply tdtt_substitute_context_here.
    + apply tdtt_context_weaken_time_top.
      exact H.
    + apply tdtt_has_type_weaken_time_top.
      exact H0.
  - rewrite shift_time_subst_term_commute.
    apply tdtt_substitute_context_there with (sort := sort).
    + exact IHHcontext.
    + rewrite <- shift_time_subst_term_commute.
      rewrite <- (shift_time_utt_sort_term 1 0 sort).
      apply tdtt_has_type_weaken_time_top.
      exact H.
Qed.

Lemma tdtt_lookup_substitute :
  forall theta replacement cutoff gamma delta index a,
    tdtt_substitute_context theta replacement cutoff gamma delta ->
    lookup gamma index a ->
    tdtt_has_type theta delta
      (subst_term replacement cutoff (tVar index))
      (subst_term replacement cutoff a).
Proof.
  intros theta replacement cutoff gamma delta index a Hcontext.
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
      apply tdtt_ty_var.
      * exact H.
      * assumption.
  - inversion Hlookup; subst.
    + simpl.
      rewrite subst_term_shift_one.
      apply tdtt_ty_var.
      * apply tdtt_wf_extend with (sort := sort).
        -- apply tdtt_substitute_context_target_wf in Hcontext.
           exact Hcontext.
        -- exact H.
      * apply lookup_here.
    + simpl.
      rewrite subst_term_shift_one.
      rewrite substitute_term_index_shift_one.
      apply tdtt_has_type_weaken_top with
          (gamma := delta)
          (sort := sort).
      * apply tdtt_substitute_context_target_wf in Hcontext.
        exact Hcontext.
      * exact H.
      * apply IHHcontext.
        assumption.
Qed.

Lemma temporal_wf_subst_term_identity :
  forall theta time,
    temporal_wf theta time ->
    forall replacement cutoff,
      subst_term replacement cutoff time = time.
Proof.
  intros theta time Htime replacement cutoff.
  inversion Htime; subst.
  reflexivity.
Qed.

Lemma tdtt_has_type_substitute :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    forall replacement cutoff delta,
      tdtt_substitute_context theta replacement cutoff gamma delta ->
      tdtt_has_type theta delta
        (subst_term replacement cutoff t)
        (subst_term replacement cutoff a).
Proof.
  intros theta gamma t a Htyping.
  induction Htyping using tdtt_has_type_ind'
    with (P := fun _ _ _ => True).
  all: autorewrite with utt_sort in *.
  - exact I.
  - exact I.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_prop.
    apply tdtt_substitute_context_target_wf in Hcontext.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_universe.
    apply tdtt_substitute_context_target_wf in Hcontext.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    apply tdtt_lookup_substitute with
        (gamma := gamma)
        (index := index).
    + exact Hcontext.
    + exact l.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_utt_sort_term.
    apply tdtt_ty_pi with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff domain_sort).
      apply IHHtyping1.
      exact Hcontext.
    + rewrite <-
        (subst_term_utt_sort_term replacement (S cutoff) codomain_sort).
      apply IHHtyping2.
      apply tdtt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_lam with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff domain_sort).
      apply IHHtyping1.
      exact Hcontext.
    + rewrite <-
        (subst_term_utt_sort_term replacement (S cutoff) codomain_sort).
      apply IHHtyping2.
      apply tdtt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
    + apply IHHtyping3.
      apply tdtt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_compose_zero.
    apply tdtt_ty_app with
        (a := subst_term replacement cutoff a)
        (b := subst_term replacement (S cutoff) b).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_sigma with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff domain_sort).
      apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      apply tdtt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_pair with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff domain_sort).
      apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      apply tdtt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
    + apply IHHtyping3.
      exact Hcontext.
    + rewrite <- subst_term_compose_zero.
      apply IHHtyping4.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_fst with
        (b := subst_term replacement (S cutoff) b).
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_compose_zero.
    apply tdtt_ty_snd with
        (a := subst_term replacement cutoff a)
        (b := subst_term replacement (S cutoff) b).
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_id with (level := level).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      exact Hcontext.
    + apply IHHtyping3.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_refl.
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_conv with
        (a := subst_term replacement cutoff a)
        (sort := sort).
    + apply IHHtyping1.
      exact Hcontext.
    + rewrite <- (subst_term_utt_sort_term replacement cutoff sort).
      apply IHHtyping2.
      exact Hcontext.
    + apply defeq_subst_term.
      exact d.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_prop_lift.
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_type_lift with (lower := lower).
    + apply IHHtyping.
      exact Hcontext.
    + exact l.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_utt_sort_term.
    apply tdtt_ty_at with (sort := sort).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff sort).
      apply IHHtyping.
      exact Hcontext.
    + apply temporal_wf_subst_term.
      assumption.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_utt_sort_term.
    apply tdtt_ty_later with (sort := sort).
    rewrite <- (subst_term_utt_sort_term replacement cutoff sort).
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_next.
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_fix with (sort := sort).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff sort).
      apply IHHtyping1.
      exact Hcontext.
    + rewrite <- subst_term_shift_one.
      apply IHHtyping2.
      apply tdtt_substitute_context_there with (sort := sort).
      * exact Hcontext.
      * simpl.
        apply tdtt_ty_later with (sort := sort).
        rewrite <- (subst_term_utt_sort_term replacement cutoff sort).
        apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_utt_sort_term.
    apply tdtt_ty_later_at with (sort := sort).
    + apply temporal_wf_subst_term.
      assumption.
    + rewrite <- (subst_term_utt_sort_term replacement cutoff sort).
      apply IHHtyping.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_next_at.
    + apply temporal_wf_subst_term.
      assumption.
    + apply IHHtyping.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_fix_at with (sort := sort).
    + apply temporal_wf_subst_term.
      assumption.
    + rewrite <- (subst_term_utt_sort_term replacement cutoff sort).
      apply IHHtyping1.
      exact Hcontext.
    + rewrite <- subst_term_shift_one.
      apply IHHtyping2.
      apply tdtt_substitute_context_there with (sort := sort).
      * exact Hcontext.
      * simpl.
        apply tdtt_ty_later_at with (sort := sort).
        -- apply temporal_wf_subst_term.
           assumption.
        -- rewrite <- (subst_term_utt_sort_term replacement cutoff sort).
           apply IHHtyping1.
           exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_utt_sort_term.
    apply tdtt_ty_clock_pi with (sort := sort).
    + apply tdtt_substitute_context_target_wf in Hcontext as Hwf.
      exact Hwf.
    + rewrite <-
        (subst_term_utt_sort_term (shift_time 1 0 replacement) cutoff sort).
      apply IHHtyping0.
      apply tdtt_substitute_context_weaken_time_top.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply tdtt_ty_clock_lam with (sort := sort).
    + apply tdtt_substitute_context_target_wf in Hcontext as Hwf.
      exact Hwf.
    + rewrite <-
        (subst_term_utt_sort_term (shift_time 1 0 replacement) cutoff sort).
      match goal with
      | H : tdtt_substitute_context theta replacement cutoff gamma delta,
          IH : forall replacement0 cutoff0 delta0,
            tdtt_substitute_context (tc_extend theta) replacement0 cutoff0
              (shift_time_context 1 0 gamma) delta0 ->
            tdtt_has_type (tc_extend theta) delta0
              (subst_term replacement0 cutoff0 a)
              (subst_term replacement0 cutoff0 (utt_sort_term sort)) |- _ =>
          apply IH;
          apply tdtt_substitute_context_weaken_time_top;
          exact H
      end.
    + match goal with
      | H : tdtt_substitute_context theta replacement cutoff gamma delta,
          IH : forall replacement0 cutoff0 delta0,
            tdtt_substitute_context (tc_extend theta) replacement0 cutoff0
              (shift_time_context 1 0 gamma) delta0 ->
            tdtt_has_type (tc_extend theta) delta0
              (subst_term replacement0 cutoff0 body)
              (subst_term replacement0 cutoff0 a) |- _ =>
          apply IH;
          apply tdtt_substitute_context_weaken_time_top;
          exact H
      end.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite (temporal_wf_subst_term_identity
      theta clock t replacement cutoff).
    replace (subst_term replacement cutoff (subst_time clock 0 a))
      with (subst_time clock 0
        (subst_term (shift_time 1 0 replacement) cutoff a)).
    2:{
      rewrite (subst_time_subst_term_commute
        theta clock t 0 (shift_time 1 0 replacement) cutoff a).
      rewrite subst_time_shift_cancel.
      reflexivity.
    }
    apply tdtt_ty_clock_app with
        (a := subst_term (shift_time 1 0 replacement) cutoff a).
    + apply IHHtyping.
      exact Hcontext.
    + exact t.
  - intros replacement cutoff delta Hcontext.
    simpl.
    match goal with
    | Hclock : temporal_wf theta clock |- _ =>
        rewrite (temporal_wf_subst_term_identity
          theta clock Hclock replacement cutoff)
    end.
    replace (subst_term replacement cutoff (subst_time clock 0 a))
      with (subst_time clock 0
        (subst_term (shift_time 1 0 replacement) cutoff a)).
    2:{
      match goal with
      | Hclock : temporal_wf theta clock |- _ =>
          rewrite (subst_time_subst_term_commute
            theta clock Hclock 0 (shift_time 1 0 replacement) cutoff a)
      end.
      rewrite subst_time_shift_cancel.
      reflexivity.
    }
    apply tdtt_ty_delayed_subst.
    + apply tdtt_substitute_context_target_wf in Hcontext as Hwf.
      exact Hwf.
    + match goal with
      | Hclock : temporal_wf theta clock |- _ => exact Hclock
      end.
    + match goal with
      | H : tdtt_substitute_context theta replacement cutoff gamma delta,
          IH : forall replacement0 cutoff0 delta0,
            tdtt_substitute_context (tc_extend theta) replacement0 cutoff0
              (shift_time_context 1 0 gamma) delta0 ->
            tdtt_has_type (tc_extend theta) delta0
              (subst_term replacement0 cutoff0 body)
              (subst_term replacement0 cutoff0 a) |- _ =>
          apply IH;
          apply tdtt_substitute_context_weaken_time_top;
          exact H
      end.
Qed.

Corollary tdtt_has_type_substitute_top :
  forall theta gamma replacement domain t a,
    tdtt_wf_context theta gamma ->
    tdtt_has_type theta gamma replacement domain ->
    tdtt_has_type theta (domain :: gamma) t a ->
    tdtt_has_type theta gamma
      (subst_term replacement 0 t)
      (subst_term replacement 0 a).
Proof.
  intros theta gamma replacement domain t a Hwf Hreplacement Htyping.
  apply tdtt_has_type_substitute with
      (gamma := domain :: gamma)
      (replacement := replacement)
      (cutoff := 0).
  - exact Htyping.
  - apply tdtt_substitute_context_here.
    + exact Hwf.
    + exact Hreplacement.
Qed.

Example tdtt_reflexivity_term_substitution_example :
  tdtt_has_type tc_empty []
    (subst_term tProp 0 (tRefl (tVar 0)))
    (subst_term tProp 0
      (tId (tUniverse 0) (tVar 0) (tVar 0))).
Proof.
  apply tdtt_has_type_substitute_top with
      (domain := tUniverse 0).
  - apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
  - apply tdtt_ty_refl.
    apply tdtt_ty_var.
    + apply tdtt_wf_extend with (sort := usType 1).
      * apply tdtt_wf_empty.
      * apply tdtt_ty_universe.
        apply tdtt_wf_empty.
    + apply lookup_here.
Qed.

Example tdtt_at_term_substitution_example :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (subst_term tProp 0 (tAt (tVar 0) (tTimeVar 0)))
    (subst_term tProp 0 (tUniverse 0)).
Proof.
  apply tdtt_has_type_substitute_top with
      (domain := tUniverse 0).
  - apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
  - apply tdtt_ty_at with (sort := usType 0).
    + apply tdtt_ty_var.
      * apply tdtt_wf_extend with (sort := usType 1).
        -- apply tdtt_wf_empty.
        -- apply tdtt_ty_universe.
           apply tdtt_wf_empty.
      * apply lookup_here.
    + apply temporal_wf_var.
      apply temporal_lookup_here.
Qed.
