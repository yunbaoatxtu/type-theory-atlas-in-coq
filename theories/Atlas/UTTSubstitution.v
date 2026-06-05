(** Substitution for UTT typing derivations.

    The De Bruijn equations are imported from the shared MLTT development.
    Only the typing layer is restated for UTT's propositional sort and
    cumulative rules.
 *)

From Stdlib Require Import List.
From Atlas Require Import Syntax Ops Context UTT Weakening Substitution
  UTTWeakening.

Import ListNotations.

#[local] Hint Rewrite subst_term_utt_sort_term : utt_sort.

Inductive utt_substitute_context (replacement : term) :
    nat -> context -> context -> Prop :=
| utt_substitute_context_here :
    forall gamma a,
      utt_wf_context gamma ->
      utt_has_type gamma replacement a ->
      utt_substitute_context replacement 0 (a :: gamma) gamma
| utt_substitute_context_there :
    forall cutoff gamma delta a sort,
      utt_substitute_context replacement cutoff gamma delta ->
      utt_has_type delta
        (subst_term replacement cutoff a)
        (utt_sort_term sort) ->
      utt_substitute_context replacement (S cutoff) (a :: gamma)
        (subst_term replacement cutoff a :: delta).

Lemma utt_substitute_context_target_wf :
  forall replacement cutoff gamma delta,
    utt_substitute_context replacement cutoff gamma delta ->
    utt_wf_context delta.
Proof.
  intros replacement cutoff gamma delta Hcontext.
  induction Hcontext.
  - exact H.
  - apply utt_wf_extend with (sort := sort).
    + exact IHHcontext.
    + exact H.
Qed.

Lemma utt_lookup_substitute :
  forall replacement cutoff gamma delta index a,
    utt_substitute_context replacement cutoff gamma delta ->
    lookup gamma index a ->
    utt_has_type delta
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
      apply utt_ty_var.
      * exact H.
      * assumption.
  - inversion Hlookup; subst.
    + simpl.
      rewrite subst_term_shift_one.
      apply utt_ty_var.
      * apply utt_wf_extend with (sort := sort).
        -- apply utt_substitute_context_target_wf in Hcontext.
           exact Hcontext.
        -- exact H.
      * apply lookup_here.
    + simpl.
      rewrite subst_term_shift_one.
      rewrite substitute_term_index_shift_one.
      apply utt_has_type_weaken_top with
          (gamma := delta)
          (sort := sort).
      * apply utt_substitute_context_target_wf in Hcontext.
        exact Hcontext.
      * exact H.
      * apply IHHcontext.
        assumption.
Qed.

Lemma utt_has_type_substitute :
  forall gamma t a,
    utt_has_type gamma t a ->
    forall replacement cutoff delta,
      utt_substitute_context replacement cutoff gamma delta ->
      utt_has_type delta
        (subst_term replacement cutoff t)
        (subst_term replacement cutoff a).
Proof.
  intros gamma t a Htyping.
  induction Htyping using utt_has_type_ind'
    with (P := fun _ _ => True).
  all: autorewrite with utt_sort in *.
  - exact I.
  - exact I.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_prop.
    apply utt_substitute_context_target_wf in Hcontext.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_universe.
    apply utt_substitute_context_target_wf in Hcontext.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    apply utt_lookup_substitute with
        (gamma := gamma)
        (index := index).
    + exact Hcontext.
    + exact l.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_utt_sort_term.
    apply utt_ty_pi with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff domain_sort).
      apply IHHtyping1.
      exact Hcontext.
    + rewrite <-
        (subst_term_utt_sort_term replacement (S cutoff) codomain_sort).
      apply IHHtyping2.
      apply utt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_lam with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff domain_sort).
      apply IHHtyping1.
      exact Hcontext.
    + rewrite <-
        (subst_term_utt_sort_term replacement (S cutoff) codomain_sort).
      apply IHHtyping2.
      apply utt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
    + apply IHHtyping3.
      apply utt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_compose_zero.
    apply utt_ty_app with
        (a := subst_term replacement cutoff a)
        (b := subst_term replacement (S cutoff) b).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_sigma with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff domain_sort).
      apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      apply utt_substitute_context_there with (sort := domain_sort).
      * exact Hcontext.
      * rewrite <-
          (subst_term_utt_sort_term replacement cutoff domain_sort).
        apply IHHtyping1.
        exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_pair with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + rewrite <- (subst_term_utt_sort_term replacement cutoff domain_sort).
      apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      apply utt_substitute_context_there with (sort := domain_sort).
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
    apply utt_ty_fst with
        (b := subst_term replacement (S cutoff) b).
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    rewrite subst_term_compose_zero.
    apply utt_ty_snd with
        (a := subst_term replacement cutoff a)
        (b := subst_term replacement (S cutoff) b).
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_id with (level := level).
    + apply IHHtyping1.
      exact Hcontext.
    + apply IHHtyping2.
      exact Hcontext.
    + apply IHHtyping3.
      exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_refl.
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_conv with
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
    apply utt_ty_prop_lift.
    apply IHHtyping.
    exact Hcontext.
  - intros replacement cutoff delta Hcontext.
    simpl.
    apply utt_ty_type_lift with (lower := lower).
    + apply IHHtyping.
      exact Hcontext.
    + exact l.
Qed.

Corollary utt_has_type_substitute_top :
  forall gamma replacement domain t a,
    utt_wf_context gamma ->
    utt_has_type gamma replacement domain ->
    utt_has_type (domain :: gamma) t a ->
    utt_has_type gamma
      (subst_term replacement 0 t)
      (subst_term replacement 0 a).
Proof.
  intros gamma replacement domain t a Hwf Hreplacement Htyping.
  apply utt_has_type_substitute with
      (gamma := domain :: gamma)
      (replacement := replacement)
      (cutoff := 0).
  - exact Htyping.
  - apply utt_substitute_context_here.
    + exact Hwf.
    + exact Hreplacement.
Qed.

Example utt_reflexivity_substitution_example :
  utt_has_type []
    (subst_term tProp 0 (tRefl (tVar 0)))
    (subst_term tProp 0
      (tId (tUniverse 0) (tVar 0) (tVar 0))).
Proof.
  apply utt_has_type_substitute_top with
      (domain := tUniverse 0).
  - apply utt_wf_empty.
  - apply utt_ty_prop.
    apply utt_wf_empty.
  - apply utt_ty_refl.
    apply utt_ty_var.
    + apply utt_wf_extend with (sort := usType 1).
      * apply utt_wf_empty.
      * apply utt_ty_universe.
        apply utt_wf_empty.
    + apply lookup_here.
Qed.
