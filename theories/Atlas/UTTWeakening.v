(** Structural weakening for UTT typing derivations.

    The ordinary-variable algebra is shared with MLTT.  This file lifts it
    through the UTT-specific propositional sort and cumulative rules.
 *)

From Stdlib Require Import List.
From Atlas Require Import Syntax Ops Context DefEq Weakening UTT.

Import ListNotations.

#[local] Hint Rewrite shift_term_utt_sort_term : utt_sort.

Lemma utt_has_type_weaken :
  forall gamma t a,
    utt_has_type gamma t a ->
    forall cutoff inserted delta,
      insert_context cutoff inserted gamma delta ->
      utt_wf_context delta ->
      utt_has_type delta
        (shift_term 1 cutoff t)
        (shift_term 1 cutoff a).
Proof.
  intros gamma t a Htyping.
  induction Htyping using utt_has_type_ind'
    with (P := fun _ _ => True).
  all: autorewrite with utt_sort in *.
  - exact I.
  - exact I.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply utt_ty_prop.
    exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply utt_ty_universe.
    exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply utt_ty_var.
    + exact Hwf.
    + apply lookup_weaken with
          (inserted := inserted)
          (gamma := gamma).
      * exact Hinsert.
      * exact l.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_utt_sort_term.
    apply utt_ty_pi with
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
      * apply utt_wf_extend with (sort := domain_sort).
        -- exact Hwf.
        -- rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
           apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply utt_ty_lam with
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
      * apply utt_wf_extend with (sort := domain_sort).
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
      * apply utt_wf_extend with (sort := domain_sort).
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
    apply utt_ty_app with
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
    apply utt_ty_sigma with
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
      * apply utt_wf_extend with (sort := domain_sort).
        -- exact Hwf.
        -- rewrite <- (shift_term_utt_sort_term 1 cutoff domain_sort).
           apply IHHtyping1 with
              (inserted := inserted)
              (delta := delta).
           ++ exact Hinsert.
           ++ exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply utt_ty_pair with
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
      * apply utt_wf_extend with (sort := domain_sort).
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
    apply utt_ty_fst with
        (b := shift_term 1 (S cutoff) b).
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    rewrite shift_term_subst_zero.
    apply utt_ty_snd with
        (a := shift_term 1 cutoff a)
        (b := shift_term 1 (S cutoff) b).
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply utt_ty_id with (level := level).
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
    apply utt_ty_refl.
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply utt_ty_conv with
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
    apply utt_ty_prop_lift.
    apply IHHtyping with
        (inserted := inserted)
        (delta := delta).
    + exact Hinsert.
    + exact Hwf.
  - intros cutoff inserted delta Hinsert Hwf.
    simpl.
    apply utt_ty_type_lift with (lower := lower).
    + apply IHHtyping with
          (inserted := inserted)
          (delta := delta).
      * exact Hinsert.
      * exact Hwf.
    + exact l.
Qed.

Corollary utt_has_type_weaken_top :
  forall gamma inserted t a sort,
    utt_wf_context gamma ->
    utt_has_type gamma inserted (utt_sort_term sort) ->
    utt_has_type gamma t a ->
    utt_has_type (inserted :: gamma)
      (shift_term 1 0 t)
      (shift_term 1 0 a).
Proof.
  intros gamma inserted t a sort Hwf Hinserted Htyping.
  apply utt_has_type_weaken with
      (gamma := gamma)
      (inserted := inserted)
      (cutoff := 0).
  - exact Htyping.
  - apply insert_here.
  - apply utt_wf_extend with (sort := sort).
    + exact Hwf.
    + exact Hinserted.
Qed.

Example utt_prop_typing_survives_extension :
  utt_has_type [tProp]
    tProp
    (tUniverse 0).
Proof.
  change (utt_has_type [tProp]
    (shift_term 1 0 tProp)
    (shift_term 1 0 (tUniverse 0))).
  apply utt_has_type_weaken_top with
      (gamma := [])
      (sort := usType 0).
  - apply utt_wf_empty.
  - apply utt_ty_prop.
    apply utt_wf_empty.
  - apply utt_ty_prop.
    apply utt_wf_empty.
Qed.
