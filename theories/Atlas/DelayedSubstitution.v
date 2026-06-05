(** Delayed substitutions for the TDTT clock layer.

    This file starts conservatively: a delayed substitution is represented as
    the operation that instantiates the fresh top clock parameter of a body
    with a concrete well-formed clock.  The interface is derived from the
    existing temporal-substitution theorem, so it can be used before adding a
    dedicated term constructor.
 *)

From Stdlib Require Import List.
From Atlas Require Import Syntax Ops Context DefEq UTT TemporalContext TDTT
  TDTTTemporalSubstitution.

Import ListNotations.

Definition delayed_substitution_context
    (clock : term) (gamma : context) : context :=
  subst_time_context clock 0 (shift_time_context 1 0 gamma).

Definition delayed_substitution_term (clock body : term) : term :=
  subst_time clock 0 body.

Lemma delayed_substitution_supports_tdtt :
  forall clock body,
    supports TDTT clock = true ->
    supports TDTT body = true ->
    supports TDTT (delayed_substitution_term clock body) = true.
Proof.
  intros clock body Hclock Hbody.
  unfold delayed_substitution_term.
  apply supports_subst_time.
  - reflexivity.
  - exact Hclock.
  - exact Hbody.
Qed.

Theorem tdtt_delayed_substitution_preserves_context :
  forall theta gamma clock,
    temporal_wf theta clock ->
    tdtt_wf_context
      (tc_extend theta)
      (shift_time_context 1 0 gamma) ->
    tdtt_wf_context theta
      (delayed_substitution_context clock gamma).
Proof.
  intros theta gamma clock Hclock Hgamma.
  unfold delayed_substitution_context.
  apply tdtt_context_substitute_time_top.
  - exact Hclock.
  - exact Hgamma.
Qed.

Theorem tdtt_delayed_substitution_preserves_typing :
  forall theta gamma clock body a,
    temporal_wf theta clock ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a ->
    tdtt_has_type theta
      (delayed_substitution_context clock gamma)
      (delayed_substitution_term clock body)
      (delayed_substitution_term clock a).
Proof.
  intros theta gamma clock body a Hclock Hbody.
  unfold delayed_substitution_context, delayed_substitution_term.
  apply tdtt_has_type_substitute_time_top.
  - exact Hclock.
  - exact Hbody.
Qed.

Lemma delayed_substitution_context_cancel :
  forall clock gamma,
    delayed_substitution_context clock gamma = gamma.
Proof.
  intros clock gamma.
  unfold delayed_substitution_context.
  induction gamma as [| entry gamma IHgamma]; simpl.
  - reflexivity.
  - rewrite subst_time_shift_cancel.
    rewrite IHgamma.
    reflexivity.
Qed.

Corollary tdtt_delayed_substitution_preserves_typing_in_context :
  forall theta gamma clock body a,
    temporal_wf theta clock ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a ->
    tdtt_has_type theta gamma
      (delayed_substitution_term clock body)
      (delayed_substitution_term clock a).
Proof.
  intros theta gamma clock body a Hclock Hbody.
  rewrite <- (delayed_substitution_context_cancel clock gamma).
  apply tdtt_delayed_substitution_preserves_typing.
  - exact Hclock.
  - exact Hbody.
Qed.

Theorem tdtt_clock_lam_application_has_delayed_type :
  forall theta gamma clock body a sort,
    tdtt_wf_context theta gamma ->
    temporal_wf theta clock ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      a
      (utt_sort_term sort) ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a ->
    tdtt_has_type theta gamma
      (tClockApp (tClockLam body) clock)
      (delayed_substitution_term clock a).
Proof.
  intros theta gamma clock body a sort Hcontext Hclock Ha Hbody.
  unfold delayed_substitution_term.
  apply tdtt_ty_clock_app with (a := a).
  - apply tdtt_ty_clock_lam with (sort := sort).
    + exact Hcontext.
    + exact Ha.
    + exact Hbody.
  - exact Hclock.
Qed.

Theorem tdtt_native_delayed_substitution_has_delayed_type :
  forall theta gamma clock body a,
    tdtt_wf_context theta gamma ->
    temporal_wf theta clock ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a ->
    tdtt_has_type theta gamma
      (tDelayedSubst clock body)
      (delayed_substitution_term clock a).
Proof.
  intros theta gamma clock body a Hcontext Hclock Hbody.
  unfold delayed_substitution_term.
  apply tdtt_ty_delayed_subst.
  - exact Hcontext.
  - exact Hclock.
  - exact Hbody.
Qed.

Lemma clock_beta_is_delayed_substitution :
  forall body clock_index,
    defeq
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (delayed_substitution_term (tTimeVar clock_index) body).
Proof.
  intros body clock_index.
  unfold delayed_substitution_term.
  apply de_clock_beta.
Qed.

Lemma native_delayed_substitution_computes :
  forall body clock_index,
    defeq
      (tDelayedSubst (tTimeVar clock_index) body)
      (delayed_substitution_term (tTimeVar clock_index) body).
Proof.
  intros body clock_index.
  unfold delayed_substitution_term.
  apply de_delayed_subst_compute.
Qed.

Lemma native_delayed_substitution_congruence :
  forall clock clock' body body',
    defeq clock clock' ->
    defeq body body' ->
    defeq
      (tDelayedSubst clock body)
      (tDelayedSubst clock' body').
Proof.
  intros clock clock' body body' Hclock Hbody.
  apply de_delayed_subst.
  - exact Hclock.
  - exact Hbody.
Qed.

Lemma clock_application_agrees_with_native_delayed_substitution :
  forall body clock_index,
    defeq
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (tDelayedSubst (tTimeVar clock_index) body).
Proof.
  intros body clock_index.
  apply de_trans with
    (u := delayed_substitution_term (tTimeVar clock_index) body).
  - apply clock_beta_is_delayed_substitution.
  - apply de_sym.
    apply native_delayed_substitution_computes.
Qed.

Theorem tdtt_clock_application_native_delayed_substitution_typed_agreement :
  forall theta gamma body a clock_index sort,
    tdtt_wf_context theta gamma ->
    temporal_wf theta (tTimeVar clock_index) ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      a
      (utt_sort_term sort) ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a ->
    tdtt_has_type theta gamma
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (delayed_substitution_term (tTimeVar clock_index) a) /\
    tdtt_has_type theta gamma
      (tDelayedSubst (tTimeVar clock_index) body)
      (delayed_substitution_term (tTimeVar clock_index) a) /\
    defeq
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (tDelayedSubst (tTimeVar clock_index) body).
Proof.
  intros theta gamma body a clock_index sort Hcontext Hclock Ha Hbody.
  split.
  - apply tdtt_clock_lam_application_has_delayed_type
      with (sort := sort).
    + exact Hcontext.
    + exact Hclock.
    + exact Ha.
    + exact Hbody.
  - split.
    + apply tdtt_native_delayed_substitution_has_delayed_type.
      * exact Hcontext.
      * exact Hclock.
      * exact Hbody.
    + apply clock_application_agrees_with_native_delayed_substitution.
Qed.

Theorem tdtt_native_delayed_substitution_typed_congruence :
  forall theta gamma clock clock' body body' a a',
    tdtt_wf_context theta gamma ->
    temporal_wf theta clock ->
    temporal_wf theta clock' ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body'
      a' ->
    defeq clock clock' ->
    defeq body body' ->
    tdtt_has_type theta gamma
      (tDelayedSubst clock body)
      (delayed_substitution_term clock a) /\
    tdtt_has_type theta gamma
      (tDelayedSubst clock' body')
      (delayed_substitution_term clock' a') /\
    defeq
      (tDelayedSubst clock body)
      (tDelayedSubst clock' body').
Proof.
  intros theta gamma clock clock' body body' a a'
    Hcontext Hclock Hclock' Hbody Hbody' Hclock_defeq Hbody_defeq.
  split.
  - apply tdtt_native_delayed_substitution_has_delayed_type.
    + exact Hcontext.
    + exact Hclock.
    + exact Hbody.
  - split.
    + apply tdtt_native_delayed_substitution_has_delayed_type.
      * exact Hcontext.
      * exact Hclock'.
      * exact Hbody'.
    + apply native_delayed_substitution_congruence.
      * exact Hclock_defeq.
      * exact Hbody_defeq.
Qed.

Example delayed_substitution_current_clock :
  delayed_substitution_term (tTimeVar 0) (tTimeVar 0) =
  tTimeVar 0.
Proof.
  apply subst_time_var_zero.
Qed.

Example tdtt_delayed_substitution_instantiates_at :
  tdtt_has_type
    (tc_extend tc_empty)
    (delayed_substitution_context (tTimeVar 0) [])
    (delayed_substitution_term
      (tTimeVar 0)
      (tAt tProp (tTimeVar 0)))
    (delayed_substitution_term (tTimeVar 0) (tUniverse 0)).
Proof.
  apply tdtt_delayed_substitution_preserves_typing.
  - apply temporal_wf_var.
    apply temporal_lookup_here.
  - apply tdtt_ty_at with (sort := usType 0).
    + apply tdtt_ty_prop.
      apply tdtt_wf_empty.
    + apply temporal_wf_var.
      apply temporal_lookup_here.
Qed.

Example tdtt_clock_lam_application_uses_delayed_type :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tClockApp (tClockLam tProp) (tTimeVar 0))
    (delayed_substitution_term (tTimeVar 0) (tUniverse 0)).
Proof.
  apply tdtt_clock_lam_application_has_delayed_type
    with (sort := usType 1).
  - apply tdtt_wf_empty.
  - apply temporal_wf_var.
    apply temporal_lookup_here.
  - apply tdtt_ty_universe.
    apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
Qed.

Example tdtt_native_delayed_substitution_uses_delayed_type :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tDelayedSubst (tTimeVar 0) tProp)
    (delayed_substitution_term (tTimeVar 0) (tUniverse 0)).
Proof.
  apply tdtt_native_delayed_substitution_has_delayed_type.
  - apply tdtt_wf_empty.
  - apply temporal_wf_var.
    apply temporal_lookup_here.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
Qed.
