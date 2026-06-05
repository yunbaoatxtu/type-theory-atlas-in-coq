(** Inversion and regularity lemmas for the Atlas judgments.

    These results expose the premises hidden inside well-formed contexts and
    temporal typing constructors.  They are intentionally phrased so they
    remain valid when a derivation ends with conversion.
 *)

From Stdlib Require Import List.
From Atlas Require Import Syntax Ops Context MLTT UTT TemporalContext TDTT.

Import ListNotations.

Lemma mltt_typing_context_wf :
  forall gamma t a,
    has_type gamma t a ->
    wf_context gamma.
Proof.
  intros gamma t a Htyping.
  induction Htyping using has_type_ind'
    with (P := fun _ _ => True);
    eauto.
Qed.

Lemma utt_typing_context_wf :
  forall gamma t a,
    utt_has_type gamma t a ->
    utt_wf_context gamma.
Proof.
  intros gamma t a Htyping.
  induction Htyping using utt_has_type_ind'
    with (P := fun _ _ => True);
    eauto.
Qed.

Lemma tdtt_typing_context_wf :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    tdtt_wf_context theta gamma.
Proof.
  intros theta gamma t a Htyping.
  induction Htyping using tdtt_has_type_ind'
    with (P := fun _ _ _ => True);
    eauto.
Qed.

Lemma mltt_wf_context_cons_inversion :
  forall gamma a,
    wf_context (a :: gamma) ->
    exists level,
      wf_context gamma /\
      has_type gamma a (tUniverse level).
Proof.
  intros gamma a Hcontext.
  inversion Hcontext; subst.
  eauto.
Qed.

Lemma utt_wf_context_cons_inversion :
  forall gamma a,
    utt_wf_context (a :: gamma) ->
    exists sort,
      utt_wf_context gamma /\
      utt_has_type gamma a (utt_sort_term sort).
Proof.
  intros gamma a Hcontext.
  inversion Hcontext; subst.
  eauto.
Qed.

Lemma tdtt_wf_context_cons_inversion :
  forall theta gamma a,
    tdtt_wf_context theta (a :: gamma) ->
    exists sort,
      tdtt_wf_context theta gamma /\
      tdtt_has_type theta gamma a (utt_sort_term sort).
Proof.
  intros theta gamma a Hcontext.
  inversion Hcontext; subst.
  eauto.
Qed.

Lemma temporal_lookup_empty_absurd :
  forall index,
    temporal_lookup tc_empty index ->
    False.
Proof.
  intros index Hlookup.
  inversion Hlookup.
Qed.

Lemma temporal_lookup_extend_inversion :
  forall theta index,
    temporal_lookup (tc_extend theta) index ->
    index = 0 \/
    exists previous,
      index = S previous /\
      temporal_lookup theta previous.
Proof.
  intros theta index Hlookup.
  inversion Hlookup; subst.
  - left.
    reflexivity.
  - right.
    eauto.
Qed.

Lemma temporal_wf_inversion :
  forall theta time,
    temporal_wf theta time ->
    exists index,
      time = tTimeVar index /\
      temporal_lookup theta index.
Proof.
  intros theta time Htime.
  inversion Htime; subst.
  eauto.
Qed.

Lemma temporal_wf_empty_absurd :
  forall time,
    temporal_wf tc_empty time ->
    False.
Proof.
  intros time Htime.
  apply temporal_wf_inversion in Htime.
  destruct Htime as [index [_ Hlookup]].
  apply temporal_lookup_empty_absurd with (index := index).
  exact Hlookup.
Qed.

Lemma tdtt_at_typing_inversion :
  forall theta gamma a time result,
    tdtt_has_type theta gamma (tAt a time) result ->
    exists sort,
      tdtt_has_type theta gamma a (utt_sort_term sort) /\
      temporal_wf theta time.
Proof.
  intros theta gamma a time result Htyping.
  remember (tAt a time) as indexed eqn:Hindexed.
  induction Htyping; inversion Hindexed; subst; eauto.
Qed.

Corollary tdtt_at_typing_temporal_wf :
  forall theta gamma a time result,
    tdtt_has_type theta gamma (tAt a time) result ->
    temporal_wf theta time.
Proof.
  intros theta gamma a time result Htyping.
  apply tdtt_at_typing_inversion in Htyping.
  destruct Htyping as [sort [_ Htime]].
  exact Htime.
Qed.

Lemma tdtt_later_typing_inversion :
  forall theta gamma a result,
    tdtt_has_type theta gamma (tLater a) result ->
    exists sort,
      tdtt_has_type theta gamma a (utt_sort_term sort).
Proof.
  intros theta gamma a result Htyping.
  remember (tLater a) as later eqn:Hlater.
  induction Htyping; inversion Hlater; subst; eauto.
Qed.

Lemma tdtt_next_typing_inversion :
  forall theta gamma t result,
    tdtt_has_type theta gamma (tNext t) result ->
    exists a,
      tdtt_has_type theta gamma t a.
Proof.
  intros theta gamma t result Htyping.
  remember (tNext t) as next eqn:Hnext.
  induction Htyping; inversion Hnext; subst; eauto.
Qed.

Lemma tdtt_fix_typing_inversion :
  forall theta gamma body result,
    tdtt_has_type theta gamma (tFix body) result ->
    exists a sort,
      tdtt_has_type theta gamma a (utt_sort_term sort) /\
      tdtt_has_type theta (tLater a :: gamma) body (shift_term 1 0 a).
Proof.
  intros theta gamma body result Htyping.
  remember (tFix body) as fixpoint eqn:Hfixpoint.
  induction Htyping; inversion Hfixpoint; subst; eauto.
Qed.

Lemma tdtt_later_at_typing_inversion :
  forall theta gamma clock a result,
    tdtt_has_type theta gamma (tLaterAt clock a) result ->
    exists sort,
      temporal_wf theta clock /\
      tdtt_has_type theta gamma a (utt_sort_term sort).
Proof.
  intros theta gamma clock a result Htyping.
  remember (tLaterAt clock a) as later eqn:Hlater.
  induction Htyping; inversion Hlater; subst; eauto.
Qed.

Lemma tdtt_next_at_typing_inversion :
  forall theta gamma clock t result,
    tdtt_has_type theta gamma (tNextAt clock t) result ->
    exists a,
      temporal_wf theta clock /\
      tdtt_has_type theta gamma t a.
Proof.
  intros theta gamma clock t result Htyping.
  remember (tNextAt clock t) as next eqn:Hnext.
  induction Htyping; inversion Hnext; subst; eauto.
Qed.

Lemma tdtt_fix_at_typing_inversion :
  forall theta gamma clock body result,
    tdtt_has_type theta gamma (tFixAt clock body) result ->
    exists a sort,
      temporal_wf theta clock /\
      tdtt_has_type theta gamma a (utt_sort_term sort) /\
      tdtt_has_type theta
        (tLaterAt clock a :: gamma)
        body
        (shift_term 1 0 a).
Proof.
  intros theta gamma clock body result Htyping.
  remember (tFixAt clock body) as fixpoint eqn:Hfixpoint.
  induction Htyping; inversion Hfixpoint; subst; eauto.
Qed.

Lemma tdtt_clock_pi_typing_inversion :
  forall theta gamma a result,
    tdtt_has_type theta gamma (tClockPi a) result ->
    exists sort,
      tdtt_wf_context theta gamma /\
      tdtt_has_type
        (tc_extend theta)
        (shift_time_context 1 0 gamma)
        a
        (utt_sort_term sort).
Proof.
  intros theta gamma a result Htyping.
  remember (tClockPi a) as clock_pi eqn:Hclock_pi.
  induction Htyping; inversion Hclock_pi; subst; eauto.
Qed.

Lemma tdtt_clock_lam_typing_inversion :
  forall theta gamma body result,
    tdtt_has_type theta gamma (tClockLam body) result ->
    exists a sort,
      tdtt_wf_context theta gamma /\
      tdtt_has_type
        (tc_extend theta)
        (shift_time_context 1 0 gamma)
        a
        (utt_sort_term sort) /\
      tdtt_has_type
        (tc_extend theta)
        (shift_time_context 1 0 gamma)
        body
        a.
Proof.
  intros theta gamma body result Htyping.
  remember (tClockLam body) as clock_lam eqn:Hclock_lam.
  induction Htyping; inversion Hclock_lam; subst; eauto.
Qed.

Lemma tdtt_clock_app_typing_inversion :
  forall theta gamma f clock result,
    tdtt_has_type theta gamma (tClockApp f clock) result ->
    exists a,
      tdtt_has_type theta gamma f (tClockPi a) /\
      temporal_wf theta clock.
Proof.
  intros theta gamma f clock result Htyping.
  remember (tClockApp f clock) as clock_app eqn:Hclock_app.
  induction Htyping; inversion Hclock_app; subst; eauto.
Qed.

Lemma tdtt_delayed_subst_typing_inversion :
  forall theta gamma clock body result,
    tdtt_has_type theta gamma (tDelayedSubst clock body) result ->
    exists a,
      tdtt_wf_context theta gamma /\
      temporal_wf theta clock /\
      tdtt_has_type
        (tc_extend theta)
        (shift_time_context 1 0 gamma)
        body
        a.
Proof.
  intros theta gamma clock body result Htyping.
  remember (tDelayedSubst clock body) as delayed eqn:Hdelayed.
  induction Htyping; inversion Hdelayed; subst; eauto.
Qed.

Example tdtt_at_inversion_recovers_current_time :
  temporal_wf
    (tc_extend tc_empty)
    (tTimeVar 0).
Proof.
  apply tdtt_at_typing_temporal_wf with
      (gamma := [])
      (a := tProp)
      (result := tUniverse 0).
  apply tdtt_prop_at_current_time.
Qed.
