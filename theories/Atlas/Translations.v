(** Inclusion translations between the Atlas systems.

    MLTT, UTT, and TDTT share a common syntax representation.  The initial
    translations are therefore identity maps on terms and contexts, while
    typing derivations are lifted through increasingly expressive judgments.
 *)

From Stdlib Require Import Bool List.
From Atlas Require Import Syntax Context DefEq MLTT UTT TemporalContext TDTT.

Import ListNotations.

Definition mltt_to_utt (t : term) : term := t.

Definition utt_to_tdtt (t : term) : term := t.

Definition mltt_to_tdtt (t : term) : term :=
  utt_to_tdtt (mltt_to_utt t).

Definition mltt_context_to_utt (gamma : context) : context := gamma.

Definition utt_context_to_tdtt (gamma : context) : context := gamma.

Definition mltt_context_to_tdtt (gamma : context) : context :=
  utt_context_to_tdtt (mltt_context_to_utt gamma).

Example term_translations_compose :
  forall t,
    mltt_to_tdtt t = utt_to_tdtt (mltt_to_utt t).
Proof. reflexivity. Qed.

Example context_translations_compose :
  forall gamma,
    mltt_context_to_tdtt gamma =
    utt_context_to_tdtt (mltt_context_to_utt gamma).
Proof. reflexivity. Qed.

Lemma mltt_supports_utt :
  forall t,
    supports MLTT t = true ->
    supports UTT (mltt_to_utt t) = true.
Proof.
  intros t Hsupport.
  unfold mltt_to_utt.
  induction t; simpl in *; try discriminate; try reflexivity;
    repeat rewrite Bool.andb_true_iff in *;
    intuition.
Qed.

Lemma utt_supports_tdtt :
  forall t,
    supports UTT t = true ->
    supports TDTT (utt_to_tdtt t) = true.
Proof.
  intros t Hsupport.
  unfold utt_to_tdtt.
  induction t; simpl in *; try discriminate; try reflexivity;
    repeat rewrite Bool.andb_true_iff in *;
    intuition.
Qed.

Corollary mltt_supports_tdtt :
  forall t,
    supports MLTT t = true ->
    supports TDTT (mltt_to_tdtt t) = true.
Proof.
  intros t Hsupport.
  apply utt_supports_tdtt.
  apply mltt_supports_utt.
  exact Hsupport.
Qed.

Theorem mltt_translation_to_utt_preserves_context :
  forall gamma,
    wf_context gamma ->
    utt_wf_context (mltt_context_to_utt gamma).
Proof.
  intros gamma Hgamma.
  apply mltt_context_embeds_in_utt.
  exact Hgamma.
Qed.

Theorem mltt_translation_to_utt_preserves_typing :
  forall gamma t a,
    has_type gamma t a ->
    utt_has_type
      (mltt_context_to_utt gamma)
      (mltt_to_utt t)
      (mltt_to_utt a).
Proof.
  intros gamma t a Htyping.
  apply mltt_typing_embeds_in_utt.
  exact Htyping.
Qed.

Lemma mltt_translation_to_utt_preserves_defeq :
  forall t u,
    defeq t u ->
    defeq (mltt_to_utt t) (mltt_to_utt u).
Proof.
  intros t u Heq.
  exact Heq.
Qed.

Theorem utt_translation_to_tdtt_preserves_context :
  forall theta gamma,
    utt_wf_context gamma ->
    tdtt_wf_context theta (utt_context_to_tdtt gamma).
Proof.
  intros theta gamma Hgamma.
  apply utt_context_embeds_in_tdtt.
  exact Hgamma.
Qed.

Theorem utt_translation_to_tdtt_preserves_typing :
  forall theta gamma t a,
    utt_has_type gamma t a ->
    tdtt_has_type theta
      (utt_context_to_tdtt gamma)
      (utt_to_tdtt t)
      (utt_to_tdtt a).
Proof.
  intros theta gamma t a Htyping.
  apply utt_typing_embeds_in_tdtt.
  exact Htyping.
Qed.

Lemma utt_translation_to_tdtt_preserves_defeq :
  forall t u,
    defeq t u ->
    defeq (utt_to_tdtt t) (utt_to_tdtt u).
Proof.
  intros t u Heq.
  exact Heq.
Qed.

Theorem mltt_embeds_in_tdtt :
  forall theta,
    (forall gamma,
        wf_context gamma ->
        tdtt_wf_context theta gamma) /\
    (forall gamma t a,
        has_type gamma t a ->
        tdtt_has_type theta gamma t a).
Proof.
  intros theta.
  split.
  - intros gamma Hgamma.
    apply utt_context_embeds_in_tdtt.
    apply mltt_context_embeds_in_utt.
    exact Hgamma.
  - intros gamma t a Htyping.
    apply utt_typing_embeds_in_tdtt.
    apply mltt_typing_embeds_in_utt.
    exact Htyping.
Qed.

Corollary mltt_translation_to_tdtt_preserves_context :
  forall theta gamma,
    wf_context gamma ->
    tdtt_wf_context theta (mltt_context_to_tdtt gamma).
Proof.
  intros theta gamma Hgamma.
  apply mltt_embeds_in_tdtt.
  exact Hgamma.
Qed.

Corollary mltt_translation_to_tdtt_preserves_typing :
  forall theta gamma t a,
    has_type gamma t a ->
    tdtt_has_type theta
      (mltt_context_to_tdtt gamma)
      (mltt_to_tdtt t)
      (mltt_to_tdtt a).
Proof.
  intros theta gamma t a Htyping.
  apply mltt_embeds_in_tdtt.
  exact Htyping.
Qed.

Lemma mltt_translation_to_tdtt_preserves_defeq :
  forall t u,
    defeq t u ->
    defeq (mltt_to_tdtt t) (mltt_to_tdtt u).
Proof.
  intros t u Heq.
  apply utt_translation_to_tdtt_preserves_defeq.
  apply mltt_translation_to_utt_preserves_defeq.
  exact Heq.
Qed.

Example mltt_beta_translates_to_utt_defeq :
  defeq
    (mltt_to_utt (tApp (tLam (tVar 0)) (tUniverse 0)))
    (mltt_to_utt (tUniverse 0)).
Proof.
  apply mltt_translation_to_utt_preserves_defeq.
  apply beta_identity_on_universe_zero.
Qed.

Example utt_beta_translates_to_tdtt_defeq :
  defeq
    (utt_to_tdtt (tApp (tLam (tVar 0)) (tUniverse 0)))
    (utt_to_tdtt (tUniverse 0)).
Proof.
  apply utt_translation_to_tdtt_preserves_defeq.
  apply beta_identity_on_universe_zero.
Qed.

Example mltt_identity_application_translates_to_tdtt :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (mltt_to_tdtt (tApp (tLam (tVar 0)) (tUniverse 0)))
    (mltt_to_tdtt (tUniverse 1)).
Proof.
  apply mltt_translation_to_tdtt_preserves_typing.
  apply identity_application_to_universe_zero.
Qed.

Example utt_impredicative_product_translates_to_tdtt :
  tdtt_has_type
    tc_empty
    []
    (utt_to_tdtt (tPi tProp (tVar 0)))
    (utt_to_tdtt tProp).
Proof.
  apply utt_translation_to_tdtt_preserves_typing.
  apply utt_impredicative_product.
Qed.

Example mltt_dependent_function_supports_tdtt :
  supports TDTT
    (mltt_to_tdtt (tPi (tUniverse 0) (tVar 0))) = true.
Proof.
  apply mltt_supports_tdtt.
  reflexivity.
Qed.
