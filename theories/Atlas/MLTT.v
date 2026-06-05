(** Initial typing rules for intensional Martin-Lof Type Theory. *)

From Stdlib Require Import List.
From Atlas Require Import Syntax Ops Context DefEq.

Import ListNotations.

Inductive wf_context : context -> Prop :=
| wf_empty :
    wf_context []
| wf_extend :
    forall gamma a level,
      wf_context gamma ->
      has_type gamma a (tUniverse level) ->
      wf_context (a :: gamma)
with has_type : context -> term -> term -> Prop :=
| ty_universe :
    forall gamma level,
      wf_context gamma ->
      has_type gamma (tUniverse level) (tUniverse (S level))
| ty_var :
    forall gamma index a,
      wf_context gamma ->
      lookup gamma index a ->
      has_type gamma (tVar index) a
| ty_pi :
    forall gamma a b level_a level_b,
      has_type gamma a (tUniverse level_a) ->
      has_type (a :: gamma) b (tUniverse level_b) ->
      has_type gamma (tPi a b) (tUniverse (Nat.max level_a level_b))
| ty_lam :
    forall gamma a body b level_a level_b,
      has_type gamma a (tUniverse level_a) ->
      has_type (a :: gamma) b (tUniverse level_b) ->
      has_type (a :: gamma) body b ->
      has_type gamma (tLam body) (tPi a b)
| ty_app :
    forall gamma f argument a b,
      has_type gamma f (tPi a b) ->
      has_type gamma argument a ->
      has_type gamma (tApp f argument) (subst_term argument 0 b)
| ty_sigma :
    forall gamma a b level_a level_b,
      has_type gamma a (tUniverse level_a) ->
      has_type (a :: gamma) b (tUniverse level_b) ->
      has_type gamma (tSigma a b) (tUniverse (Nat.max level_a level_b))
| ty_pair :
    forall gamma a b first second level_a level_b,
      has_type gamma a (tUniverse level_a) ->
      has_type (a :: gamma) b (tUniverse level_b) ->
      has_type gamma first a ->
      has_type gamma second (subst_term first 0 b) ->
      has_type gamma (tPair first second) (tSigma a b)
| ty_fst :
    forall gamma pair a b,
      has_type gamma pair (tSigma a b) ->
      has_type gamma (tFst pair) a
| ty_snd :
    forall gamma pair a b,
      has_type gamma pair (tSigma a b) ->
      has_type gamma (tSnd pair) (subst_term (tFst pair) 0 b)
| ty_id :
    forall gamma a x y level,
      has_type gamma a (tUniverse level) ->
      has_type gamma x a ->
      has_type gamma y a ->
      has_type gamma (tId a x y) (tUniverse level)
| ty_refl :
    forall gamma a x,
      has_type gamma x a ->
      has_type gamma (tRefl x) (tId a x x)
| ty_conv :
    forall gamma t a b level,
      has_type gamma t a ->
      has_type gamma b (tUniverse level) ->
      defeq a b ->
      has_type gamma t b.

Scheme wf_context_ind' := Induction for wf_context Sort Prop
with has_type_ind' := Induction for has_type Sort Prop.

Combined Scheme mltt_typing_mutind from wf_context_ind', has_type_ind'.

Example empty_context_is_well_formed :
  wf_context [].
Proof. apply wf_empty. Qed.

Example universe_zero_has_type_universe_one :
  has_type [] (tUniverse 0) (tUniverse 1).
Proof.
  apply ty_universe.
  apply wf_empty.
Qed.

Example one_type_context_is_well_formed :
  wf_context [tUniverse 0].
Proof.
  apply wf_extend with (level := 1).
  - apply wf_empty.
  - apply ty_universe.
    apply wf_empty.
Qed.

Lemma identity_function_on_universe :
  forall level,
  has_type []
    (tLam (tVar 0))
    (tPi (tUniverse (S level)) (tUniverse (S level))).
Proof.
  intros level.
  apply ty_lam with (level_a := S (S level)) (level_b := S (S level)).
  - apply ty_universe.
    apply wf_empty.
  - apply ty_universe.
    apply wf_extend with (level := S (S level)).
    + apply wf_empty.
    + apply ty_universe.
      apply wf_empty.
  - apply ty_var.
    + apply wf_extend with (level := S (S level)).
      * apply wf_empty.
      * apply ty_universe.
        apply wf_empty.
    + apply lookup_here.
Qed.

Example identity_function_on_small_types :
  has_type []
    (tLam (tVar 0))
    (tPi (tUniverse 1) (tUniverse 1)).
Proof. apply identity_function_on_universe. Qed.

Lemma identity_application_to_universe :
  forall level,
  has_type []
    (tApp (tLam (tVar 0)) (tUniverse level))
    (tUniverse (S level)).
Proof.
  intros level.
  apply ty_app with
      (a := tUniverse (S level))
      (b := tUniverse (S level)).
  - apply identity_function_on_universe.
  - apply ty_universe.
    apply wf_empty.
Qed.

Example identity_application_to_universe_zero :
  has_type []
    (tApp (tLam (tVar 0)) (tUniverse 0))
    (tUniverse 1).
Proof. apply identity_application_to_universe. Qed.

Example pair_of_small_types :
  has_type []
    (tPair (tUniverse 0) (tUniverse 0))
    (tSigma (tUniverse 1) (tUniverse 1)).
Proof.
  apply ty_pair with (level_a := 2) (level_b := 2).
  - apply ty_universe.
    apply wf_empty.
  - apply ty_universe.
    apply wf_extend with (level := 2).
    + apply wf_empty.
    + apply ty_universe.
      apply wf_empty.
  - apply ty_universe.
    apply wf_empty.
  - apply ty_universe.
    apply wf_empty.
Qed.

Example reflexivity_of_universe_zero :
  has_type []
    (tRefl (tUniverse 0))
    (tId (tUniverse 1) (tUniverse 0) (tUniverse 0)).
Proof.
  apply ty_refl.
  apply ty_universe.
  apply wf_empty.
Qed.

Example universe_zero_has_convertible_type :
  has_type []
    (tUniverse 0)
    (tApp (tLam (tVar 0)) (tUniverse 1)).
Proof.
  apply ty_conv with
      (a := tUniverse 1)
      (level := 2).
  - apply ty_universe.
    apply wf_empty.
  - apply identity_application_to_universe.
  - apply de_sym.
    apply de_beta.
Qed.
