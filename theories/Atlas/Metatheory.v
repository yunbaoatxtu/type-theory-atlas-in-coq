(** Syntax-support reliability for the Atlas typing judgments.

    The shared syntax is intentionally permissive.  These theorems show that
    each typing judgment only derives terms and types admitted by its system
    profile.
 *)

From Stdlib Require Import Bool List.
From Atlas Require Import Syntax Ops Context DefEq MLTT UTT TemporalContext
  TDTT Substitution TDTTSubstitution TDTTTemporalSubstitution Translations
  Inversion DelayedSubstitution.

Import ListNotations.

Definition context_supports (s : system) (gamma : context) : Prop :=
  Forall (fun a => supports s a = true) gamma.

Lemma lookup_supports :
  forall s gamma index a,
    context_supports s gamma ->
    lookup gamma index a ->
    supports s a = true.
Proof.
  intros s gamma index a Hgamma Hlookup.
  induction Hlookup.
  - inversion Hgamma; subst.
    rewrite supports_shift_term.
    assumption.
  - inversion Hgamma; subst.
    rewrite supports_shift_term.
    apply IHHlookup.
    assumption.
Qed.

Lemma utt_sort_supports_utt :
  forall sort,
    supports UTT (utt_sort_term sort) = true.
Proof.
  intros [| level]; reflexivity.
Qed.

Lemma utt_sort_supports_tdtt :
  forall sort,
    supports TDTT (utt_sort_term sort) = true.
Proof.
  intros [| level]; reflexivity.
Qed.

Theorem mltt_typing_supports :
  (forall gamma,
      wf_context gamma ->
      context_supports MLTT gamma) /\
  (forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true).
Proof.
  apply mltt_typing_mutind
    with
      (P := fun gamma _ => context_supports MLTT gamma)
      (P0 := fun _ t a _ =>
        supports MLTT t = true /\ supports MLTT a = true).
  - constructor.
  - intros gamma a level _ Hgamma _ Ha.
    constructor.
    + exact (proj1 Ha).
    + exact Hgamma.
  - intros gamma level _ Hgamma.
    split; reflexivity.
  - intros gamma index a _ Hgamma Hlookup.
    split.
    + reflexivity.
    + apply lookup_supports with
          (gamma := gamma)
          (index := index).
      * exact Hgamma.
      * exact Hlookup.
  - intros gamma a b level_a level_b _ Ha _ Hb.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + reflexivity.
  - intros gamma a body b level_a level_b _ Ha _ Hb _ Hbody.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    destruct Hbody as [Hbody _].
    split.
    + exact Hbody.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
  - intros gamma f argument a b _ Hf _ Hargument.
    destruct Hf as [Hf Hpi].
    destruct Hargument as [Hargument _].
    simpl in Hpi.
    apply Bool.andb_true_iff in Hpi as [_ Hb].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + apply supports_subst_term.
      * exact Hargument.
      * exact Hb.
  - intros gamma a b level_a level_b _ Ha _ Hb.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + reflexivity.
  - intros gamma a b first second level_a level_b
      _ Ha _ Hb _ Hfirst _ Hsecond.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    destruct Hfirst as [Hfirst _].
    destruct Hsecond as [Hsecond _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
  - intros gamma pair a b _ Hpair.
    destruct Hpair as [Hpair Hsigma].
    simpl in Hsigma.
    apply Bool.andb_true_iff in Hsigma as [Ha _].
    split.
    + exact Hpair.
    + exact Ha.
  - intros gamma pair a b _ Hpair.
    destruct Hpair as [Hpair Hsigma].
    simpl in Hsigma.
    apply Bool.andb_true_iff in Hsigma as [_ Hb].
    split.
    + exact Hpair.
    + apply supports_subst_term.
      * exact Hpair.
      * exact Hb.
  - intros gamma a x y level _ Ha _ Hx _ Hy.
    destruct Ha as [Ha _].
    destruct Hx as [Hx _].
    destruct Hy as [Hy _].
    split.
    + simpl.
      rewrite Ha, Hx, Hy.
      reflexivity.
    + reflexivity.
  - intros gamma a x _ Hx.
    destruct Hx as [Hx Ha].
    split.
    + exact Hx.
    + simpl.
      rewrite Ha, Hx.
      reflexivity.
  - intros gamma t a b level _ Ht _ Hb Heq.
    destruct Ht as [Ht _].
    destruct Hb as [Hb _].
    split; assumption.
Qed.

Corollary mltt_typable_supports :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\ supports MLTT a = true.
Proof.
  apply mltt_typing_supports.
Qed.

Theorem utt_typing_supports :
  (forall gamma,
      utt_wf_context gamma ->
      context_supports UTT gamma) /\
  (forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true).
Proof.
  apply utt_typing_mutind
    with
      (P := fun gamma _ => context_supports UTT gamma)
      (P0 := fun _ t a _ =>
        supports UTT t = true /\ supports UTT a = true).
  - constructor.
  - intros gamma a sort _ Hgamma _ Ha.
    constructor.
    + exact (proj1 Ha).
    + exact Hgamma.
  - intros gamma _ Hgamma.
    split; reflexivity.
  - intros gamma level _ Hgamma.
    split; reflexivity.
  - intros gamma index a _ Hgamma Hlookup.
    split.
    + reflexivity.
    + apply lookup_supports with
          (gamma := gamma)
          (index := index).
      * exact Hgamma.
      * exact Hlookup.
  - intros gamma a b domain_sort codomain_sort _ Ha _ Hb.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + apply utt_sort_supports_utt.
  - intros gamma a body b domain_sort codomain_sort _ Ha _ Hb _ Hbody.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    destruct Hbody as [Hbody _].
    split.
    + exact Hbody.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
  - intros gamma f argument a b _ Hf _ Hargument.
    destruct Hf as [Hf Hpi].
    destruct Hargument as [Hargument _].
    simpl in Hpi.
    apply Bool.andb_true_iff in Hpi as [_ Hb].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + apply supports_subst_term.
      * exact Hargument.
      * exact Hb.
  - intros gamma a b domain_sort level_b _ Ha _ Hb.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + reflexivity.
  - intros gamma a b first second domain_sort level_b
      _ Ha _ Hb _ Hfirst _ Hsecond.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    destruct Hfirst as [Hfirst _].
    destruct Hsecond as [Hsecond _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
  - intros gamma pair a b _ Hpair.
    destruct Hpair as [Hpair Hsigma].
    simpl in Hsigma.
    apply Bool.andb_true_iff in Hsigma as [Ha _].
    split.
    + exact Hpair.
    + exact Ha.
  - intros gamma pair a b _ Hpair.
    destruct Hpair as [Hpair Hsigma].
    simpl in Hsigma.
    apply Bool.andb_true_iff in Hsigma as [_ Hb].
    split.
    + exact Hpair.
    + apply supports_subst_term.
      * exact Hpair.
      * exact Hb.
  - intros gamma a x y level _ Ha _ Hx _ Hy.
    destruct Ha as [Ha _].
    destruct Hx as [Hx _].
    destruct Hy as [Hy _].
    split.
    + simpl.
      rewrite Ha, Hx, Hy.
      reflexivity.
    + reflexivity.
  - intros gamma a x _ Hx.
    destruct Hx as [Hx Ha].
    split.
    + exact Hx.
    + simpl.
      rewrite Ha, Hx.
      reflexivity.
  - intros gamma t a b sort _ Ht _ Hb Heq.
    destruct Ht as [Ht _].
    destruct Hb as [Hb _].
    split; assumption.
  - intros gamma proposition level _ Hproposition.
    destruct Hproposition as [Hproposition _].
    split.
    + exact Hproposition.
    + reflexivity.
  - intros gamma a lower upper _ Ha Hle.
    destruct Ha as [Ha _].
    split.
    + exact Ha.
    + reflexivity.
Qed.

Corollary utt_typable_supports :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\ supports UTT a = true.
Proof.
  apply utt_typing_supports.
Qed.

Theorem tdtt_typing_supports :
  (forall theta gamma,
        tdtt_wf_context theta gamma ->
        context_supports TDTT gamma) /\
    (forall theta gamma t a,
        tdtt_has_type theta gamma t a ->
        supports TDTT t = true /\
        supports TDTT a = true).
Proof.
  apply tdtt_typing_mutind
    with
      (P := fun _ gamma _ => context_supports TDTT gamma)
      (P0 := fun _ _ t a _ =>
        supports TDTT t = true /\ supports TDTT a = true).
  - intros theta.
    constructor.
  - intros theta gamma a sort _ Hgamma _ Ha.
    constructor.
    + exact (proj1 Ha).
    + exact Hgamma.
  - intros theta gamma _ Hgamma.
    split; reflexivity.
  - intros theta gamma level _ Hgamma.
    split; reflexivity.
  - intros theta gamma index a _ Hgamma Hlookup.
    split.
    + reflexivity.
    + apply lookup_supports with
          (gamma := gamma)
          (index := index).
      * exact Hgamma.
      * exact Hlookup.
  - intros theta gamma a b domain_sort codomain_sort _ Ha _ Hb.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + apply utt_sort_supports_tdtt.
  - intros theta gamma a body b domain_sort codomain_sort _ Ha _ Hb _ Hbody.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    destruct Hbody as [Hbody _].
    split.
    + exact Hbody.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
  - intros theta gamma f argument a b _ Hf _ Hargument.
    destruct Hf as [Hf Hpi].
    destruct Hargument as [Hargument _].
    simpl in Hpi.
    apply Bool.andb_true_iff in Hpi as [_ Hb].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + apply supports_subst_term.
      * exact Hargument.
      * exact Hb.
  - intros theta gamma a b domain_sort level_b _ Ha _ Hb.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + reflexivity.
  - intros theta gamma a b first second domain_sort level_b
      _ Ha _ Hb _ Hfirst _ Hsecond.
    destruct Ha as [Ha _].
    destruct Hb as [Hb _].
    destruct Hfirst as [Hfirst _].
    destruct Hsecond as [Hsecond _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
    + simpl.
      apply Bool.andb_true_iff.
      split; assumption.
  - intros theta gamma pair a b _ Hpair.
    destruct Hpair as [Hpair Hsigma].
    simpl in Hsigma.
    apply Bool.andb_true_iff in Hsigma as [Ha _].
    split.
    + exact Hpair.
    + exact Ha.
  - intros theta gamma pair a b _ Hpair.
    destruct Hpair as [Hpair Hsigma].
    simpl in Hsigma.
    apply Bool.andb_true_iff in Hsigma as [_ Hb].
    split.
    + exact Hpair.
    + apply supports_subst_term.
      * exact Hpair.
      * exact Hb.
  - intros theta gamma a x y level _ Ha _ Hx _ Hy.
    destruct Ha as [Ha _].
    destruct Hx as [Hx _].
    destruct Hy as [Hy _].
    split.
    + simpl.
      rewrite Ha, Hx, Hy.
      reflexivity.
    + reflexivity.
  - intros theta gamma a x _ Hx.
    destruct Hx as [Hx Ha].
    split.
    + exact Hx.
    + simpl.
      rewrite Ha, Hx.
      reflexivity.
  - intros theta gamma t a b sort _ Ht _ Hb Heq.
    destruct Ht as [Ht _].
    destruct Hb as [Hb _].
    split; assumption.
  - intros theta gamma proposition level _ Hproposition.
    destruct Hproposition as [Hproposition _].
    split.
    + exact Hproposition.
    + reflexivity.
  - intros theta gamma a lower upper _ Ha Hle.
    destruct Ha as [Ha _].
    split.
    + exact Ha.
    + reflexivity.
  - intros theta gamma a time sort _ Ha Htime.
    destruct Ha as [Ha _].
    split.
    + simpl.
      apply Bool.andb_true_iff.
      split.
      * exact Ha.
      * apply temporal_wf_supports_tdtt with (theta := theta).
        exact Htime.
    + apply utt_sort_supports_tdtt.
  - intros theta gamma a sort _ Ha.
    destruct Ha as [Ha _].
    split.
    + exact Ha.
    + apply utt_sort_supports_tdtt.
  - intros theta gamma t a _ Ht.
    destruct Ht as [Ht Ha].
    split.
    + exact Ht.
    + exact Ha.
  - intros theta gamma a body sort _ Ha _ Hbody.
    destruct Ha as [Ha _].
    destruct Hbody as [Hbody _].
    split.
    + exact Hbody.
    + exact Ha.
  - intros theta gamma clock a sort Hclock _ Ha.
    destruct Ha as [Ha _].
    split.
    + simpl.
      rewrite Ha.
      rewrite (temporal_wf_supports_tdtt theta clock Hclock).
      reflexivity.
    + apply utt_sort_supports_tdtt.
  - intros theta gamma clock t a Hclock _ Ht.
    destruct Ht as [Ht Ha].
    pose proof (temporal_wf_supports_tdtt theta clock Hclock) as Hclock_support.
    split.
    + simpl.
      rewrite Hclock_support, Ht.
      reflexivity.
    + simpl.
      rewrite Hclock_support, Ha.
      reflexivity.
  - intros theta gamma clock a body sort Hclock _ Ha _ Hbody.
    destruct Ha as [Ha _].
    destruct Hbody as [Hbody _].
    pose proof (temporal_wf_supports_tdtt theta clock Hclock) as Hclock_support.
    split.
    + simpl.
      rewrite Hclock_support, Hbody.
      reflexivity.
    + exact Ha.
  - intros theta gamma a sort _ Hgamma _ Ha.
    destruct Ha as [Ha _].
    split.
    + simpl.
      exact Ha.
    + apply utt_sort_supports_tdtt.
  - intros theta gamma body a sort _ Hgamma _ Ha _ Hbody.
    destruct Ha as [Ha _].
    destruct Hbody as [Hbody _].
    split.
    + simpl.
      exact Hbody.
    + simpl.
      exact Ha.
  - intros theta gamma f clock a _ Hf Hclock.
    destruct Hf as [Hf Hpi].
    simpl in Hpi.
    pose proof (temporal_wf_supports_tdtt theta clock Hclock) as Hclock_support.
    split.
    + simpl.
      rewrite Hf, Hclock_support.
      reflexivity.
    + apply supports_subst_time.
      * reflexivity.
      * exact Hclock_support.
      * exact Hpi.
  - intros theta gamma clock body a _ Hgamma Hclock _ Hbody.
    destruct Hbody as [Hbody Ha].
    pose proof (temporal_wf_supports_tdtt theta clock Hclock) as Hclock_support.
    split.
    + simpl.
      rewrite Hclock_support, Hbody.
      reflexivity.
    + apply supports_subst_time.
      * reflexivity.
      * exact Hclock_support.
      * exact Ha.
Qed.

Corollary tdtt_typable_supports :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\ supports TDTT a = true.
Proof.
  intros theta.
  apply tdtt_typing_supports.
Qed.

Example mltt_typing_never_derives_temporal_syntax :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true.
Proof.
  intros gamma t a Htyping.
  apply mltt_typable_supports in Htyping.
  exact (proj1 Htyping).
Qed.

Example utt_typing_never_derives_temporal_syntax :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true.
Proof.
  intros gamma t a Htyping.
  apply utt_typable_supports in Htyping.
  exact (proj1 Htyping).
Qed.

Example tdtt_at_term_is_supported :
  supports TDTT (tAt tProp (tTimeVar 0)) = true.
Proof. reflexivity. Qed.

Lemma mltt_context_supports_utt_translation :
  forall gamma,
    context_supports MLTT gamma ->
    context_supports UTT (mltt_context_to_utt gamma).
Proof.
  intros gamma Hgamma.
  unfold mltt_context_to_utt.
  induction Hgamma.
  - constructor.
  - constructor.
    + apply mltt_supports_utt.
      exact H.
    + exact IHHgamma.
Qed.

Lemma utt_context_supports_tdtt_translation :
  forall gamma,
    context_supports UTT gamma ->
    context_supports TDTT (utt_context_to_tdtt gamma).
Proof.
  intros gamma Hgamma.
  unfold utt_context_to_tdtt.
  induction Hgamma.
  - constructor.
  - constructor.
    + apply utt_supports_tdtt.
      exact H.
    + exact IHHgamma.
Qed.

Corollary mltt_context_supports_tdtt_translation :
  forall gamma,
    context_supports MLTT gamma ->
    context_supports TDTT (mltt_context_to_tdtt gamma).
Proof.
  intros gamma Hgamma.
  unfold mltt_context_to_tdtt.
  apply utt_context_supports_tdtt_translation.
  apply mltt_context_supports_utt_translation.
  exact Hgamma.
Qed.

Theorem mltt_translation_to_utt_typing_reliable :
  forall gamma t a,
    has_type gamma t a ->
    utt_has_type
      (mltt_context_to_utt gamma)
      (mltt_to_utt t)
      (mltt_to_utt a) /\
    supports UTT (mltt_to_utt t) = true /\
    supports UTT (mltt_to_utt a) = true.
Proof.
  intros gamma t a Htyping.
  pose proof (mltt_translation_to_utt_preserves_typing
    gamma t a Htyping) as Htranslated.
  pose proof (mltt_typable_supports gamma t a Htyping)
    as [Ht Ha].
  split.
  - exact Htranslated.
  - split.
    + apply mltt_supports_utt.
      exact Ht.
    + apply mltt_supports_utt.
      exact Ha.
Qed.

Theorem utt_translation_to_tdtt_typing_reliable :
  forall theta gamma t a,
    utt_has_type gamma t a ->
    tdtt_has_type theta
      (utt_context_to_tdtt gamma)
      (utt_to_tdtt t)
      (utt_to_tdtt a) /\
    supports TDTT (utt_to_tdtt t) = true /\
    supports TDTT (utt_to_tdtt a) = true.
Proof.
  intros theta gamma t a Htyping.
  pose proof (utt_translation_to_tdtt_preserves_typing
    theta gamma t a Htyping) as Htranslated.
  pose proof (utt_typable_supports gamma t a Htyping)
    as [Ht Ha].
  split.
  - exact Htranslated.
  - split.
    + apply utt_supports_tdtt.
      exact Ht.
    + apply utt_supports_tdtt.
      exact Ha.
Qed.

Corollary mltt_translation_to_tdtt_typing_reliable :
  forall theta gamma t a,
    has_type gamma t a ->
    tdtt_has_type theta
      (mltt_context_to_tdtt gamma)
      (mltt_to_tdtt t)
      (mltt_to_tdtt a) /\
    supports TDTT (mltt_to_tdtt t) = true /\
    supports TDTT (mltt_to_tdtt a) = true.
Proof.
  intros theta gamma t a Htyping.
  pose proof (mltt_translation_to_tdtt_preserves_typing
    theta gamma t a Htyping) as Htranslated.
  pose proof (mltt_typable_supports gamma t a Htyping)
    as [Ht Ha].
  split.
  - exact Htranslated.
  - split.
    + apply mltt_supports_tdtt.
      exact Ht.
    + apply mltt_supports_tdtt.
      exact Ha.
Qed.

Record mltt_to_utt_translation_regular
    (gamma : context) (t a : term) : Prop := {
  mltt_to_utt_regular_context_wf :
    utt_wf_context (mltt_context_to_utt gamma);
  mltt_to_utt_regular_context_support :
    context_supports UTT (mltt_context_to_utt gamma);
  mltt_to_utt_regular_typing :
    utt_has_type
      (mltt_context_to_utt gamma)
      (mltt_to_utt t)
      (mltt_to_utt a);
  mltt_to_utt_regular_term_support :
    supports UTT (mltt_to_utt t) = true;
  mltt_to_utt_regular_type_support :
    supports UTT (mltt_to_utt a) = true
}.

Record utt_to_tdtt_translation_regular
    (theta : temporal_context) (gamma : context) (t a : term) : Prop := {
  utt_to_tdtt_regular_context_wf :
    tdtt_wf_context theta (utt_context_to_tdtt gamma);
  utt_to_tdtt_regular_context_support :
    context_supports TDTT (utt_context_to_tdtt gamma);
  utt_to_tdtt_regular_typing :
    tdtt_has_type theta
      (utt_context_to_tdtt gamma)
      (utt_to_tdtt t)
      (utt_to_tdtt a);
  utt_to_tdtt_regular_term_support :
    supports TDTT (utt_to_tdtt t) = true;
  utt_to_tdtt_regular_type_support :
    supports TDTT (utt_to_tdtt a) = true
}.

Record mltt_to_tdtt_translation_regular
    (theta : temporal_context) (gamma : context) (t a : term) : Prop := {
  mltt_to_tdtt_regular_context_wf :
    tdtt_wf_context theta (mltt_context_to_tdtt gamma);
  mltt_to_tdtt_regular_context_support :
    context_supports TDTT (mltt_context_to_tdtt gamma);
  mltt_to_tdtt_regular_typing :
    tdtt_has_type theta
      (mltt_context_to_tdtt gamma)
      (mltt_to_tdtt t)
      (mltt_to_tdtt a);
  mltt_to_tdtt_regular_term_support :
    supports TDTT (mltt_to_tdtt t) = true;
  mltt_to_tdtt_regular_type_support :
    supports TDTT (mltt_to_tdtt a) = true
}.

Theorem mltt_translation_to_utt_regular :
  forall gamma t a,
    has_type gamma t a ->
    mltt_to_utt_translation_regular gamma t a.
Proof.
  intros gamma t a Htyping.
  pose proof (mltt_typing_context_wf gamma t a Htyping) as Hcontext.
  pose proof (mltt_translation_to_utt_typing_reliable
    gamma t a Htyping) as [Htranslated [Ht Ha]].
  constructor.
  - apply mltt_translation_to_utt_preserves_context.
    exact Hcontext.
  - apply mltt_context_supports_utt_translation.
    destruct mltt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - exact Htranslated.
  - exact Ht.
  - exact Ha.
Qed.

Theorem utt_translation_to_tdtt_regular :
  forall theta gamma t a,
    utt_has_type gamma t a ->
    utt_to_tdtt_translation_regular theta gamma t a.
Proof.
  intros theta gamma t a Htyping.
  pose proof (utt_typing_context_wf gamma t a Htyping) as Hcontext.
  pose proof (utt_translation_to_tdtt_typing_reliable
    theta gamma t a Htyping) as [Htranslated [Ht Ha]].
  constructor.
  - apply utt_translation_to_tdtt_preserves_context.
    exact Hcontext.
  - apply utt_context_supports_tdtt_translation.
    destruct utt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - exact Htranslated.
  - exact Ht.
  - exact Ha.
Qed.

Corollary mltt_translation_to_tdtt_regular :
  forall theta gamma t a,
    has_type gamma t a ->
    mltt_to_tdtt_translation_regular theta gamma t a.
Proof.
  intros theta gamma t a Htyping.
  pose proof (mltt_typing_context_wf gamma t a Htyping) as Hcontext.
  pose proof (mltt_translation_to_tdtt_typing_reliable
    theta gamma t a Htyping) as [Htranslated [Ht Ha]].
  constructor.
  - apply mltt_translation_to_tdtt_preserves_context.
    exact Hcontext.
  - apply mltt_context_supports_tdtt_translation.
    destruct mltt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - exact Htranslated.
  - exact Ht.
  - exact Ha.
Qed.

(** Since [defeq] is shared and untyped, its translation regularity states
    explicit source-support assumptions for both sides of the equality. *)
Record mltt_to_utt_defeq_regular (t u : term) : Prop := {
  mltt_to_utt_regular_defeq :
    defeq (mltt_to_utt t) (mltt_to_utt u);
  mltt_to_utt_regular_left_support :
    supports UTT (mltt_to_utt t) = true;
  mltt_to_utt_regular_right_support :
    supports UTT (mltt_to_utt u) = true
}.

Record utt_to_tdtt_defeq_regular (t u : term) : Prop := {
  utt_to_tdtt_regular_defeq :
    defeq (utt_to_tdtt t) (utt_to_tdtt u);
  utt_to_tdtt_regular_left_support :
    supports TDTT (utt_to_tdtt t) = true;
  utt_to_tdtt_regular_right_support :
    supports TDTT (utt_to_tdtt u) = true
}.

Record mltt_to_tdtt_defeq_regular (t u : term) : Prop := {
  mltt_to_tdtt_regular_defeq :
    defeq (mltt_to_tdtt t) (mltt_to_tdtt u);
  mltt_to_tdtt_regular_left_support :
    supports TDTT (mltt_to_tdtt t) = true;
  mltt_to_tdtt_regular_right_support :
    supports TDTT (mltt_to_tdtt u) = true
}.

Theorem mltt_translation_to_utt_defeq_regular :
  forall t u,
    defeq t u ->
    supports MLTT t = true ->
    supports MLTT u = true ->
    mltt_to_utt_defeq_regular t u.
Proof.
  intros t u Heq Ht Hu.
  constructor.
  - apply mltt_translation_to_utt_preserves_defeq.
    exact Heq.
  - apply mltt_supports_utt.
    exact Ht.
  - apply mltt_supports_utt.
    exact Hu.
Qed.

Theorem utt_translation_to_tdtt_defeq_regular :
  forall t u,
    defeq t u ->
    supports UTT t = true ->
    supports UTT u = true ->
    utt_to_tdtt_defeq_regular t u.
Proof.
  intros t u Heq Ht Hu.
  constructor.
  - apply utt_translation_to_tdtt_preserves_defeq.
    exact Heq.
  - apply utt_supports_tdtt.
    exact Ht.
  - apply utt_supports_tdtt.
    exact Hu.
Qed.

Corollary mltt_translation_to_tdtt_defeq_regular :
  forall t u,
    defeq t u ->
    supports MLTT t = true ->
    supports MLTT u = true ->
    mltt_to_tdtt_defeq_regular t u.
Proof.
  intros t u Heq Ht Hu.
  constructor.
  - apply mltt_translation_to_tdtt_preserves_defeq.
    exact Heq.
  - apply mltt_supports_tdtt.
    exact Ht.
  - apply mltt_supports_tdtt.
    exact Hu.
Qed.

Record mltt_typed_conversion_regular
    (gamma : context) (t a b : term) (level : nat) : Prop := {
  mltt_conversion_regular_context_wf :
    wf_context gamma;
  mltt_conversion_regular_context_support :
    context_supports MLTT gamma;
  mltt_conversion_regular_source_typing :
    has_type gamma t a;
  mltt_conversion_regular_target_type :
    has_type gamma b (tUniverse level);
  mltt_conversion_regular_defeq :
    defeq a b;
  mltt_conversion_regular_converted_typing :
    has_type gamma t b;
  mltt_conversion_regular_term_support :
    supports MLTT t = true;
  mltt_conversion_regular_source_type_support :
    supports MLTT a = true;
  mltt_conversion_regular_target_type_support :
    supports MLTT b = true
}.

Record utt_typed_conversion_regular
    (gamma : context) (t a b : term) (sort : utt_sort) : Prop := {
  utt_conversion_regular_context_wf :
    utt_wf_context gamma;
  utt_conversion_regular_context_support :
    context_supports UTT gamma;
  utt_conversion_regular_source_typing :
    utt_has_type gamma t a;
  utt_conversion_regular_target_type :
    utt_has_type gamma b (utt_sort_term sort);
  utt_conversion_regular_defeq :
    defeq a b;
  utt_conversion_regular_converted_typing :
    utt_has_type gamma t b;
  utt_conversion_regular_term_support :
    supports UTT t = true;
  utt_conversion_regular_source_type_support :
    supports UTT a = true;
  utt_conversion_regular_target_type_support :
    supports UTT b = true
}.

Record tdtt_typed_conversion_regular
    (theta : temporal_context) (gamma : context)
    (t a b : term) (sort : utt_sort) : Prop := {
  tdtt_conversion_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_conversion_regular_context_support :
    context_supports TDTT gamma;
  tdtt_conversion_regular_source_typing :
    tdtt_has_type theta gamma t a;
  tdtt_conversion_regular_target_type :
    tdtt_has_type theta gamma b (utt_sort_term sort);
  tdtt_conversion_regular_defeq :
    defeq a b;
  tdtt_conversion_regular_converted_typing :
    tdtt_has_type theta gamma t b;
  tdtt_conversion_regular_term_support :
    supports TDTT t = true;
  tdtt_conversion_regular_source_type_support :
    supports TDTT a = true;
  tdtt_conversion_regular_target_type_support :
    supports TDTT b = true
}.

Theorem mltt_typed_conversion_is_regular :
  forall gamma t a b level,
    has_type gamma t a ->
    has_type gamma b (tUniverse level) ->
    defeq a b ->
    mltt_typed_conversion_regular gamma t a b level.
Proof.
  intros gamma t a b level Htyping Htarget Heq.
  pose proof (mltt_typing_context_wf gamma t a Htyping) as Hcontext.
  pose proof (mltt_typable_supports gamma t a Htyping)
    as [Ht Ha].
  pose proof (mltt_typable_supports gamma b (tUniverse level) Htarget)
    as [Hb _].
  constructor.
  - exact Hcontext.
  - destruct mltt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - exact Htyping.
  - exact Htarget.
  - exact Heq.
  - apply ty_conv with (a := a) (level := level).
    + exact Htyping.
    + exact Htarget.
    + exact Heq.
  - exact Ht.
  - exact Ha.
  - exact Hb.
Qed.

Theorem utt_typed_conversion_is_regular :
  forall gamma t a b sort,
    utt_has_type gamma t a ->
    utt_has_type gamma b (utt_sort_term sort) ->
    defeq a b ->
    utt_typed_conversion_regular gamma t a b sort.
Proof.
  intros gamma t a b sort Htyping Htarget Heq.
  pose proof (utt_typing_context_wf gamma t a Htyping) as Hcontext.
  pose proof (utt_typable_supports gamma t a Htyping)
    as [Ht Ha].
  pose proof (utt_typable_supports gamma b (utt_sort_term sort) Htarget)
    as [Hb _].
  constructor.
  - exact Hcontext.
  - destruct utt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - exact Htyping.
  - exact Htarget.
  - exact Heq.
  - apply utt_ty_conv with (a := a) (sort := sort).
    + exact Htyping.
    + exact Htarget.
    + exact Heq.
  - exact Ht.
  - exact Ha.
  - exact Hb.
Qed.

Theorem tdtt_typed_conversion_is_regular :
  forall theta gamma t a b sort,
    tdtt_has_type theta gamma t a ->
    tdtt_has_type theta gamma b (utt_sort_term sort) ->
    defeq a b ->
    tdtt_typed_conversion_regular theta gamma t a b sort.
Proof.
  intros theta gamma t a b sort Htyping Htarget Heq.
  pose proof (tdtt_typing_context_wf theta gamma t a Htyping) as Hcontext.
  pose proof (tdtt_typable_supports theta gamma t a Htyping)
    as [Ht Ha].
  pose proof (tdtt_typable_supports
    theta gamma b (utt_sort_term sort) Htarget) as [Hb _].
  constructor.
  - exact Hcontext.
  - destruct tdtt_typing_supports as [Hcontext_support _].
    apply (Hcontext_support theta gamma).
    exact Hcontext.
  - exact Htyping.
  - exact Htarget.
  - exact Heq.
  - apply tdtt_ty_conv with (a := a) (sort := sort).
    + exact Htyping.
    + exact Htarget.
    + exact Heq.
  - exact Ht.
  - exact Ha.
  - exact Hb.
Qed.

Record mltt_typed_defeq_regular
    (gamma : context) (a b : term)
    (left_level right_level : nat) : Prop := {
  mltt_typed_defeq_regular_context_wf :
    wf_context gamma;
  mltt_typed_defeq_regular_context_support :
    context_supports MLTT gamma;
  mltt_typed_defeq_regular_left_type :
    has_type gamma a (tUniverse left_level);
  mltt_typed_defeq_regular_right_type :
    has_type gamma b (tUniverse right_level);
  mltt_typed_defeq_regular_defeq :
    defeq a b;
  mltt_typed_defeq_regular_left_support :
    supports MLTT a = true;
  mltt_typed_defeq_regular_right_support :
    supports MLTT b = true
}.

Record utt_typed_defeq_regular
    (gamma : context) (a b : term)
    (left_sort right_sort : utt_sort) : Prop := {
  utt_typed_defeq_regular_context_wf :
    utt_wf_context gamma;
  utt_typed_defeq_regular_context_support :
    context_supports UTT gamma;
  utt_typed_defeq_regular_left_type :
    utt_has_type gamma a (utt_sort_term left_sort);
  utt_typed_defeq_regular_right_type :
    utt_has_type gamma b (utt_sort_term right_sort);
  utt_typed_defeq_regular_defeq :
    defeq a b;
  utt_typed_defeq_regular_left_support :
    supports UTT a = true;
  utt_typed_defeq_regular_right_support :
    supports UTT b = true
}.

Record tdtt_typed_defeq_regular
    (theta : temporal_context) (gamma : context) (a b : term)
    (left_sort right_sort : utt_sort) : Prop := {
  tdtt_typed_defeq_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_typed_defeq_regular_context_support :
    context_supports TDTT gamma;
  tdtt_typed_defeq_regular_left_type :
    tdtt_has_type theta gamma a (utt_sort_term left_sort);
  tdtt_typed_defeq_regular_right_type :
    tdtt_has_type theta gamma b (utt_sort_term right_sort);
  tdtt_typed_defeq_regular_defeq :
    defeq a b;
  tdtt_typed_defeq_regular_left_support :
    supports TDTT a = true;
  tdtt_typed_defeq_regular_right_support :
    supports TDTT b = true
}.

Theorem mltt_typed_defeq_is_regular :
  forall gamma a b left_level right_level,
    has_type gamma a (tUniverse left_level) ->
    has_type gamma b (tUniverse right_level) ->
    defeq a b ->
    mltt_typed_defeq_regular gamma a b left_level right_level.
Proof.
  intros gamma a b left_level right_level Hleft Hright Heq.
  pose proof (mltt_typing_context_wf
    gamma a (tUniverse left_level) Hleft) as Hcontext.
  pose proof (mltt_typable_supports
    gamma a (tUniverse left_level) Hleft) as [Ha _].
  pose proof (mltt_typable_supports
    gamma b (tUniverse right_level) Hright) as [Hb _].
  constructor.
  - exact Hcontext.
  - destruct mltt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - exact Hleft.
  - exact Hright.
  - exact Heq.
  - exact Ha.
  - exact Hb.
Qed.

Theorem utt_typed_defeq_is_regular :
  forall gamma a b left_sort right_sort,
    utt_has_type gamma a (utt_sort_term left_sort) ->
    utt_has_type gamma b (utt_sort_term right_sort) ->
    defeq a b ->
    utt_typed_defeq_regular gamma a b left_sort right_sort.
Proof.
  intros gamma a b left_sort right_sort Hleft Hright Heq.
  pose proof (utt_typing_context_wf
    gamma a (utt_sort_term left_sort) Hleft) as Hcontext.
  pose proof (utt_typable_supports
    gamma a (utt_sort_term left_sort) Hleft) as [Ha _].
  pose proof (utt_typable_supports
    gamma b (utt_sort_term right_sort) Hright) as [Hb _].
  constructor.
  - exact Hcontext.
  - destruct utt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - exact Hleft.
  - exact Hright.
  - exact Heq.
  - exact Ha.
  - exact Hb.
Qed.

Theorem tdtt_typed_defeq_is_regular :
  forall theta gamma a b left_sort right_sort,
    tdtt_has_type theta gamma a (utt_sort_term left_sort) ->
    tdtt_has_type theta gamma b (utt_sort_term right_sort) ->
    defeq a b ->
    tdtt_typed_defeq_regular theta gamma a b left_sort right_sort.
Proof.
  intros theta gamma a b left_sort right_sort Hleft Hright Heq.
  pose proof (tdtt_typing_context_wf
    theta gamma a (utt_sort_term left_sort) Hleft) as Hcontext.
  pose proof (tdtt_typable_supports
    theta gamma a (utt_sort_term left_sort) Hleft) as [Ha _].
  pose proof (tdtt_typable_supports
    theta gamma b (utt_sort_term right_sort) Hright) as [Hb _].
  constructor.
  - exact Hcontext.
  - destruct tdtt_typing_supports as [Hcontext_support _].
    apply (Hcontext_support theta gamma).
    exact Hcontext.
  - exact Hleft.
  - exact Hright.
  - exact Heq.
  - exact Ha.
  - exact Hb.
Qed.

Record mltt_context_extension_regular
    (gamma : context) (a : term) (level : nat) : Prop := {
  mltt_context_extension_regular_context_wf :
    wf_context (a :: gamma);
  mltt_context_extension_regular_tail_wf :
    wf_context gamma;
  mltt_context_extension_regular_context_support :
    context_supports MLTT (a :: gamma);
  mltt_context_extension_regular_tail_support :
    context_supports MLTT gamma;
  mltt_context_extension_regular_entry_type :
    has_type gamma a (tUniverse level);
  mltt_context_extension_regular_entry_support :
    supports MLTT a = true
}.

Record utt_context_extension_regular
    (gamma : context) (a : term) (sort : utt_sort) : Prop := {
  utt_context_extension_regular_context_wf :
    utt_wf_context (a :: gamma);
  utt_context_extension_regular_tail_wf :
    utt_wf_context gamma;
  utt_context_extension_regular_context_support :
    context_supports UTT (a :: gamma);
  utt_context_extension_regular_tail_support :
    context_supports UTT gamma;
  utt_context_extension_regular_entry_type :
    utt_has_type gamma a (utt_sort_term sort);
  utt_context_extension_regular_entry_support :
    supports UTT a = true
}.

Record tdtt_context_extension_regular
    (theta : temporal_context) (gamma : context)
    (a : term) (sort : utt_sort) : Prop := {
  tdtt_context_extension_regular_context_wf :
    tdtt_wf_context theta (a :: gamma);
  tdtt_context_extension_regular_tail_wf :
    tdtt_wf_context theta gamma;
  tdtt_context_extension_regular_context_support :
    context_supports TDTT (a :: gamma);
  tdtt_context_extension_regular_tail_support :
    context_supports TDTT gamma;
  tdtt_context_extension_regular_entry_type :
    tdtt_has_type theta gamma a (utt_sort_term sort);
  tdtt_context_extension_regular_entry_support :
    supports TDTT a = true
}.

Theorem mltt_context_extension_is_regular :
  forall gamma a,
    wf_context (a :: gamma) ->
    exists level,
      mltt_context_extension_regular gamma a level.
Proof.
  intros gamma a Hcontext.
  destruct (mltt_wf_context_cons_inversion gamma a Hcontext)
    as [level [Htail Hentry]].
  exists level.
  constructor.
  - exact Hcontext.
  - exact Htail.
  - destruct mltt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - destruct mltt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Htail.
  - exact Hentry.
  - apply mltt_typable_supports in Hentry.
    exact (proj1 Hentry).
Qed.

Theorem utt_context_extension_is_regular :
  forall gamma a,
    utt_wf_context (a :: gamma) ->
    exists sort,
      utt_context_extension_regular gamma a sort.
Proof.
  intros gamma a Hcontext.
  destruct (utt_wf_context_cons_inversion gamma a Hcontext)
    as [sort [Htail Hentry]].
  exists sort.
  constructor.
  - exact Hcontext.
  - exact Htail.
  - destruct utt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Hcontext.
  - destruct utt_typing_supports as [Hcontext_support _].
    apply Hcontext_support.
    exact Htail.
  - exact Hentry.
  - apply utt_typable_supports in Hentry.
    exact (proj1 Hentry).
Qed.

Theorem tdtt_context_extension_is_regular :
  forall theta gamma a,
    tdtt_wf_context theta (a :: gamma) ->
    exists sort,
      tdtt_context_extension_regular theta gamma a sort.
Proof.
  intros theta gamma a Hcontext.
  destruct (tdtt_wf_context_cons_inversion theta gamma a Hcontext)
    as [sort [Htail Hentry]].
  exists sort.
  constructor.
  - exact Hcontext.
  - exact Htail.
  - destruct tdtt_typing_supports as [Hcontext_support _].
    apply (Hcontext_support theta (a :: gamma)).
    exact Hcontext.
  - destruct tdtt_typing_supports as [Hcontext_support _].
    apply (Hcontext_support theta gamma).
    exact Htail.
  - exact Hentry.
  - apply tdtt_typable_supports in Hentry.
    exact (proj1 Hentry).
Qed.

Record mltt_context_lookup_regular
    (gamma : context) (index : nat) (a : term) : Prop := {
  mltt_context_lookup_regular_context_wf :
    wf_context gamma;
  mltt_context_lookup_regular_context_support :
    context_supports MLTT gamma;
  mltt_context_lookup_regular_lookup :
    lookup gamma index a;
  mltt_context_lookup_regular_entry_support :
    supports MLTT a = true
}.

Record utt_context_lookup_regular
    (gamma : context) (index : nat) (a : term) : Prop := {
  utt_context_lookup_regular_context_wf :
    utt_wf_context gamma;
  utt_context_lookup_regular_context_support :
    context_supports UTT gamma;
  utt_context_lookup_regular_lookup :
    lookup gamma index a;
  utt_context_lookup_regular_entry_support :
    supports UTT a = true
}.

Record tdtt_context_lookup_regular
    (theta : temporal_context)
    (gamma : context) (index : nat) (a : term) : Prop := {
  tdtt_context_lookup_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_context_lookup_regular_context_support :
    context_supports TDTT gamma;
  tdtt_context_lookup_regular_lookup :
    lookup gamma index a;
  tdtt_context_lookup_regular_entry_support :
    supports TDTT a = true
}.

Theorem mltt_context_lookup_is_regular :
  forall gamma index a,
    wf_context gamma ->
    lookup gamma index a ->
    mltt_context_lookup_regular gamma index a.
Proof.
  intros gamma index a Hcontext Hlookup.
  pose proof (proj1 mltt_typing_supports gamma Hcontext)
    as Hsupport.
  constructor.
  - exact Hcontext.
  - exact Hsupport.
  - exact Hlookup.
  - apply lookup_supports with
      (gamma := gamma)
      (index := index).
    + exact Hsupport.
    + exact Hlookup.
Qed.

Theorem utt_context_lookup_is_regular :
  forall gamma index a,
    utt_wf_context gamma ->
    lookup gamma index a ->
    utt_context_lookup_regular gamma index a.
Proof.
  intros gamma index a Hcontext Hlookup.
  pose proof (proj1 utt_typing_supports gamma Hcontext)
    as Hsupport.
  constructor.
  - exact Hcontext.
  - exact Hsupport.
  - exact Hlookup.
  - apply lookup_supports with
      (gamma := gamma)
      (index := index).
    + exact Hsupport.
    + exact Hlookup.
Qed.

Theorem tdtt_context_lookup_is_regular :
  forall theta gamma index a,
    tdtt_wf_context theta gamma ->
    lookup gamma index a ->
    tdtt_context_lookup_regular theta gamma index a.
Proof.
  intros theta gamma index a Hcontext Hlookup.
  pose proof (proj1 tdtt_typing_supports theta gamma Hcontext)
    as Hsupport.
  constructor.
  - exact Hcontext.
  - exact Hsupport.
  - exact Hlookup.
  - apply lookup_supports with
      (gamma := gamma)
      (index := index).
    + exact Hsupport.
    + exact Hlookup.
Qed.

Record tdtt_temporal_lookup_regular
    (theta : temporal_context) (index : nat) : Prop := {
  tdtt_temporal_lookup_regular_lookup :
    temporal_lookup theta index;
  tdtt_temporal_lookup_regular_wf :
    temporal_wf theta (tTimeVar index);
  tdtt_temporal_lookup_regular_support :
    supports TDTT (tTimeVar index) = true
}.

Theorem tdtt_temporal_lookup_is_regular :
  forall theta index,
    temporal_lookup theta index ->
    tdtt_temporal_lookup_regular theta index.
Proof.
  intros theta index Hlookup.
  constructor.
  - exact Hlookup.
  - apply temporal_wf_var.
    exact Hlookup.
  - reflexivity.
Qed.

Record tdtt_temporal_wf_regular
    (theta : temporal_context) (time : term) : Prop := {
  tdtt_temporal_wf_regular_wf :
    temporal_wf theta time;
  tdtt_temporal_wf_regular_support :
    supports TDTT time = true;
  tdtt_temporal_wf_regular_inversion :
    exists index,
      time = tTimeVar index /\
      temporal_lookup theta index
}.

Theorem tdtt_temporal_wf_is_regular :
  forall theta time,
    temporal_wf theta time ->
    tdtt_temporal_wf_regular theta time.
Proof.
  intros theta time Htime.
  constructor.
  - exact Htime.
  - apply temporal_wf_supports_tdtt with (theta := theta).
    exact Htime.
  - apply temporal_wf_inversion.
    exact Htime.
Qed.

Record tdtt_at_constructor_regular
    (theta : temporal_context) (gamma : context)
    (a time result : term) (sort : utt_sort) : Prop := {
  tdtt_at_regular_typing :
    tdtt_has_type theta gamma (tAt a time) result;
  tdtt_at_regular_indexed_type :
    tdtt_has_type theta gamma a (utt_sort_term sort);
  tdtt_at_regular_time_wf :
    temporal_wf theta time;
  tdtt_at_regular_constructor_support :
    supports TDTT (tAt a time) = true;
  tdtt_at_regular_indexed_type_support :
    supports TDTT a = true;
  tdtt_at_regular_time_support :
    supports TDTT time = true
}.

Theorem tdtt_at_constructor_is_regular :
  forall theta gamma a time result,
    tdtt_has_type theta gamma (tAt a time) result ->
    exists sort,
      tdtt_at_constructor_regular theta gamma a time result sort.
Proof.
  intros theta gamma a time result Htyping.
  destruct (tdtt_at_typing_inversion theta gamma a time result Htyping)
    as [sort [Ha Htime]].
  exists sort.
  pose proof (tdtt_typable_supports
    theta gamma (tAt a time) result Htyping) as [Hat _].
  pose proof (tdtt_typable_supports
    theta gamma a (utt_sort_term sort) Ha) as [Ha_support _].
  pose proof (temporal_wf_supports_tdtt theta time Htime)
    as Htime_support.
  constructor.
  - exact Htyping.
  - exact Ha.
  - exact Htime.
  - exact Hat.
  - exact Ha_support.
  - exact Htime_support.
Qed.

Record tdtt_later_at_constructor_regular
    (theta : temporal_context) (gamma : context)
    (clock a result : term) (sort : utt_sort) : Prop := {
  tdtt_later_at_regular_typing :
    tdtt_has_type theta gamma (tLaterAt clock a) result;
  tdtt_later_at_regular_clock_wf :
    temporal_wf theta clock;
  tdtt_later_at_regular_payload_type :
    tdtt_has_type theta gamma a (utt_sort_term sort);
  tdtt_later_at_regular_constructor_support :
    supports TDTT (tLaterAt clock a) = true;
  tdtt_later_at_regular_clock_support :
    supports TDTT clock = true;
  tdtt_later_at_regular_payload_support :
    supports TDTT a = true
}.

Theorem tdtt_later_at_constructor_is_regular :
  forall theta gamma clock a result,
    tdtt_has_type theta gamma (tLaterAt clock a) result ->
    exists sort,
      tdtt_later_at_constructor_regular theta gamma clock a result sort.
Proof.
  intros theta gamma clock a result Htyping.
  destruct (tdtt_later_at_typing_inversion
    theta gamma clock a result Htyping) as [sort [Hclock Ha]].
  exists sort.
  pose proof (tdtt_typable_supports
    theta gamma (tLaterAt clock a) result Htyping) as [Hlater _].
  pose proof (temporal_wf_supports_tdtt theta clock Hclock)
    as Hclock_support.
  pose proof (tdtt_typable_supports
    theta gamma a (utt_sort_term sort) Ha) as [Ha_support _].
  constructor.
  - exact Htyping.
  - exact Hclock.
  - exact Ha.
  - exact Hlater.
  - exact Hclock_support.
  - exact Ha_support.
Qed.

Record tdtt_next_at_constructor_regular
    (theta : temporal_context) (gamma : context)
    (clock t result a : term) : Prop := {
  tdtt_next_at_regular_typing :
    tdtt_has_type theta gamma (tNextAt clock t) result;
  tdtt_next_at_regular_clock_wf :
    temporal_wf theta clock;
  tdtt_next_at_regular_payload_typing :
    tdtt_has_type theta gamma t a;
  tdtt_next_at_regular_constructor_support :
    supports TDTT (tNextAt clock t) = true;
  tdtt_next_at_regular_clock_support :
    supports TDTT clock = true;
  tdtt_next_at_regular_payload_support :
    supports TDTT t = true;
  tdtt_next_at_regular_payload_type_support :
    supports TDTT a = true
}.

Theorem tdtt_next_at_constructor_is_regular :
  forall theta gamma clock t result,
    tdtt_has_type theta gamma (tNextAt clock t) result ->
    exists a,
      tdtt_next_at_constructor_regular theta gamma clock t result a.
Proof.
  intros theta gamma clock t result Htyping.
  destruct (tdtt_next_at_typing_inversion
    theta gamma clock t result Htyping) as [a [Hclock Ht]].
  exists a.
  pose proof (tdtt_typable_supports
    theta gamma (tNextAt clock t) result Htyping) as [Hnext _].
  pose proof (temporal_wf_supports_tdtt theta clock Hclock)
    as Hclock_support.
  pose proof (tdtt_typable_supports theta gamma t a Ht)
    as [Ht_support Ha_support].
  constructor.
  - exact Htyping.
  - exact Hclock.
  - exact Ht.
  - exact Hnext.
  - exact Hclock_support.
  - exact Ht_support.
  - exact Ha_support.
Qed.

Record tdtt_fix_at_constructor_regular
    (theta : temporal_context) (gamma : context)
    (clock body result a : term) (sort : utt_sort) : Prop := {
  tdtt_fix_at_regular_typing :
    tdtt_has_type theta gamma (tFixAt clock body) result;
  tdtt_fix_at_regular_clock_wf :
    temporal_wf theta clock;
  tdtt_fix_at_regular_guarded_type :
    tdtt_has_type theta gamma a (utt_sort_term sort);
  tdtt_fix_at_regular_body_typing :
    tdtt_has_type theta
      (tLaterAt clock a :: gamma)
      body
      (shift_term 1 0 a);
  tdtt_fix_at_regular_constructor_support :
    supports TDTT (tFixAt clock body) = true;
  tdtt_fix_at_regular_clock_support :
    supports TDTT clock = true;
  tdtt_fix_at_regular_guarded_type_support :
    supports TDTT a = true;
  tdtt_fix_at_regular_body_support :
    supports TDTT body = true;
  tdtt_fix_at_regular_body_type_support :
    supports TDTT (shift_term 1 0 a) = true
}.

Theorem tdtt_fix_at_constructor_is_regular :
  forall theta gamma clock body result,
    tdtt_has_type theta gamma (tFixAt clock body) result ->
    exists a sort,
      tdtt_fix_at_constructor_regular theta gamma clock body result a sort.
Proof.
  intros theta gamma clock body result Htyping.
  destruct (tdtt_fix_at_typing_inversion
    theta gamma clock body result Htyping)
    as [a [sort [Hclock [Ha Hbody]]]].
  exists a, sort.
  pose proof (tdtt_typable_supports
    theta gamma (tFixAt clock body) result Htyping) as [Hfix _].
  pose proof (temporal_wf_supports_tdtt theta clock Hclock)
    as Hclock_support.
  pose proof (tdtt_typable_supports
    theta gamma a (utt_sort_term sort) Ha) as [Ha_support _].
  pose proof (tdtt_typable_supports
    theta (tLaterAt clock a :: gamma) body (shift_term 1 0 a) Hbody)
    as [Hbody_support Hbody_type_support].
  constructor.
  - exact Htyping.
  - exact Hclock.
  - exact Ha.
  - exact Hbody.
  - exact Hfix.
  - exact Hclock_support.
  - exact Ha_support.
  - exact Hbody_support.
  - exact Hbody_type_support.
Qed.

Record tdtt_clock_pi_constructor_regular
    (theta : temporal_context) (gamma : context)
    (a result : term) (sort : utt_sort) : Prop := {
  tdtt_clock_pi_regular_typing :
    tdtt_has_type theta gamma (tClockPi a) result;
  tdtt_clock_pi_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_clock_pi_regular_shifted_context_wf :
    tdtt_wf_context
      (tc_extend theta)
      (shift_time_context 1 0 gamma);
  tdtt_clock_pi_regular_body_type :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      a
      (utt_sort_term sort);
  tdtt_clock_pi_regular_shifted_context_support :
    context_supports TDTT (shift_time_context 1 0 gamma);
  tdtt_clock_pi_regular_constructor_support :
    supports TDTT (tClockPi a) = true;
  tdtt_clock_pi_regular_body_support :
    supports TDTT a = true
}.

Theorem tdtt_clock_pi_constructor_is_regular :
  forall theta gamma a result,
    tdtt_has_type theta gamma (tClockPi a) result ->
    exists sort,
      tdtt_clock_pi_constructor_regular theta gamma a result sort.
Proof.
  intros theta gamma a result Htyping.
  destruct (tdtt_clock_pi_typing_inversion theta gamma a result Htyping)
    as [sort [Hcontext Ha]].
  exists sort.
  pose proof (tdtt_typing_context_wf
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    a
    (utt_sort_term sort)
    Ha) as Hshifted_context.
  pose proof (tdtt_typable_supports
    theta gamma (tClockPi a) result Htyping) as [Hclock_pi _].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    a
    (utt_sort_term sort)
    Ha) as [Ha_support _].
  destruct tdtt_typing_supports as [Hcontext_support _].
  pose proof (Hcontext_support
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    Hshifted_context) as Hshifted_context_support.
  constructor.
  - exact Htyping.
  - exact Hcontext.
  - exact Hshifted_context.
  - exact Ha.
  - exact Hshifted_context_support.
  - exact Hclock_pi.
  - exact Ha_support.
Qed.

Record tdtt_clock_lam_constructor_regular
    (theta : temporal_context) (gamma : context)
    (body result a : term) (sort : utt_sort) : Prop := {
  tdtt_clock_lam_regular_typing :
    tdtt_has_type theta gamma (tClockLam body) result;
  tdtt_clock_lam_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_clock_lam_regular_shifted_context_wf :
    tdtt_wf_context
      (tc_extend theta)
      (shift_time_context 1 0 gamma);
  tdtt_clock_lam_regular_body_type :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      a
      (utt_sort_term sort);
  tdtt_clock_lam_regular_body_typing :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a;
  tdtt_clock_lam_regular_shifted_context_support :
    context_supports TDTT (shift_time_context 1 0 gamma);
  tdtt_clock_lam_regular_constructor_support :
    supports TDTT (tClockLam body) = true;
  tdtt_clock_lam_regular_abstraction_type_support :
    supports TDTT (tClockPi a) = true;
  tdtt_clock_lam_regular_body_type_support :
    supports TDTT a = true;
  tdtt_clock_lam_regular_body_support :
    supports TDTT body = true
}.

Theorem tdtt_clock_lam_constructor_is_regular :
  forall theta gamma body result,
    tdtt_has_type theta gamma (tClockLam body) result ->
    exists a sort,
      tdtt_clock_lam_constructor_regular
        theta gamma body result a sort.
Proof.
  intros theta gamma body result Htyping.
  destruct (tdtt_clock_lam_typing_inversion
    theta gamma body result Htyping)
    as [a [sort [Hcontext [Ha Hbody]]]].
  exists a, sort.
  pose proof (tdtt_typing_context_wf
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    a
    (utt_sort_term sort)
    Ha) as Hshifted_context.
  pose proof (tdtt_typable_supports
    theta gamma (tClockLam body) result Htyping) as [Hclock_lam _].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    a
    (utt_sort_term sort)
    Ha) as [Ha_support _].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as [Hbody_support _].
  destruct tdtt_typing_supports as [Hcontext_support _].
  pose proof (Hcontext_support
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    Hshifted_context) as Hshifted_context_support.
  constructor.
  - exact Htyping.
  - exact Hcontext.
  - exact Hshifted_context.
  - exact Ha.
  - exact Hbody.
  - exact Hshifted_context_support.
  - exact Hclock_lam.
  - simpl.
    exact Ha_support.
  - exact Ha_support.
  - exact Hbody_support.
Qed.

Record tdtt_clock_app_constructor_regular
    (theta : temporal_context) (gamma : context)
    (f clock result a : term) : Prop := {
  tdtt_clock_app_regular_typing :
    tdtt_has_type theta gamma (tClockApp f clock) result;
  tdtt_clock_app_regular_function_typing :
    tdtt_has_type theta gamma f (tClockPi a);
  tdtt_clock_app_regular_clock_wf :
    temporal_wf theta clock;
  tdtt_clock_app_regular_constructor_support :
    supports TDTT (tClockApp f clock) = true;
  tdtt_clock_app_regular_function_support :
    supports TDTT f = true;
  tdtt_clock_app_regular_clock_support :
    supports TDTT clock = true;
  tdtt_clock_app_regular_type_family_support :
    supports TDTT a = true;
  tdtt_clock_app_regular_result_type_support :
    supports TDTT result = true
}.

Theorem tdtt_clock_app_constructor_is_regular :
  forall theta gamma f clock result,
    tdtt_has_type theta gamma (tClockApp f clock) result ->
    exists a,
      tdtt_clock_app_constructor_regular theta gamma f clock result a.
Proof.
  intros theta gamma f clock result Htyping.
  destruct (tdtt_clock_app_typing_inversion
    theta gamma f clock result Htyping) as [a [Hf Hclock]].
  exists a.
  pose proof (tdtt_typable_supports
    theta gamma (tClockApp f clock) result Htyping) as [Hclock_app Hresult].
  pose proof (tdtt_typable_supports
    theta gamma f (tClockPi a) Hf) as [Hf_support Hpi_support].
  pose proof (temporal_wf_supports_tdtt theta clock Hclock)
    as Hclock_support.
  simpl in Hpi_support.
  constructor.
  - exact Htyping.
  - exact Hf.
  - exact Hclock.
  - exact Hclock_app.
  - exact Hf_support.
  - exact Hclock_support.
  - exact Hpi_support.
  - exact Hresult.
Qed.

Record tdtt_delayed_subst_constructor_regular
    (theta : temporal_context) (gamma : context)
    (clock body result a : term) : Prop := {
  tdtt_delayed_subst_regular_typing :
    tdtt_has_type theta gamma (tDelayedSubst clock body) result;
  tdtt_delayed_subst_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_delayed_subst_regular_shifted_context_wf :
    tdtt_wf_context
      (tc_extend theta)
      (shift_time_context 1 0 gamma);
  tdtt_delayed_subst_regular_clock_wf :
    temporal_wf theta clock;
  tdtt_delayed_subst_regular_body_typing :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a;
  tdtt_delayed_subst_regular_constructor_support :
    supports TDTT (tDelayedSubst clock body) = true;
  tdtt_delayed_subst_regular_clock_support :
    supports TDTT clock = true;
  tdtt_delayed_subst_regular_body_support :
    supports TDTT body = true;
  tdtt_delayed_subst_regular_body_type_support :
    supports TDTT a = true;
  tdtt_delayed_subst_regular_result_type_support :
    supports TDTT result = true;
  tdtt_delayed_subst_regular_delayed_type_support :
    supports TDTT (delayed_substitution_term clock a) = true
}.

Theorem tdtt_delayed_subst_constructor_is_regular :
  forall theta gamma clock body result,
    tdtt_has_type theta gamma (tDelayedSubst clock body) result ->
    exists a,
      tdtt_delayed_subst_constructor_regular
        theta gamma clock body result a.
Proof.
  intros theta gamma clock body result Htyping.
  destruct (tdtt_delayed_subst_typing_inversion
    theta gamma clock body result Htyping)
    as [a [Hcontext [Hclock Hbody]]].
  exists a.
  pose proof (tdtt_typing_context_wf
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as Hshifted_context.
  pose proof (tdtt_typable_supports
    theta gamma (tDelayedSubst clock body) result Htyping)
    as [Hdelayed Hresult].
  pose proof (temporal_wf_supports_tdtt theta clock Hclock)
    as Hclock_support.
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as [Hbody_support Ha_support].
  pose proof (delayed_substitution_supports_tdtt
    clock a Hclock_support Ha_support) as Hdelayed_type.
  constructor.
  - exact Htyping.
  - exact Hcontext.
  - exact Hshifted_context.
  - exact Hclock.
  - exact Hbody.
  - exact Hdelayed.
  - exact Hclock_support.
  - exact Hbody_support.
  - exact Ha_support.
  - exact Hresult.
	  - exact Hdelayed_type.
Qed.

Record tdtt_delayed_subst_inversion_regular
    (theta : temporal_context) (gamma : context)
    (clock body result a : term) : Prop := {
  tdtt_delayed_subst_inversion_regular_typing :
    tdtt_has_type theta gamma (tDelayedSubst clock body) result;
  tdtt_delayed_subst_inversion_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_delayed_subst_inversion_regular_shifted_context_wf :
    tdtt_wf_context
      (tc_extend theta)
      (shift_time_context 1 0 gamma);
  tdtt_delayed_subst_inversion_regular_clock_wf :
    temporal_wf theta clock;
  tdtt_delayed_subst_inversion_regular_body_typing :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a;
  tdtt_delayed_subst_inversion_regular_canonical_typing :
    tdtt_has_type theta gamma
      (tDelayedSubst clock body)
      (delayed_substitution_term clock a);
  tdtt_delayed_subst_inversion_regular_delayed_term_typing :
    tdtt_has_type theta gamma
      (delayed_substitution_term clock body)
      (delayed_substitution_term clock a);
  tdtt_delayed_subst_inversion_regular_constructor_support :
    supports TDTT (tDelayedSubst clock body) = true;
  tdtt_delayed_subst_inversion_regular_result_support :
    supports TDTT result = true;
  tdtt_delayed_subst_inversion_regular_canonical_type_support :
    supports TDTT (delayed_substitution_term clock a) = true;
  tdtt_delayed_subst_inversion_regular_delayed_term_support :
    supports TDTT (delayed_substitution_term clock body) = true;
  tdtt_delayed_subst_inversion_regular_clock_support :
    supports TDTT clock = true;
  tdtt_delayed_subst_inversion_regular_body_support :
    supports TDTT body = true;
  tdtt_delayed_subst_inversion_regular_body_type_support :
    supports TDTT a = true
}.

Theorem tdtt_delayed_subst_typing_inversion_is_regular :
  forall theta gamma clock body result,
    tdtt_has_type theta gamma (tDelayedSubst clock body) result ->
    exists a,
      tdtt_delayed_subst_inversion_regular
        theta gamma clock body result a.
Proof.
  intros theta gamma clock body result Htyping.
  destruct (tdtt_delayed_subst_typing_inversion
    theta gamma clock body result Htyping)
    as [a [Hcontext [Hclock Hbody]]].
  exists a.
  pose proof (tdtt_typing_context_wf
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as Hshifted_context.
  pose proof (tdtt_native_delayed_substitution_has_delayed_type
    theta gamma clock body a Hcontext Hclock Hbody) as Hcanonical.
  pose proof (tdtt_delayed_substitution_preserves_typing_in_context
    theta gamma clock body a Hclock Hbody) as Hdelayed_term.
  pose proof (tdtt_typable_supports
    theta gamma
    (tDelayedSubst clock body)
    result
    Htyping) as [Hconstructor_support Hresult_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (tDelayedSubst clock body)
    (delayed_substitution_term clock a)
    Hcanonical) as [_ Hcanonical_type_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (delayed_substitution_term clock body)
    (delayed_substitution_term clock a)
    Hdelayed_term) as [Hdelayed_term_support _].
  pose proof (temporal_wf_supports_tdtt theta clock Hclock)
    as Hclock_support.
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as [Hbody_support Ha_support].
  constructor.
  - exact Htyping.
  - exact Hcontext.
  - exact Hshifted_context.
  - exact Hclock.
  - exact Hbody.
  - exact Hcanonical.
  - exact Hdelayed_term.
  - exact Hconstructor_support.
  - exact Hresult_support.
  - exact Hcanonical_type_support.
  - exact Hdelayed_term_support.
  - exact Hclock_support.
  - exact Hbody_support.
  - exact Ha_support.
Qed.

Lemma subst_time_shift_time_context_cancel :
  forall replacement gamma,
    subst_time_context replacement 0 (shift_time_context 1 0 gamma) =
    gamma.
Proof.
  intros replacement gamma.
  induction gamma as [| entry gamma IHgamma]; simpl.
  - reflexivity.
  - rewrite subst_time_shift_cancel.
    rewrite IHgamma.
    reflexivity.
Qed.

Lemma tdtt_clock_beta_reduct_has_type :
  forall theta gamma body a clock_index,
    temporal_wf theta (tTimeVar clock_index) ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a ->
    tdtt_has_type theta gamma
      (subst_time (tTimeVar clock_index) 0 body)
      (subst_time (tTimeVar clock_index) 0 a).
Proof.
  intros theta gamma body a clock_index Hclock Hbody.
  pose proof (tdtt_has_type_substitute_time_top
    theta
    (tTimeVar clock_index)
    (shift_time_context 1 0 gamma)
    body
    a
    Hclock
    Hbody) as Hreduct.
  rewrite subst_time_shift_time_context_cancel in Hreduct.
  exact Hreduct.
Qed.

Record tdtt_clock_beta_regular
    (theta : temporal_context) (gamma : context)
    (body a : term) (clock_index : nat) (sort : utt_sort) : Prop := {
  tdtt_clock_beta_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_clock_beta_regular_clock_wf :
    temporal_wf theta (tTimeVar clock_index);
  tdtt_clock_beta_regular_family_type :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      a
      (utt_sort_term sort);
  tdtt_clock_beta_regular_body_typing :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a;
  tdtt_clock_beta_regular_application_typing :
    tdtt_has_type theta gamma
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (subst_time (tTimeVar clock_index) 0 a);
  tdtt_clock_beta_regular_reduct_typing :
    tdtt_has_type theta gamma
      (subst_time (tTimeVar clock_index) 0 body)
      (subst_time (tTimeVar clock_index) 0 a);
  tdtt_clock_beta_regular_defeq :
    defeq
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (subst_time (tTimeVar clock_index) 0 body);
  tdtt_clock_beta_regular_application_support :
    supports TDTT
      (tClockApp (tClockLam body) (tTimeVar clock_index)) = true;
  tdtt_clock_beta_regular_reduct_support :
    supports TDTT (subst_time (tTimeVar clock_index) 0 body) = true;
  tdtt_clock_beta_regular_result_type_support :
    supports TDTT (subst_time (tTimeVar clock_index) 0 a) = true;
  tdtt_clock_beta_regular_family_support :
    supports TDTT a = true;
  tdtt_clock_beta_regular_body_support :
    supports TDTT body = true;
  tdtt_clock_beta_regular_clock_support :
    supports TDTT (tTimeVar clock_index) = true
}.

Theorem tdtt_clock_beta_is_regular :
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
    tdtt_clock_beta_regular theta gamma body a clock_index sort.
Proof.
  intros theta gamma body a clock_index sort
    Hcontext Hclock Ha Hbody.
  assert (Happlication :
    tdtt_has_type theta gamma
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (subst_time (tTimeVar clock_index) 0 a)).
  { apply tdtt_ty_clock_app with (a := a).
    - apply tdtt_ty_clock_lam with (sort := sort).
      + exact Hcontext.
      + exact Ha.
      + exact Hbody.
    - exact Hclock. }
  pose proof (tdtt_clock_beta_reduct_has_type
    theta gamma body a clock_index Hclock Hbody) as Hreduct.
  pose proof (tdtt_typable_supports
    theta gamma
    (tClockApp (tClockLam body) (tTimeVar clock_index))
    (subst_time (tTimeVar clock_index) 0 a)
    Happlication) as [Happlication_support Hresult_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (subst_time (tTimeVar clock_index) 0 body)
    (subst_time (tTimeVar clock_index) 0 a)
    Hreduct) as [Hreduct_support _].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    a
    (utt_sort_term sort)
    Ha) as [Ha_support _].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as [Hbody_support _].
  pose proof (temporal_wf_supports_tdtt
    theta (tTimeVar clock_index) Hclock) as Hclock_support.
  constructor.
  - exact Hcontext.
  - exact Hclock.
  - exact Ha.
  - exact Hbody.
  - exact Happlication.
  - exact Hreduct.
  - apply de_clock_beta.
  - exact Happlication_support.
  - exact Hreduct_support.
  - exact Hresult_support.
  - exact Ha_support.
  - exact Hbody_support.
  - exact Hclock_support.
Qed.

Theorem tdtt_clock_beta_from_clock_lam_regular :
  forall theta gamma body result a clock_index sort,
    tdtt_clock_lam_constructor_regular theta gamma body result a sort ->
    temporal_wf theta (tTimeVar clock_index) ->
    tdtt_clock_beta_regular theta gamma body a clock_index sort.
Proof.
  intros theta gamma body result a clock_index sort Hregular Hclock.
  destruct Hregular as
    [_ Hcontext _ Ha Hbody _ _ _ _ _].
  apply tdtt_clock_beta_is_regular.
  - exact Hcontext.
  - exact Hclock.
  - exact Ha.
  - exact Hbody.
Qed.

Record tdtt_delayed_subst_compute_regular
    (theta : temporal_context) (gamma : context)
    (body a : term) (clock_index : nat) : Prop := {
  tdtt_delayed_subst_compute_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_delayed_subst_compute_regular_clock_wf :
    temporal_wf theta (tTimeVar clock_index);
  tdtt_delayed_subst_compute_regular_body_typing :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a;
  tdtt_delayed_subst_compute_regular_native_typing :
    tdtt_has_type theta gamma
      (tDelayedSubst (tTimeVar clock_index) body)
      (subst_time (tTimeVar clock_index) 0 a);
  tdtt_delayed_subst_compute_regular_reduct_typing :
    tdtt_has_type theta gamma
      (subst_time (tTimeVar clock_index) 0 body)
      (subst_time (tTimeVar clock_index) 0 a);
  tdtt_delayed_subst_compute_regular_defeq :
    defeq
      (tDelayedSubst (tTimeVar clock_index) body)
      (subst_time (tTimeVar clock_index) 0 body);
  tdtt_delayed_subst_compute_regular_native_support :
    supports TDTT (tDelayedSubst (tTimeVar clock_index) body) = true;
  tdtt_delayed_subst_compute_regular_reduct_support :
    supports TDTT (subst_time (tTimeVar clock_index) 0 body) = true;
  tdtt_delayed_subst_compute_regular_result_type_support :
    supports TDTT (subst_time (tTimeVar clock_index) 0 a) = true;
  tdtt_delayed_subst_compute_regular_body_support :
    supports TDTT body = true;
  tdtt_delayed_subst_compute_regular_body_type_support :
    supports TDTT a = true;
  tdtt_delayed_subst_compute_regular_clock_support :
    supports TDTT (tTimeVar clock_index) = true
}.

Theorem tdtt_delayed_subst_compute_is_regular :
  forall theta gamma body a clock_index,
    tdtt_wf_context theta gamma ->
    temporal_wf theta (tTimeVar clock_index) ->
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a ->
    tdtt_delayed_subst_compute_regular
      theta gamma body a clock_index.
Proof.
  intros theta gamma body a clock_index Hcontext Hclock Hbody.
  assert (Hnative :
    tdtt_has_type theta gamma
      (tDelayedSubst (tTimeVar clock_index) body)
      (subst_time (tTimeVar clock_index) 0 a)).
  { apply tdtt_ty_delayed_subst.
    - exact Hcontext.
    - exact Hclock.
    - exact Hbody. }
  pose proof (tdtt_clock_beta_reduct_has_type
    theta gamma body a clock_index Hclock Hbody) as Hreduct.
  pose proof (tdtt_typable_supports
    theta gamma
    (tDelayedSubst (tTimeVar clock_index) body)
    (subst_time (tTimeVar clock_index) 0 a)
    Hnative) as [Hnative_support Hresult_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (subst_time (tTimeVar clock_index) 0 body)
    (subst_time (tTimeVar clock_index) 0 a)
    Hreduct) as [Hreduct_support _].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as [Hbody_support Ha_support].
  pose proof (temporal_wf_supports_tdtt
    theta (tTimeVar clock_index) Hclock) as Hclock_support.
  constructor.
  - exact Hcontext.
  - exact Hclock.
  - exact Hbody.
  - exact Hnative.
  - exact Hreduct.
  - apply de_delayed_subst_compute.
  - exact Hnative_support.
  - exact Hreduct_support.
  - exact Hresult_support.
  - exact Hbody_support.
  - exact Ha_support.
  - exact Hclock_support.
Qed.

Record tdtt_clock_native_agreement_regular
    (theta : temporal_context) (gamma : context)
    (body a : term) (clock_index : nat) (sort : utt_sort) : Prop := {
  tdtt_clock_native_agreement_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_clock_native_agreement_regular_clock_wf :
    temporal_wf theta (tTimeVar clock_index);
  tdtt_clock_native_agreement_regular_family_type :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      a
      (utt_sort_term sort);
  tdtt_clock_native_agreement_regular_body_typing :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a;
  tdtt_clock_native_agreement_regular_application_typing :
    tdtt_has_type theta gamma
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (delayed_substitution_term (tTimeVar clock_index) a);
  tdtt_clock_native_agreement_regular_native_typing :
    tdtt_has_type theta gamma
      (tDelayedSubst (tTimeVar clock_index) body)
      (delayed_substitution_term (tTimeVar clock_index) a);
  tdtt_clock_native_agreement_regular_defeq :
    defeq
      (tClockApp (tClockLam body) (tTimeVar clock_index))
      (tDelayedSubst (tTimeVar clock_index) body);
  tdtt_clock_native_agreement_regular_application_support :
    supports TDTT
      (tClockApp (tClockLam body) (tTimeVar clock_index)) = true;
  tdtt_clock_native_agreement_regular_native_support :
    supports TDTT (tDelayedSubst (tTimeVar clock_index) body) = true;
  tdtt_clock_native_agreement_regular_result_type_support :
    supports TDTT
      (delayed_substitution_term (tTimeVar clock_index) a) = true;
  tdtt_clock_native_agreement_regular_family_support :
    supports TDTT a = true;
  tdtt_clock_native_agreement_regular_body_support :
    supports TDTT body = true;
  tdtt_clock_native_agreement_regular_clock_support :
    supports TDTT (tTimeVar clock_index) = true
}.

Theorem tdtt_clock_native_agreement_is_regular :
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
    tdtt_clock_native_agreement_regular
      theta gamma body a clock_index sort.
Proof.
  intros theta gamma body a clock_index sort
    Hcontext Hclock Ha Hbody.
  destruct
    (tdtt_clock_application_native_delayed_substitution_typed_agreement
      theta gamma body a clock_index sort Hcontext Hclock Ha Hbody)
    as [Happlication [Hnative Hagreement]].
  pose proof (tdtt_typable_supports
    theta gamma
    (tClockApp (tClockLam body) (tTimeVar clock_index))
    (delayed_substitution_term (tTimeVar clock_index) a)
    Happlication) as [Happlication_support Hresult_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (tDelayedSubst (tTimeVar clock_index) body)
    (delayed_substitution_term (tTimeVar clock_index) a)
    Hnative) as [Hnative_support _].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    a
    (utt_sort_term sort)
    Ha) as [Ha_support _].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as [Hbody_support _].
  pose proof (temporal_wf_supports_tdtt
    theta (tTimeVar clock_index) Hclock) as Hclock_support.
  constructor.
  - exact Hcontext.
  - exact Hclock.
  - exact Ha.
  - exact Hbody.
  - exact Happlication.
  - exact Hnative.
  - exact Hagreement.
  - exact Happlication_support.
  - exact Hnative_support.
  - exact Hresult_support.
  - exact Ha_support.
  - exact Hbody_support.
  - exact Hclock_support.
Qed.

Record tdtt_native_delayed_substitution_congruence_regular
    (theta : temporal_context) (gamma : context)
    (clock clock' body body' a a' : term) : Prop := {
  tdtt_native_delayed_subst_congruence_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_native_delayed_subst_congruence_regular_left_clock_wf :
    temporal_wf theta clock;
  tdtt_native_delayed_subst_congruence_regular_right_clock_wf :
    temporal_wf theta clock';
  tdtt_native_delayed_subst_congruence_regular_left_body_typing :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body
      a;
  tdtt_native_delayed_subst_congruence_regular_right_body_typing :
    tdtt_has_type
      (tc_extend theta)
      (shift_time_context 1 0 gamma)
      body'
      a';
  tdtt_native_delayed_subst_congruence_regular_left_typing :
    tdtt_has_type theta gamma
      (tDelayedSubst clock body)
      (delayed_substitution_term clock a);
  tdtt_native_delayed_subst_congruence_regular_right_typing :
    tdtt_has_type theta gamma
      (tDelayedSubst clock' body')
      (delayed_substitution_term clock' a');
  tdtt_native_delayed_subst_congruence_regular_clock_defeq :
    defeq clock clock';
  tdtt_native_delayed_subst_congruence_regular_body_defeq :
    defeq body body';
  tdtt_native_delayed_subst_congruence_regular_defeq :
    defeq
      (tDelayedSubst clock body)
      (tDelayedSubst clock' body');
  tdtt_native_delayed_subst_congruence_regular_left_support :
    supports TDTT (tDelayedSubst clock body) = true;
  tdtt_native_delayed_subst_congruence_regular_right_support :
    supports TDTT (tDelayedSubst clock' body') = true;
  tdtt_native_delayed_subst_congruence_regular_left_result_support :
    supports TDTT (delayed_substitution_term clock a) = true;
  tdtt_native_delayed_subst_congruence_regular_right_result_support :
    supports TDTT (delayed_substitution_term clock' a') = true;
  tdtt_native_delayed_subst_congruence_regular_left_clock_support :
    supports TDTT clock = true;
  tdtt_native_delayed_subst_congruence_regular_right_clock_support :
    supports TDTT clock' = true;
  tdtt_native_delayed_subst_congruence_regular_left_body_support :
    supports TDTT body = true;
  tdtt_native_delayed_subst_congruence_regular_right_body_support :
    supports TDTT body' = true;
  tdtt_native_delayed_subst_congruence_regular_left_body_type_support :
    supports TDTT a = true;
  tdtt_native_delayed_subst_congruence_regular_right_body_type_support :
    supports TDTT a' = true
}.

Theorem tdtt_native_delayed_substitution_congruence_is_regular :
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
    tdtt_native_delayed_substitution_congruence_regular
      theta gamma clock clock' body body' a a'.
Proof.
  intros theta gamma clock clock' body body' a a'
    Hcontext Hclock Hclock' Hbody Hbody' Hclock_defeq Hbody_defeq.
  destruct (tdtt_native_delayed_substitution_typed_congruence
    theta gamma clock clock' body body' a a'
    Hcontext Hclock Hclock' Hbody Hbody' Hclock_defeq Hbody_defeq)
    as [Hleft [Hright Hnative_defeq]].
  pose proof (tdtt_typable_supports
    theta gamma
    (tDelayedSubst clock body)
    (delayed_substitution_term clock a)
    Hleft) as [Hleft_support Hleft_result_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (tDelayedSubst clock' body')
    (delayed_substitution_term clock' a')
    Hright) as [Hright_support Hright_result_support].
  pose proof (temporal_wf_supports_tdtt
    theta clock Hclock) as Hclock_support.
  pose proof (temporal_wf_supports_tdtt
    theta clock' Hclock') as Hclock'_support.
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body
    a
    Hbody) as [Hbody_support Ha_support].
  pose proof (tdtt_typable_supports
    (tc_extend theta)
    (shift_time_context 1 0 gamma)
    body'
    a'
    Hbody') as [Hbody'_support Ha'_support].
  constructor.
  - exact Hcontext.
  - exact Hclock.
  - exact Hclock'.
  - exact Hbody.
  - exact Hbody'.
  - exact Hleft.
  - exact Hright.
  - exact Hclock_defeq.
  - exact Hbody_defeq.
  - exact Hnative_defeq.
  - exact Hleft_support.
  - exact Hright_support.
  - exact Hleft_result_support.
  - exact Hright_result_support.
  - exact Hclock_support.
  - exact Hclock'_support.
  - exact Hbody_support.
  - exact Hbody'_support.
  - exact Ha_support.
  - exact Ha'_support.
Qed.

Record tdtt_beta_regular
    (theta : temporal_context) (gamma : context)
    (body argument a b : term)
    (domain_sort codomain_sort : utt_sort) : Prop := {
  tdtt_beta_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_beta_regular_domain_type :
    tdtt_has_type theta gamma a (utt_sort_term domain_sort);
  tdtt_beta_regular_codomain_type :
    tdtt_has_type theta (a :: gamma) b (utt_sort_term codomain_sort);
  tdtt_beta_regular_body_typing :
    tdtt_has_type theta (a :: gamma) body b;
  tdtt_beta_regular_argument_typing :
    tdtt_has_type theta gamma argument a;
  tdtt_beta_regular_lambda_typing :
    tdtt_has_type theta gamma (tLam body) (tPi a b);
  tdtt_beta_regular_application_typing :
    tdtt_has_type theta gamma
      (tApp (tLam body) argument)
      (subst_term argument 0 b);
  tdtt_beta_regular_reduct_typing :
    tdtt_has_type theta gamma
      (subst_term argument 0 body)
      (subst_term argument 0 b);
  tdtt_beta_regular_defeq :
    defeq
      (tApp (tLam body) argument)
      (subst_term argument 0 body);
  tdtt_beta_regular_lambda_support :
    supports TDTT (tLam body) = true;
  tdtt_beta_regular_application_support :
    supports TDTT (tApp (tLam body) argument) = true;
  tdtt_beta_regular_reduct_support :
    supports TDTT (subst_term argument 0 body) = true;
  tdtt_beta_regular_result_type_support :
    supports TDTT (subst_term argument 0 b) = true;
  tdtt_beta_regular_function_type_support :
    supports TDTT (tPi a b) = true;
  tdtt_beta_regular_domain_support :
    supports TDTT a = true;
  tdtt_beta_regular_codomain_support :
    supports TDTT b = true;
  tdtt_beta_regular_body_support :
    supports TDTT body = true;
  tdtt_beta_regular_argument_support :
    supports TDTT argument = true
}.

Theorem tdtt_beta_is_regular :
  forall theta gamma body argument a b domain_sort codomain_sort,
    tdtt_has_type theta gamma a (utt_sort_term domain_sort) ->
    tdtt_has_type theta (a :: gamma) b (utt_sort_term codomain_sort) ->
    tdtt_has_type theta (a :: gamma) body b ->
    tdtt_has_type theta gamma argument a ->
    tdtt_beta_regular
      theta gamma body argument a b domain_sort codomain_sort.
Proof.
  intros theta gamma body argument a b domain_sort codomain_sort
    Hdomain Hcodomain Hbody Hargument.
  pose proof (tdtt_typing_context_wf
    theta gamma a (utt_sort_term domain_sort) Hdomain) as Hcontext.
  assert (Hlambda :
    tdtt_has_type theta gamma (tLam body) (tPi a b)).
  { apply tdtt_ty_lam with
      (domain_sort := domain_sort)
      (codomain_sort := codomain_sort).
    - exact Hdomain.
    - exact Hcodomain.
    - exact Hbody. }
  assert (Happlication :
    tdtt_has_type theta gamma
      (tApp (tLam body) argument)
      (subst_term argument 0 b)).
  { apply tdtt_ty_app with (a := a) (b := b).
    - exact Hlambda.
    - exact Hargument. }
  pose proof (tdtt_has_type_substitute_top
    theta gamma argument a body b Hcontext Hargument Hbody) as Hreduct.
  pose proof (tdtt_typable_supports
    theta gamma (tLam body) (tPi a b) Hlambda)
    as [Hlambda_support Hfunction_type_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (tApp (tLam body) argument)
    (subst_term argument 0 b)
    Happlication) as [Happlication_support Hresult_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (subst_term argument 0 body)
    (subst_term argument 0 b)
    Hreduct) as [Hreduct_support _].
  pose proof (tdtt_typable_supports
    theta gamma a (utt_sort_term domain_sort) Hdomain)
    as [Ha_support _].
  pose proof (tdtt_typable_supports
    theta (a :: gamma) b (utt_sort_term codomain_sort) Hcodomain)
    as [Hb_support _].
  pose proof (tdtt_typable_supports
    theta (a :: gamma) body b Hbody)
    as [Hbody_support _].
  pose proof (tdtt_typable_supports
    theta gamma argument a Hargument)
    as [Hargument_support _].
  constructor.
  - exact Hcontext.
  - exact Hdomain.
  - exact Hcodomain.
  - exact Hbody.
  - exact Hargument.
  - exact Hlambda.
  - exact Happlication.
  - exact Hreduct.
  - apply de_beta.
  - exact Hlambda_support.
  - exact Happlication_support.
  - exact Hreduct_support.
  - exact Hresult_support.
  - exact Hfunction_type_support.
  - exact Ha_support.
  - exact Hb_support.
  - exact Hbody_support.
  - exact Hargument_support.
Qed.

Record tdtt_fix_unfold_regular
    (theta : temporal_context) (gamma : context)
    (body a : term) (sort : utt_sort) : Prop := {
  tdtt_fix_unfold_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_fix_unfold_regular_guarded_type :
    tdtt_has_type theta gamma a (utt_sort_term sort);
  tdtt_fix_unfold_regular_body_typing :
    tdtt_has_type theta
      (tLater a :: gamma)
      body
      (shift_term 1 0 a);
  tdtt_fix_unfold_regular_fix_typing :
    tdtt_has_type theta gamma (tFix body) a;
  tdtt_fix_unfold_regular_next_fix_typing :
    tdtt_has_type theta gamma (tNext (tFix body)) (tLater a);
  tdtt_fix_unfold_regular_reduct_typing :
    tdtt_has_type theta gamma
      (subst_term (tNext (tFix body)) 0 body)
      a;
  tdtt_fix_unfold_regular_defeq :
    defeq
      (tFix body)
      (subst_term (tNext (tFix body)) 0 body);
  tdtt_fix_unfold_regular_fix_support :
    supports TDTT (tFix body) = true;
  tdtt_fix_unfold_regular_next_fix_support :
    supports TDTT (tNext (tFix body)) = true;
  tdtt_fix_unfold_regular_later_type_support :
    supports TDTT (tLater a) = true;
  tdtt_fix_unfold_regular_reduct_support :
    supports TDTT (subst_term (tNext (tFix body)) 0 body) = true;
  tdtt_fix_unfold_regular_guarded_type_support :
    supports TDTT a = true;
  tdtt_fix_unfold_regular_body_support :
    supports TDTT body = true
}.

Theorem tdtt_fix_unfold_is_regular :
  forall theta gamma body a sort,
    tdtt_has_type theta gamma a (utt_sort_term sort) ->
    tdtt_has_type theta
      (tLater a :: gamma)
      body
      (shift_term 1 0 a) ->
    tdtt_fix_unfold_regular theta gamma body a sort.
Proof.
  intros theta gamma body a sort Ha Hbody.
  pose proof (tdtt_typing_context_wf
    theta gamma a (utt_sort_term sort) Ha) as Hcontext.
  assert (Hfix : tdtt_has_type theta gamma (tFix body) a).
  { apply tdtt_ty_fix with (sort := sort).
    - exact Ha.
    - exact Hbody. }
  assert (Hnext_fix :
    tdtt_has_type theta gamma (tNext (tFix body)) (tLater a)).
  { apply tdtt_ty_next.
    exact Hfix. }
  pose proof (tdtt_has_type_substitute_top
    theta
    gamma
    (tNext (tFix body))
    (tLater a)
    body
    (shift_term 1 0 a)
    Hcontext
    Hnext_fix
    Hbody) as Hreduct.
  rewrite subst_term_shift_cancel in Hreduct.
  pose proof (tdtt_typable_supports
    theta gamma (tFix body) a Hfix) as [Hfix_support Ha_support].
  pose proof (tdtt_typable_supports
    theta gamma (tNext (tFix body)) (tLater a) Hnext_fix)
    as [Hnext_fix_support Hlater_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (subst_term (tNext (tFix body)) 0 body)
    a
    Hreduct) as [Hreduct_support _].
  pose proof (tdtt_typable_supports
    theta (tLater a :: gamma) body (shift_term 1 0 a) Hbody)
    as [Hbody_support _].
  constructor.
  - exact Hcontext.
  - exact Ha.
  - exact Hbody.
  - exact Hfix.
  - exact Hnext_fix.
  - exact Hreduct.
  - apply de_fix_unfold.
  - exact Hfix_support.
  - exact Hnext_fix_support.
  - exact Hlater_support.
  - exact Hreduct_support.
  - exact Ha_support.
  - exact Hbody_support.
Qed.

Theorem tdtt_fix_unfold_from_fix_typing_is_regular :
  forall theta gamma body result,
    tdtt_has_type theta gamma (tFix body) result ->
    exists a sort,
      tdtt_fix_unfold_regular theta gamma body a sort.
Proof.
  intros theta gamma body result Htyping.
  destruct (tdtt_fix_typing_inversion theta gamma body result Htyping)
    as [a [sort [Ha Hbody]]].
  exists a, sort.
  apply tdtt_fix_unfold_is_regular.
  - exact Ha.
  - exact Hbody.
Qed.

Record tdtt_fix_at_unfold_regular
    (theta : temporal_context) (gamma : context)
    (clock body a : term) (sort : utt_sort) : Prop := {
  tdtt_fix_at_unfold_regular_context_wf :
    tdtt_wf_context theta gamma;
  tdtt_fix_at_unfold_regular_clock_wf :
    temporal_wf theta clock;
  tdtt_fix_at_unfold_regular_guarded_type :
    tdtt_has_type theta gamma a (utt_sort_term sort);
  tdtt_fix_at_unfold_regular_body_typing :
    tdtt_has_type theta
      (tLaterAt clock a :: gamma)
      body
      (shift_term 1 0 a);
  tdtt_fix_at_unfold_regular_fix_typing :
    tdtt_has_type theta gamma (tFixAt clock body) a;
  tdtt_fix_at_unfold_regular_next_fix_typing :
    tdtt_has_type theta gamma
      (tNextAt clock (tFixAt clock body))
      (tLaterAt clock a);
  tdtt_fix_at_unfold_regular_reduct_typing :
    tdtt_has_type theta gamma
      (subst_term (tNextAt clock (tFixAt clock body)) 0 body)
      a;
  tdtt_fix_at_unfold_regular_defeq :
    defeq
      (tFixAt clock body)
      (subst_term (tNextAt clock (tFixAt clock body)) 0 body);
  tdtt_fix_at_unfold_regular_fix_support :
    supports TDTT (tFixAt clock body) = true;
  tdtt_fix_at_unfold_regular_next_fix_support :
    supports TDTT (tNextAt clock (tFixAt clock body)) = true;
  tdtt_fix_at_unfold_regular_later_type_support :
    supports TDTT (tLaterAt clock a) = true;
  tdtt_fix_at_unfold_regular_clock_support :
    supports TDTT clock = true;
  tdtt_fix_at_unfold_regular_reduct_support :
    supports TDTT
      (subst_term (tNextAt clock (tFixAt clock body)) 0 body) = true;
  tdtt_fix_at_unfold_regular_guarded_type_support :
    supports TDTT a = true;
  tdtt_fix_at_unfold_regular_body_support :
    supports TDTT body = true
}.

Theorem tdtt_fix_at_unfold_is_regular :
  forall theta gamma clock body a sort,
    temporal_wf theta clock ->
    tdtt_has_type theta gamma a (utt_sort_term sort) ->
    tdtt_has_type theta
      (tLaterAt clock a :: gamma)
      body
      (shift_term 1 0 a) ->
    tdtt_fix_at_unfold_regular theta gamma clock body a sort.
Proof.
  intros theta gamma clock body a sort Hclock Ha Hbody.
  pose proof (tdtt_typing_context_wf
    theta gamma a (utt_sort_term sort) Ha) as Hcontext.
  assert (Hfix :
    tdtt_has_type theta gamma (tFixAt clock body) a).
  { apply tdtt_ty_fix_at with (sort := sort).
    - exact Hclock.
    - exact Ha.
    - exact Hbody. }
  assert (Hnext_fix :
    tdtt_has_type theta gamma
      (tNextAt clock (tFixAt clock body))
      (tLaterAt clock a)).
  { apply tdtt_ty_next_at.
    - exact Hclock.
    - exact Hfix. }
  pose proof (tdtt_has_type_substitute_top
    theta
    gamma
    (tNextAt clock (tFixAt clock body))
    (tLaterAt clock a)
    body
    (shift_term 1 0 a)
    Hcontext
    Hnext_fix
    Hbody) as Hreduct.
  rewrite subst_term_shift_cancel in Hreduct.
  pose proof (tdtt_typable_supports
    theta gamma (tFixAt clock body) a Hfix)
    as [Hfix_support Ha_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (tNextAt clock (tFixAt clock body))
    (tLaterAt clock a)
    Hnext_fix) as [Hnext_fix_support Hlater_at_support].
  pose proof (tdtt_typable_supports
    theta gamma
    (subst_term (tNextAt clock (tFixAt clock body)) 0 body)
    a
    Hreduct) as [Hreduct_support _].
  pose proof (tdtt_typable_supports
    theta (tLaterAt clock a :: gamma) body (shift_term 1 0 a) Hbody)
    as [Hbody_support _].
  pose proof (temporal_wf_supports_tdtt theta clock Hclock)
    as Hclock_support.
  constructor.
  - exact Hcontext.
  - exact Hclock.
  - exact Ha.
  - exact Hbody.
  - exact Hfix.
  - exact Hnext_fix.
  - exact Hreduct.
  - apply de_fix_at_unfold.
  - exact Hfix_support.
  - exact Hnext_fix_support.
  - exact Hlater_at_support.
  - exact Hclock_support.
  - exact Hreduct_support.
  - exact Ha_support.
  - exact Hbody_support.
Qed.

Theorem tdtt_fix_at_unfold_from_fix_typing_is_regular :
  forall theta gamma clock body result,
    tdtt_has_type theta gamma (tFixAt clock body) result ->
    exists a sort,
      tdtt_fix_at_unfold_regular theta gamma clock body a sort.
Proof.
  intros theta gamma clock body result Htyping.
  destruct (tdtt_fix_at_typing_inversion
    theta gamma clock body result Htyping)
    as [a [sort [Hclock [Ha Hbody]]]].
  exists a, sort.
  apply tdtt_fix_at_unfold_is_regular.
  - exact Hclock.
  - exact Ha.
  - exact Hbody.
Qed.

Record tdtt_typed_computation_regularities : Prop := {
  tdtt_computation_regular_beta :
    forall theta gamma body argument a b domain_sort codomain_sort,
      tdtt_has_type theta gamma a (utt_sort_term domain_sort) ->
      tdtt_has_type theta (a :: gamma) b (utt_sort_term codomain_sort) ->
      tdtt_has_type theta (a :: gamma) body b ->
      tdtt_has_type theta gamma argument a ->
      tdtt_beta_regular
        theta gamma body argument a b domain_sort codomain_sort;
  tdtt_computation_regular_clock_beta :
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
	  tdtt_clock_beta_regular theta gamma body a clock_index sort;
  tdtt_computation_regular_delayed_subst_compute :
    forall theta gamma body a clock_index,
      tdtt_wf_context theta gamma ->
      temporal_wf theta (tTimeVar clock_index) ->
      tdtt_has_type
        (tc_extend theta)
        (shift_time_context 1 0 gamma)
        body
        a ->
      tdtt_delayed_subst_compute_regular
        theta gamma body a clock_index;
  tdtt_computation_regular_fix_unfold :
    forall theta gamma body a sort,
      tdtt_has_type theta gamma a (utt_sort_term sort) ->
      tdtt_has_type theta
        (tLater a :: gamma)
        body
        (shift_term 1 0 a) ->
      tdtt_fix_unfold_regular theta gamma body a sort;
  tdtt_computation_regular_fix_unfold_from_typing :
    forall theta gamma body result,
      tdtt_has_type theta gamma (tFix body) result ->
      exists a sort,
        tdtt_fix_unfold_regular theta gamma body a sort;
  tdtt_computation_regular_fix_at_unfold :
    forall theta gamma clock body a sort,
      temporal_wf theta clock ->
      tdtt_has_type theta gamma a (utt_sort_term sort) ->
      tdtt_has_type theta
        (tLaterAt clock a :: gamma)
        body
        (shift_term 1 0 a) ->
      tdtt_fix_at_unfold_regular theta gamma clock body a sort;
  tdtt_computation_regular_fix_at_unfold_from_typing :
    forall theta gamma clock body result,
      tdtt_has_type theta gamma (tFixAt clock body) result ->
      exists a sort,
        tdtt_fix_at_unfold_regular theta gamma clock body a sort
}.

Theorem tdtt_typed_computation_regularities_hold :
  tdtt_typed_computation_regularities.
Proof.
  constructor.
  - intros theta gamma body argument a b domain_sort codomain_sort
      Hdomain Hcodomain Hbody Hargument.
    apply tdtt_beta_is_regular.
    + exact Hdomain.
    + exact Hcodomain.
    + exact Hbody.
    + exact Hargument.
  - intros theta gamma body a clock_index sort
      Hcontext Hclock Ha Hbody.
    apply tdtt_clock_beta_is_regular.
    + exact Hcontext.
    + exact Hclock.
    + exact Ha.
    + exact Hbody.
  - intros theta gamma body a clock_index Hcontext Hclock Hbody.
    apply tdtt_delayed_subst_compute_is_regular.
    + exact Hcontext.
    + exact Hclock.
    + exact Hbody.
  - intros theta gamma body a sort Ha Hbody.
    apply tdtt_fix_unfold_is_regular.
    + exact Ha.
    + exact Hbody.
  - intros theta gamma body result Htyping.
    apply tdtt_fix_unfold_from_fix_typing_is_regular
      with (result := result).
    exact Htyping.
  - intros theta gamma clock body a sort Hclock Ha Hbody.
    apply tdtt_fix_at_unfold_is_regular.
    + exact Hclock.
    + exact Ha.
    + exact Hbody.
  - intros theta gamma clock body result Htyping.
    apply tdtt_fix_at_unfold_from_fix_typing_is_regular
      with (result := result).
    exact Htyping.
Qed.

Record tdtt_delayed_substitution_regularities : Prop := {
  tdtt_delayed_substitution_regular_support :
    forall clock body,
      supports TDTT clock = true ->
      supports TDTT body = true ->
      supports TDTT (delayed_substitution_term clock body) = true;
  tdtt_delayed_substitution_regular_context_preservation :
    forall theta gamma clock,
      temporal_wf theta clock ->
      tdtt_wf_context
        (tc_extend theta)
        (shift_time_context 1 0 gamma) ->
      tdtt_wf_context theta
        (delayed_substitution_context clock gamma);
  tdtt_delayed_substitution_regular_context_cancel :
    forall clock gamma,
      delayed_substitution_context clock gamma = gamma;
  tdtt_delayed_substitution_regular_typing_preservation :
    forall theta gamma clock body a,
      temporal_wf theta clock ->
      tdtt_has_type
        (tc_extend theta)
        (shift_time_context 1 0 gamma)
        body
        a ->
      tdtt_has_type theta gamma
        (delayed_substitution_term clock body)
        (delayed_substitution_term clock a);
  tdtt_delayed_substitution_regular_clock_lam_application :
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
        (delayed_substitution_term clock a);
	  tdtt_delayed_substitution_regular_native_typing :
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
	        (delayed_substitution_term clock a);
  tdtt_delayed_substitution_regular_native_inversion :
    forall theta gamma clock body result,
      tdtt_has_type theta gamma (tDelayedSubst clock body) result ->
      exists a,
        tdtt_delayed_subst_inversion_regular
          theta gamma clock body result a;
  tdtt_delayed_substitution_regular_clock_beta :
    forall body clock_index,
      defeq
        (tClockApp (tClockLam body) (tTimeVar clock_index))
        (delayed_substitution_term (tTimeVar clock_index) body);
  tdtt_delayed_substitution_regular_native_compute :
    forall body clock_index,
      defeq
        (tDelayedSubst (tTimeVar clock_index) body)
        (delayed_substitution_term (tTimeVar clock_index) body);
  tdtt_delayed_substitution_regular_native_congruence :
    forall clock clock' body body',
      defeq clock clock' ->
      defeq body body' ->
      defeq
        (tDelayedSubst clock body)
        (tDelayedSubst clock' body');
  tdtt_delayed_substitution_regular_clock_native_agreement :
    forall body clock_index,
      defeq
        (tClockApp (tClockLam body) (tTimeVar clock_index))
        (tDelayedSubst (tTimeVar clock_index) body);
  tdtt_delayed_substitution_regular_typed_native_agreement :
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
        (tDelayedSubst (tTimeVar clock_index) body);
  tdtt_delayed_substitution_regular_typed_native_agreement_regular :
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
      tdtt_clock_native_agreement_regular
        theta gamma body a clock_index sort;
  tdtt_delayed_substitution_regular_typed_native_congruence_regular :
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
      tdtt_native_delayed_substitution_congruence_regular
        theta gamma clock clock' body body' a a'
}.

Theorem tdtt_delayed_substitution_regularities_hold :
  tdtt_delayed_substitution_regularities.
Proof.
  constructor.
  - intros clock body Hclock Hbody.
    apply delayed_substitution_supports_tdtt.
    + exact Hclock.
    + exact Hbody.
  - intros theta gamma clock Hclock Hcontext.
    apply tdtt_delayed_substitution_preserves_context.
    + exact Hclock.
    + exact Hcontext.
  - intros clock gamma.
    apply delayed_substitution_context_cancel.
  - intros theta gamma clock body a Hclock Hbody.
    apply tdtt_delayed_substitution_preserves_typing_in_context.
    + exact Hclock.
    + exact Hbody.
  - intros theta gamma clock body a sort Hcontext Hclock Ha Hbody.
    apply tdtt_clock_lam_application_has_delayed_type
      with (sort := sort).
    + exact Hcontext.
    + exact Hclock.
    + exact Ha.
    + exact Hbody.
	  - intros theta gamma clock body a Hcontext Hclock Hbody.
	    apply tdtt_native_delayed_substitution_has_delayed_type.
	    + exact Hcontext.
	    + exact Hclock.
	    + exact Hbody.
  - intros theta gamma clock body result Htyping.
    apply tdtt_delayed_subst_typing_inversion_is_regular.
    exact Htyping.
  - intros body clock_index.
    apply clock_beta_is_delayed_substitution.
  - intros body clock_index.
    apply native_delayed_substitution_computes.
  - intros clock clock' body body' Hclock Hbody.
    apply native_delayed_substitution_congruence.
    + exact Hclock.
    + exact Hbody.
  - intros body clock_index.
    apply clock_application_agrees_with_native_delayed_substitution.
  - intros theta gamma body a clock_index sort Hcontext Hclock Ha Hbody.
    apply tdtt_clock_application_native_delayed_substitution_typed_agreement
      with (sort := sort).
    + exact Hcontext.
    + exact Hclock.
    + exact Ha.
    + exact Hbody.
  - intros theta gamma body a clock_index sort Hcontext Hclock Ha Hbody.
    apply tdtt_clock_native_agreement_is_regular.
    + exact Hcontext.
    + exact Hclock.
    + exact Ha.
    + exact Hbody.
  - intros theta gamma clock clock' body body' a a'
      Hcontext Hclock Hclock' Hbody Hbody' Hclock_defeq Hbody_defeq.
    apply tdtt_native_delayed_substitution_congruence_is_regular.
    + exact Hcontext.
    + exact Hclock.
    + exact Hclock'.
    + exact Hbody.
    + exact Hbody'.
    + exact Hclock_defeq.
    + exact Hbody_defeq.
Qed.

Record type_theory_atlas_metatheory_regularities : Prop := {
  atlas_mltt_typing_support :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_utt_typing_support :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_tdtt_typing_support :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_mltt_to_utt_translation :
    forall gamma t a,
      has_type gamma t a ->
      mltt_to_utt_translation_regular gamma t a;
  atlas_utt_to_tdtt_translation :
    forall theta gamma t a,
      utt_has_type gamma t a ->
      utt_to_tdtt_translation_regular theta gamma t a;
  atlas_mltt_to_tdtt_translation :
    forall theta gamma t a,
      has_type gamma t a ->
      mltt_to_tdtt_translation_regular theta gamma t a;
  atlas_tdtt_typed_conversion :
    forall theta gamma t a b sort,
      tdtt_has_type theta gamma t a ->
      tdtt_has_type theta gamma b (utt_sort_term sort) ->
      defeq a b ->
      tdtt_typed_conversion_regular theta gamma t a b sort;
  atlas_tdtt_typed_defeq :
    forall theta gamma a b left_sort right_sort,
      tdtt_has_type theta gamma a (utt_sort_term left_sort) ->
      tdtt_has_type theta gamma b (utt_sort_term right_sort) ->
      defeq a b ->
      tdtt_typed_defeq_regular theta gamma a b left_sort right_sort;
  atlas_tdtt_context_extension :
    forall theta gamma a,
      tdtt_wf_context theta (a :: gamma) ->
      exists sort,
        tdtt_context_extension_regular theta gamma a sort;
  atlas_tdtt_context_lookup :
    forall theta gamma index a,
      tdtt_wf_context theta gamma ->
      lookup gamma index a ->
      tdtt_context_lookup_regular theta gamma index a;
  atlas_tdtt_temporal_lookup :
    forall theta index,
      temporal_lookup theta index ->
      tdtt_temporal_lookup_regular theta index;
  atlas_tdtt_temporal_wf :
    forall theta time,
      temporal_wf theta time ->
      tdtt_temporal_wf_regular theta time;
  atlas_tdtt_at_constructor :
    forall theta gamma a time result,
      tdtt_has_type theta gamma (tAt a time) result ->
      exists sort,
        tdtt_at_constructor_regular theta gamma a time result sort;
  atlas_tdtt_later_at_constructor :
    forall theta gamma clock a result,
      tdtt_has_type theta gamma (tLaterAt clock a) result ->
      exists sort,
        tdtt_later_at_constructor_regular theta gamma clock a result sort;
  atlas_tdtt_next_at_constructor :
    forall theta gamma clock t result,
      tdtt_has_type theta gamma (tNextAt clock t) result ->
      exists a,
        tdtt_next_at_constructor_regular theta gamma clock t result a;
  atlas_tdtt_fix_at_constructor :
    forall theta gamma clock body result,
      tdtt_has_type theta gamma (tFixAt clock body) result ->
      exists a sort,
        tdtt_fix_at_constructor_regular
          theta gamma clock body result a sort;
  atlas_tdtt_clock_pi_constructor :
    forall theta gamma a result,
      tdtt_has_type theta gamma (tClockPi a) result ->
      exists sort,
        tdtt_clock_pi_constructor_regular theta gamma a result sort;
  atlas_tdtt_clock_lam_constructor :
    forall theta gamma body result,
      tdtt_has_type theta gamma (tClockLam body) result ->
      exists a sort,
        tdtt_clock_lam_constructor_regular
          theta gamma body result a sort;
  atlas_tdtt_clock_app_constructor :
    forall theta gamma f clock result,
      tdtt_has_type theta gamma (tClockApp f clock) result ->
      exists a,
        tdtt_clock_app_constructor_regular theta gamma f clock result a;
  atlas_tdtt_delayed_subst_constructor :
    forall theta gamma clock body result,
      tdtt_has_type theta gamma (tDelayedSubst clock body) result ->
      exists a,
        tdtt_delayed_subst_constructor_regular
          theta gamma clock body result a;
  atlas_tdtt_typed_computation :
    tdtt_typed_computation_regularities;
  atlas_tdtt_delayed_substitution :
    tdtt_delayed_substitution_regularities
}.

Theorem type_theory_atlas_metatheory_regularities_hold :
  type_theory_atlas_metatheory_regularities.
Proof.
  constructor.
  - intros gamma t a Htyping.
    apply (mltt_typable_supports gamma t a).
    exact Htyping.
  - intros gamma t a Htyping.
    apply (utt_typable_supports gamma t a).
    exact Htyping.
  - intros theta gamma t a Htyping.
    apply (tdtt_typable_supports theta gamma t a).
    exact Htyping.
  - intros gamma t a Htyping.
    apply mltt_translation_to_utt_regular.
    exact Htyping.
  - intros theta gamma t a Htyping.
    apply utt_translation_to_tdtt_regular.
    exact Htyping.
  - intros theta gamma t a Htyping.
    apply mltt_translation_to_tdtt_regular.
    exact Htyping.
  - intros theta gamma t a b sort Htyping Htarget Heq.
    apply tdtt_typed_conversion_is_regular.
    + exact Htyping.
    + exact Htarget.
    + exact Heq.
  - intros theta gamma a b left_sort right_sort Hleft Hright Heq.
    apply tdtt_typed_defeq_is_regular.
    + exact Hleft.
    + exact Hright.
    + exact Heq.
  - intros theta gamma a Hcontext.
    apply tdtt_context_extension_is_regular.
    exact Hcontext.
  - intros theta gamma index a Hcontext Hlookup.
    apply tdtt_context_lookup_is_regular.
    + exact Hcontext.
    + exact Hlookup.
  - intros theta index Hlookup.
    apply tdtt_temporal_lookup_is_regular.
    exact Hlookup.
  - intros theta time Htime.
    apply tdtt_temporal_wf_is_regular.
    exact Htime.
  - intros theta gamma a time result Htyping.
    apply tdtt_at_constructor_is_regular.
    exact Htyping.
  - intros theta gamma clock a result Htyping.
    apply tdtt_later_at_constructor_is_regular.
    exact Htyping.
  - intros theta gamma clock t result Htyping.
    apply tdtt_next_at_constructor_is_regular.
    exact Htyping.
  - intros theta gamma clock body result Htyping.
    apply tdtt_fix_at_constructor_is_regular.
    exact Htyping.
  - intros theta gamma a result Htyping.
    apply tdtt_clock_pi_constructor_is_regular.
    exact Htyping.
  - intros theta gamma body result Htyping.
    apply tdtt_clock_lam_constructor_is_regular.
    exact Htyping.
  - intros theta gamma f clock result Htyping.
    apply tdtt_clock_app_constructor_is_regular.
    exact Htyping.
  - intros theta gamma clock body result Htyping.
    apply tdtt_delayed_subst_constructor_is_regular.
    exact Htyping.
  - apply tdtt_typed_computation_regularities_hold.
  - apply tdtt_delayed_substitution_regularities_hold.
Qed.

Record atlas_delayed_substitution_translation_summary : Prop := {
  atlas_delayed_summary_mltt_rejects_native :
    supports MLTT (tDelayedSubst (tTimeVar 0) tProp) = false;
  atlas_delayed_summary_utt_rejects_native :
    supports UTT (tDelayedSubst (tTimeVar 0) tProp) = false;
  atlas_delayed_summary_tdtt_accepts_native :
    supports TDTT (tDelayedSubst (tTimeVar 0) tProp) = true;
  atlas_delayed_summary_mltt_to_utt_support :
    forall t,
      supports MLTT t = true ->
      supports UTT (mltt_to_utt t) = true;
  atlas_delayed_summary_utt_to_tdtt_support :
    forall t,
      supports UTT t = true ->
      supports TDTT (utt_to_tdtt t) = true;
  atlas_delayed_summary_mltt_to_tdtt_support :
    forall t,
      supports MLTT t = true ->
      supports TDTT (mltt_to_tdtt t) = true;
  atlas_delayed_summary_tdtt_native_typing :
    tdtt_has_type
      (tc_extend tc_empty)
      []
      (tDelayedSubst (tTimeVar 0) tProp)
      (tUniverse 0);
  atlas_delayed_summary_tdtt_native_compute :
    defeq (tDelayedSubst (tTimeVar 0) tProp) tProp;
  atlas_delayed_summary_typed_computation :
    tdtt_typed_computation_regularities;
  atlas_delayed_summary_delayed_regularities :
    tdtt_delayed_substitution_regularities
}.

Theorem atlas_delayed_substitution_translation_summary_holds :
  atlas_delayed_substitution_translation_summary.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t Hsupport.
    apply mltt_supports_utt.
    exact Hsupport.
  - intros t Hsupport.
    apply utt_supports_tdtt.
    exact Hsupport.
  - intros t Hsupport.
    apply mltt_supports_tdtt.
    exact Hsupport.
  - apply tdtt_delayed_substitution_prop.
  - apply de_delayed_subst_compute.
  - apply tdtt_typed_computation_regularities_hold.
  - apply tdtt_delayed_substitution_regularities_hold.
Qed.

Record atlas_feature_boundary_summary : Prop := {
  atlas_feature_summary_mltt_to_utt_support :
    forall t,
      supports MLTT t = true ->
      supports UTT (mltt_to_utt t) = true;
  atlas_feature_summary_utt_to_tdtt_support :
    forall t,
      supports UTT t = true ->
      supports TDTT (utt_to_tdtt t) = true;
  atlas_feature_summary_mltt_to_tdtt_support :
    forall t,
      supports MLTT t = true ->
      supports TDTT (mltt_to_tdtt t) = true;
  atlas_feature_summary_mltt_rejects_prop :
    supports MLTT tProp = false;
  atlas_feature_summary_mltt_rejects_time :
    supports MLTT (tTimeVar 0) = false;
  atlas_feature_summary_mltt_rejects_temporal_operator :
    supports MLTT temporal_identity = false;
  atlas_feature_summary_mltt_rejects_guarded_fix :
    supports MLTT (tFix tProp) = false;
  atlas_feature_summary_mltt_rejects_clock_quantification :
    supports MLTT (tClockPi tProp) = false;
  atlas_feature_summary_mltt_rejects_delayed_substitution :
    supports MLTT (tDelayedSubst (tTimeVar 0) tProp) = false;
  atlas_feature_summary_utt_accepts_prop :
    supports UTT tProp = true;
  atlas_feature_summary_utt_rejects_time :
    supports UTT (tTimeVar 0) = false;
  atlas_feature_summary_utt_rejects_temporal_operator :
    supports UTT temporal_identity = false;
  atlas_feature_summary_utt_rejects_guarded_fix :
    supports UTT (tFix tProp) = false;
  atlas_feature_summary_utt_rejects_clock_quantification :
    supports UTT (tClockPi tProp) = false;
  atlas_feature_summary_utt_rejects_delayed_substitution :
    supports UTT (tDelayedSubst (tTimeVar 0) tProp) = false;
  atlas_feature_summary_tdtt_accepts_prop :
    supports TDTT tProp = true;
  atlas_feature_summary_tdtt_accepts_time :
    supports TDTT (tTimeVar 0) = true;
  atlas_feature_summary_tdtt_accepts_temporal_operator :
    supports TDTT temporal_identity = true;
  atlas_feature_summary_tdtt_accepts_guarded_fix :
    supports TDTT (tFix tProp) = true;
  atlas_feature_summary_tdtt_accepts_clock_quantification :
    supports TDTT (tClockPi tProp) = true;
  atlas_feature_summary_tdtt_accepts_delayed_substitution :
    supports TDTT (tDelayedSubst (tTimeVar 0) tProp) = true;
  atlas_feature_summary_tdtt_accepts_clock_beta_redex :
    supports TDTT
      (tClockApp (tClockLam tProp) (tTimeVar 0)) = true
}.

Theorem atlas_feature_boundary_summary_holds :
  atlas_feature_boundary_summary.
Proof.
  constructor.
  - intros t Hsupport.
    apply mltt_supports_utt.
    exact Hsupport.
  - intros t Hsupport.
    apply utt_supports_tdtt.
    exact Hsupport.
  - intros t Hsupport.
    apply mltt_supports_tdtt.
    exact Hsupport.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Record atlas_translation_reliability_summary : Prop := {
  atlas_translation_summary_feature_boundaries :
    atlas_feature_boundary_summary;
  atlas_translation_summary_mltt_to_utt_context :
    forall gamma,
      wf_context gamma ->
      utt_wf_context (mltt_context_to_utt gamma);
  atlas_translation_summary_utt_to_tdtt_context :
    forall theta gamma,
      utt_wf_context gamma ->
      tdtt_wf_context theta (utt_context_to_tdtt gamma);
  atlas_translation_summary_mltt_to_tdtt_context :
    forall theta gamma,
      wf_context gamma ->
      tdtt_wf_context theta (mltt_context_to_tdtt gamma);
  atlas_translation_summary_mltt_to_utt_context_support :
    forall gamma,
      context_supports MLTT gamma ->
      context_supports UTT (mltt_context_to_utt gamma);
  atlas_translation_summary_utt_to_tdtt_context_support :
    forall gamma,
      context_supports UTT gamma ->
      context_supports TDTT (utt_context_to_tdtt gamma);
  atlas_translation_summary_mltt_to_tdtt_context_support :
    forall gamma,
      context_supports MLTT gamma ->
      context_supports TDTT (mltt_context_to_tdtt gamma);
  atlas_translation_summary_mltt_to_utt_typing :
    forall gamma t a,
      has_type gamma t a ->
      mltt_to_utt_translation_regular gamma t a;
  atlas_translation_summary_utt_to_tdtt_typing :
    forall theta gamma t a,
      utt_has_type gamma t a ->
      utt_to_tdtt_translation_regular theta gamma t a;
  atlas_translation_summary_mltt_to_tdtt_typing :
    forall theta gamma t a,
      has_type gamma t a ->
      mltt_to_tdtt_translation_regular theta gamma t a;
  atlas_translation_summary_mltt_to_utt_defeq :
    forall t u,
      defeq t u ->
      supports MLTT t = true ->
      supports MLTT u = true ->
      mltt_to_utt_defeq_regular t u;
  atlas_translation_summary_utt_to_tdtt_defeq :
    forall t u,
      defeq t u ->
      supports UTT t = true ->
      supports UTT u = true ->
      utt_to_tdtt_defeq_regular t u;
  atlas_translation_summary_mltt_to_tdtt_defeq :
    forall t u,
      defeq t u ->
      supports MLTT t = true ->
      supports MLTT u = true ->
      mltt_to_tdtt_defeq_regular t u
}.

Theorem atlas_translation_reliability_summary_holds :
  atlas_translation_reliability_summary.
Proof.
  constructor.
  - apply atlas_feature_boundary_summary_holds.
  - intros gamma Hcontext.
    apply mltt_translation_to_utt_preserves_context.
    exact Hcontext.
  - intros theta gamma Hcontext.
    apply utt_translation_to_tdtt_preserves_context.
    exact Hcontext.
  - intros theta gamma Hcontext.
    apply mltt_translation_to_tdtt_preserves_context.
    exact Hcontext.
  - intros gamma Hsupport.
    apply mltt_context_supports_utt_translation.
    exact Hsupport.
  - intros gamma Hsupport.
    apply utt_context_supports_tdtt_translation.
    exact Hsupport.
  - intros gamma Hsupport.
    apply mltt_context_supports_tdtt_translation.
    exact Hsupport.
  - intros gamma t a Htyping.
    apply mltt_translation_to_utt_regular.
    exact Htyping.
  - intros theta gamma t a Htyping.
    apply utt_translation_to_tdtt_regular.
    exact Htyping.
  - intros theta gamma t a Htyping.
    apply mltt_translation_to_tdtt_regular.
    exact Htyping.
  - intros t u Heq Ht Hu.
    apply mltt_translation_to_utt_defeq_regular.
    + exact Heq.
    + exact Ht.
    + exact Hu.
  - intros t u Heq Ht Hu.
    apply utt_translation_to_tdtt_defeq_regular.
    + exact Heq.
    + exact Ht.
    + exact Hu.
  - intros t u Heq Ht Hu.
    apply mltt_translation_to_tdtt_defeq_regular.
    + exact Heq.
    + exact Ht.
    + exact Hu.
Qed.

Record atlas_tdtt_constructor_regularities_summary : Prop := {
  atlas_constructor_summary_at :
    forall theta gamma a time result,
      tdtt_has_type theta gamma (tAt a time) result ->
      exists sort,
        tdtt_at_constructor_regular theta gamma a time result sort;
  atlas_constructor_summary_later_at :
    forall theta gamma clock a result,
      tdtt_has_type theta gamma (tLaterAt clock a) result ->
      exists sort,
        tdtt_later_at_constructor_regular theta gamma clock a result sort;
  atlas_constructor_summary_next_at :
    forall theta gamma clock t result,
      tdtt_has_type theta gamma (tNextAt clock t) result ->
      exists a,
        tdtt_next_at_constructor_regular theta gamma clock t result a;
  atlas_constructor_summary_fix_at :
    forall theta gamma clock body result,
      tdtt_has_type theta gamma (tFixAt clock body) result ->
      exists a sort,
        tdtt_fix_at_constructor_regular
          theta gamma clock body result a sort;
  atlas_constructor_summary_clock_pi :
    forall theta gamma a result,
      tdtt_has_type theta gamma (tClockPi a) result ->
      exists sort,
        tdtt_clock_pi_constructor_regular theta gamma a result sort;
  atlas_constructor_summary_clock_lam :
    forall theta gamma body result,
      tdtt_has_type theta gamma (tClockLam body) result ->
      exists a sort,
        tdtt_clock_lam_constructor_regular
          theta gamma body result a sort;
  atlas_constructor_summary_clock_app :
    forall theta gamma f clock result,
      tdtt_has_type theta gamma (tClockApp f clock) result ->
      exists a,
        tdtt_clock_app_constructor_regular theta gamma f clock result a;
  atlas_constructor_summary_delayed_subst :
    forall theta gamma clock body result,
      tdtt_has_type theta gamma (tDelayedSubst clock body) result ->
      exists a,
        tdtt_delayed_subst_constructor_regular
          theta gamma clock body result a
}.

Theorem atlas_tdtt_constructor_regularities_summary_holds :
  atlas_tdtt_constructor_regularities_summary.
Proof.
  constructor.
  - intros theta gamma a time result Htyping.
    apply tdtt_at_constructor_is_regular.
    exact Htyping.
  - intros theta gamma clock a result Htyping.
    apply tdtt_later_at_constructor_is_regular.
    exact Htyping.
  - intros theta gamma clock t result Htyping.
    apply tdtt_next_at_constructor_is_regular.
    exact Htyping.
  - intros theta gamma clock body result Htyping.
    apply tdtt_fix_at_constructor_is_regular.
    exact Htyping.
  - intros theta gamma a result Htyping.
    apply tdtt_clock_pi_constructor_is_regular.
    exact Htyping.
  - intros theta gamma body result Htyping.
    apply tdtt_clock_lam_constructor_is_regular.
    exact Htyping.
  - intros theta gamma f clock result Htyping.
    apply tdtt_clock_app_constructor_is_regular.
    exact Htyping.
  - intros theta gamma clock body result Htyping.
    apply tdtt_delayed_subst_constructor_is_regular.
    exact Htyping.
Qed.

Record atlas_tdtt_regularity_dashboard : Prop := {
  atlas_dashboard_feature_boundaries :
    atlas_feature_boundary_summary;
  atlas_dashboard_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_dashboard_metatheory :
    type_theory_atlas_metatheory_regularities;
  atlas_dashboard_constructor_regularities :
    atlas_tdtt_constructor_regularities_summary;
  atlas_dashboard_typed_computation :
    tdtt_typed_computation_regularities;
  atlas_dashboard_delayed_substitution :
    tdtt_delayed_substitution_regularities;
  atlas_dashboard_delayed_translation :
    atlas_delayed_substitution_translation_summary
}.

Theorem atlas_tdtt_regularity_dashboard_holds :
  atlas_tdtt_regularity_dashboard.
Proof.
  constructor.
  - apply atlas_feature_boundary_summary_holds.
  - apply atlas_translation_reliability_summary_holds.
  - apply type_theory_atlas_metatheory_regularities_hold.
  - apply atlas_tdtt_constructor_regularities_summary_holds.
  - apply tdtt_typed_computation_regularities_hold.
  - apply tdtt_delayed_substitution_regularities_hold.
  - apply atlas_delayed_substitution_translation_summary_holds.
Qed.

Record type_theory_atlas_coverage : Prop := {
  atlas_coverage_mltt_dependent_functions :
    supports MLTT (tPi (tUniverse 0) (tVar 0)) = true;
  atlas_coverage_mltt_rejects_propositions :
    supports MLTT tProp = false;
  atlas_coverage_mltt_rejects_temporal_syntax :
    supports MLTT temporal_identity = false;
  atlas_coverage_utt_dependent_pairs :
    supports UTT (tSigma (tUniverse 0) (tVar 0)) = true;
  atlas_coverage_utt_propositions :
    supports UTT tProp = true;
  atlas_coverage_utt_rejects_temporal_syntax :
    supports UTT temporal_identity = false;
  atlas_coverage_utt_rejects_guarded_fix :
    supports UTT (tFix tProp) = false;
  atlas_coverage_utt_rejects_clock_quantification :
    supports UTT (tClockPi tProp) = false;
  atlas_coverage_utt_rejects_delayed_substitution :
    supports UTT (tDelayedSubst (tTimeVar 0) tProp) = false;
  atlas_coverage_tdtt_temporal_syntax :
    supports TDTT temporal_identity = true;
  atlas_coverage_tdtt_guarded_fix :
    supports TDTT (tFix tProp) = true;
  atlas_coverage_tdtt_clocked_later :
    supports TDTT (tLaterAt (tTimeVar 0) tProp) = true;
  atlas_coverage_tdtt_clock_quantification :
    supports TDTT (tClockPi tProp) = true;
  atlas_coverage_tdtt_delayed_substitution_syntax :
    supports TDTT (tDelayedSubst (tTimeVar 0) tProp) = true;
  atlas_coverage_metatheory :
    type_theory_atlas_metatheory_regularities;
  atlas_coverage_typed_computation :
    tdtt_typed_computation_regularities;
  atlas_coverage_delayed_substitution :
    tdtt_delayed_substitution_regularities;
  atlas_coverage_delayed_translation_summary :
    atlas_delayed_substitution_translation_summary;
  atlas_coverage_feature_boundary_summary :
    atlas_feature_boundary_summary;
  atlas_coverage_translation_reliability_summary :
    atlas_translation_reliability_summary;
  atlas_coverage_tdtt_constructor_summary :
    atlas_tdtt_constructor_regularities_summary;
  atlas_coverage_tdtt_regularity_dashboard :
    atlas_tdtt_regularity_dashboard
}.

Theorem type_theory_atlas_coverage_holds :
  type_theory_atlas_coverage.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply type_theory_atlas_metatheory_regularities_hold.
  - apply tdtt_typed_computation_regularities_hold.
  - apply tdtt_delayed_substitution_regularities_hold.
  - apply atlas_delayed_substitution_translation_summary_holds.
  - apply atlas_feature_boundary_summary_holds.
  - apply atlas_translation_reliability_summary_holds.
  - apply atlas_tdtt_constructor_regularities_summary_holds.
  - apply atlas_tdtt_regularity_dashboard_holds.
Qed.

Record atlas_system_boundary_regularities : Prop := {
  atlas_boundary_mltt_to_utt_support :
    forall t,
      supports MLTT t = true ->
      supports UTT (mltt_to_utt t) = true;
  atlas_boundary_utt_to_tdtt_support :
    forall t,
      supports UTT t = true ->
      supports TDTT (utt_to_tdtt t) = true;
  atlas_boundary_mltt_to_tdtt_support :
    forall t,
      supports MLTT t = true ->
      supports TDTT (mltt_to_tdtt t) = true;
  atlas_boundary_mltt_rejects_prop :
    supports MLTT tProp = false;
  atlas_boundary_mltt_rejects_time :
    supports MLTT (tTimeVar 0) = false;
  atlas_boundary_mltt_rejects_temporal_operator :
    supports MLTT temporal_identity = false;
  atlas_boundary_mltt_rejects_clock_quantification :
    supports MLTT (tClockPi (tUniverse 0)) = false;
  atlas_boundary_mltt_rejects_delayed_substitution :
    supports MLTT (tDelayedSubst (tTimeVar 0) (tUniverse 0)) = false;
  atlas_boundary_utt_accepts_prop :
    supports UTT tProp = true;
  atlas_boundary_utt_rejects_time :
    supports UTT (tTimeVar 0) = false;
  atlas_boundary_utt_rejects_temporal_operator :
    supports UTT temporal_identity = false;
  atlas_boundary_utt_rejects_guarded_fix :
    supports UTT (tFix tProp) = false;
  atlas_boundary_utt_rejects_clock_quantification :
    supports UTT (tClockPi tProp) = false;
  atlas_boundary_utt_rejects_delayed_substitution :
    supports UTT (tDelayedSubst (tTimeVar 0) tProp) = false;
  atlas_boundary_tdtt_accepts_time :
    supports TDTT (tTimeVar 0) = true;
  atlas_boundary_tdtt_accepts_temporal_operator :
    supports TDTT temporal_identity = true;
  atlas_boundary_tdtt_accepts_guarded_fix :
    supports TDTT (tFix tProp) = true;
  atlas_boundary_tdtt_accepts_clock_quantification :
    supports TDTT (tClockPi tProp) = true;
  atlas_boundary_tdtt_accepts_delayed_substitution :
    supports TDTT (tDelayedSubst (tTimeVar 0) tProp) = true;
  atlas_boundary_tdtt_accepts_clock_beta_redex :
    supports TDTT
      (tClockApp (tClockLam tProp) (tTimeVar 0)) = true
}.

Theorem atlas_system_boundary_regularities_hold :
  atlas_system_boundary_regularities.
Proof.
  constructor.
  - intros t Hsupport.
    apply mltt_supports_utt.
    exact Hsupport.
  - intros t Hsupport.
    apply utt_supports_tdtt.
    exact Hsupport.
  - intros t Hsupport.
    apply mltt_supports_tdtt.
    exact Hsupport.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Record atlas_system_comparison_matrix : Prop := {
  atlas_comparison_feature_boundaries :
    atlas_feature_boundary_summary;
  atlas_comparison_system_boundaries :
    atlas_system_boundary_regularities;
  atlas_comparison_mltt_prop :
    supports MLTT tProp = false;
  atlas_comparison_utt_prop :
    supports UTT tProp = true;
  atlas_comparison_tdtt_prop :
    supports TDTT tProp = true;
  atlas_comparison_mltt_time :
    supports MLTT (tTimeVar 0) = false;
  atlas_comparison_utt_time :
    supports UTT (tTimeVar 0) = false;
  atlas_comparison_tdtt_time :
    supports TDTT (tTimeVar 0) = true;
  atlas_comparison_mltt_temporal_operator :
    supports MLTT temporal_identity = false;
  atlas_comparison_utt_temporal_operator :
    supports UTT temporal_identity = false;
  atlas_comparison_tdtt_temporal_operator :
    supports TDTT temporal_identity = true;
  atlas_comparison_mltt_guarded_fix :
    supports MLTT (tFix tProp) = false;
  atlas_comparison_utt_guarded_fix :
    supports UTT (tFix tProp) = false;
  atlas_comparison_tdtt_guarded_fix :
    supports TDTT (tFix tProp) = true;
  atlas_comparison_mltt_clock_quantification :
    supports MLTT (tClockPi tProp) = false;
  atlas_comparison_utt_clock_quantification :
    supports UTT (tClockPi tProp) = false;
  atlas_comparison_tdtt_clock_quantification :
    supports TDTT (tClockPi tProp) = true;
  atlas_comparison_mltt_delayed_substitution :
    supports MLTT (tDelayedSubst (tTimeVar 0) tProp) = false;
  atlas_comparison_utt_delayed_substitution :
    supports UTT (tDelayedSubst (tTimeVar 0) tProp) = false;
  atlas_comparison_tdtt_delayed_substitution :
    supports TDTT (tDelayedSubst (tTimeVar 0) tProp) = true;
  atlas_comparison_tdtt_clock_beta_redex :
    supports TDTT
      (tClockApp (tClockLam tProp) (tTimeVar 0)) = true
}.

Theorem atlas_system_comparison_matrix_holds :
  atlas_system_comparison_matrix.
Proof.
  constructor.
  - apply atlas_feature_boundary_summary_holds.
  - apply atlas_system_boundary_regularities_hold.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem atlas_comparison_matrix_gives_proposition_profile :
  atlas_system_comparison_matrix ->
  supports MLTT tProp = false /\
  supports UTT tProp = true /\
  supports TDTT tProp = true.
Proof.
  intros Hmatrix.
  split.
  - exact (atlas_comparison_mltt_prop Hmatrix).
  - split.
    + exact (atlas_comparison_utt_prop Hmatrix).
    + exact (atlas_comparison_tdtt_prop Hmatrix).
Qed.

Theorem atlas_comparison_matrix_gives_temporal_profile :
  atlas_system_comparison_matrix ->
  (supports MLTT (tTimeVar 0) = false /\
   supports UTT (tTimeVar 0) = false /\
   supports TDTT (tTimeVar 0) = true) /\
  (supports MLTT temporal_identity = false /\
   supports UTT temporal_identity = false /\
   supports TDTT temporal_identity = true).
Proof.
  intros Hmatrix.
  split.
  - split.
    + exact (atlas_comparison_mltt_time Hmatrix).
    + split.
      * exact (atlas_comparison_utt_time Hmatrix).
      * exact (atlas_comparison_tdtt_time Hmatrix).
  - split.
    + exact (atlas_comparison_mltt_temporal_operator Hmatrix).
    + split.
      * exact (atlas_comparison_utt_temporal_operator Hmatrix).
      * exact (atlas_comparison_tdtt_temporal_operator Hmatrix).
Qed.

Theorem atlas_comparison_matrix_gives_guarded_fix_profile :
  atlas_system_comparison_matrix ->
  supports MLTT (tFix tProp) = false /\
  supports UTT (tFix tProp) = false /\
  supports TDTT (tFix tProp) = true.
Proof.
  intros Hmatrix.
  split.
  - exact (atlas_comparison_mltt_guarded_fix Hmatrix).
  - split.
    + exact (atlas_comparison_utt_guarded_fix Hmatrix).
    + exact (atlas_comparison_tdtt_guarded_fix Hmatrix).
Qed.

Theorem atlas_comparison_matrix_gives_clock_profile :
  atlas_system_comparison_matrix ->
  supports MLTT (tClockPi tProp) = false /\
  supports UTT (tClockPi tProp) = false /\
  supports TDTT (tClockPi tProp) = true /\
  supports TDTT
    (tClockApp (tClockLam tProp) (tTimeVar 0)) = true.
Proof.
  intros Hmatrix.
  split.
  - exact (atlas_comparison_mltt_clock_quantification Hmatrix).
  - split.
    + exact (atlas_comparison_utt_clock_quantification Hmatrix).
    + split.
      * exact (atlas_comparison_tdtt_clock_quantification Hmatrix).
      * exact (atlas_comparison_tdtt_clock_beta_redex Hmatrix).
Qed.

Theorem atlas_comparison_matrix_gives_delayed_substitution_profile :
  atlas_system_comparison_matrix ->
  supports MLTT (tDelayedSubst (tTimeVar 0) tProp) = false /\
  supports UTT (tDelayedSubst (tTimeVar 0) tProp) = false /\
  supports TDTT (tDelayedSubst (tTimeVar 0) tProp) = true.
Proof.
  intros Hmatrix.
  split.
  - exact (atlas_comparison_mltt_delayed_substitution Hmatrix).
  - split.
    + exact (atlas_comparison_utt_delayed_substitution Hmatrix).
    + exact (atlas_comparison_tdtt_delayed_substitution Hmatrix).
Qed.

Record atlas_system_comparison_projection_summary : Prop := {
  atlas_projection_comparison_matrix :
    atlas_system_comparison_matrix;
  atlas_projection_proposition_profile :
    supports MLTT tProp = false /\
    supports UTT tProp = true /\
    supports TDTT tProp = true;
  atlas_projection_temporal_profile :
    (supports MLTT (tTimeVar 0) = false /\
     supports UTT (tTimeVar 0) = false /\
     supports TDTT (tTimeVar 0) = true) /\
    (supports MLTT temporal_identity = false /\
     supports UTT temporal_identity = false /\
     supports TDTT temporal_identity = true);
  atlas_projection_guarded_fix_profile :
    supports MLTT (tFix tProp) = false /\
    supports UTT (tFix tProp) = false /\
    supports TDTT (tFix tProp) = true;
  atlas_projection_clock_profile :
    supports MLTT (tClockPi tProp) = false /\
    supports UTT (tClockPi tProp) = false /\
    supports TDTT (tClockPi tProp) = true /\
    supports TDTT
      (tClockApp (tClockLam tProp) (tTimeVar 0)) = true;
  atlas_projection_delayed_substitution_profile :
    supports MLTT (tDelayedSubst (tTimeVar 0) tProp) = false /\
    supports UTT (tDelayedSubst (tTimeVar 0) tProp) = false /\
    supports TDTT (tDelayedSubst (tTimeVar 0) tProp) = true
}.

Theorem atlas_system_comparison_projection_summary_holds :
  atlas_system_comparison_projection_summary.
Proof.
  constructor.
  - apply atlas_system_comparison_matrix_holds.
  - apply atlas_comparison_matrix_gives_proposition_profile.
    apply atlas_system_comparison_matrix_holds.
  - apply atlas_comparison_matrix_gives_temporal_profile.
    apply atlas_system_comparison_matrix_holds.
  - apply atlas_comparison_matrix_gives_guarded_fix_profile.
    apply atlas_system_comparison_matrix_holds.
  - apply atlas_comparison_matrix_gives_clock_profile.
    apply atlas_system_comparison_matrix_holds.
  - apply atlas_comparison_matrix_gives_delayed_substitution_profile.
    apply atlas_system_comparison_matrix_holds.
Qed.

Record atlas_comparison_translation_linkage_summary : Prop := {
  atlas_linkage_feature_boundaries :
    atlas_feature_boundary_summary;
  atlas_linkage_system_boundaries :
    atlas_system_boundary_regularities;
  atlas_linkage_comparison_matrix :
    atlas_system_comparison_matrix;
  atlas_linkage_comparison_projections :
    atlas_system_comparison_projection_summary;
  atlas_linkage_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_linkage_mltt_to_utt_support :
    forall t,
      supports MLTT t = true ->
      supports UTT (mltt_to_utt t) = true;
  atlas_linkage_utt_to_tdtt_support :
    forall t,
      supports UTT t = true ->
      supports TDTT (utt_to_tdtt t) = true;
  atlas_linkage_mltt_to_tdtt_support :
    forall t,
      supports MLTT t = true ->
      supports TDTT (mltt_to_tdtt t) = true;
  atlas_linkage_mltt_to_utt_context_support :
    forall gamma,
      context_supports MLTT gamma ->
      context_supports UTT (mltt_context_to_utt gamma);
  atlas_linkage_utt_to_tdtt_context_support :
    forall gamma,
      context_supports UTT gamma ->
      context_supports TDTT (utt_context_to_tdtt gamma);
  atlas_linkage_mltt_to_tdtt_context_support :
    forall gamma,
      context_supports MLTT gamma ->
      context_supports TDTT (mltt_context_to_tdtt gamma);
  atlas_linkage_mltt_to_utt_typing :
    forall gamma t a,
      has_type gamma t a ->
      mltt_to_utt_translation_regular gamma t a;
  atlas_linkage_utt_to_tdtt_typing :
    forall theta gamma t a,
      utt_has_type gamma t a ->
      utt_to_tdtt_translation_regular theta gamma t a;
  atlas_linkage_mltt_to_tdtt_typing :
    forall theta gamma t a,
      has_type gamma t a ->
      mltt_to_tdtt_translation_regular theta gamma t a
}.

Theorem atlas_comparison_translation_linkage_summary_holds :
  atlas_comparison_translation_linkage_summary.
Proof.
  constructor.
  - apply atlas_feature_boundary_summary_holds.
  - apply atlas_system_boundary_regularities_hold.
  - apply atlas_system_comparison_matrix_holds.
  - apply atlas_system_comparison_projection_summary_holds.
  - apply atlas_translation_reliability_summary_holds.
  - intros t Hsupport.
    apply mltt_supports_utt.
    exact Hsupport.
  - intros t Hsupport.
    apply utt_supports_tdtt.
    exact Hsupport.
  - intros t Hsupport.
    apply mltt_supports_tdtt.
    exact Hsupport.
  - intros gamma Hsupport.
    apply mltt_context_supports_utt_translation.
    exact Hsupport.
  - intros gamma Hsupport.
    apply utt_context_supports_tdtt_translation.
    exact Hsupport.
  - intros gamma Hsupport.
    apply mltt_context_supports_tdtt_translation.
    exact Hsupport.
  - intros gamma t a Htyping.
    apply mltt_translation_to_utt_regular.
    exact Htyping.
  - intros theta gamma t a Htyping.
    apply utt_translation_to_tdtt_regular.
    exact Htyping.
  - intros theta gamma t a Htyping.
    apply mltt_translation_to_tdtt_regular.
    exact Htyping.
Qed.

Record atlas_system_embedding_regularities : Prop := {
  atlas_embedding_mltt_to_utt_context :
    forall gamma,
      wf_context gamma ->
      utt_wf_context (mltt_context_to_utt gamma);
  atlas_embedding_mltt_to_utt_typing :
    forall gamma t a,
      has_type gamma t a ->
      utt_has_type
        (mltt_context_to_utt gamma)
        (mltt_to_utt t)
        (mltt_to_utt a);
  atlas_embedding_mltt_to_utt_defeq :
    forall t u,
      defeq t u ->
      defeq (mltt_to_utt t) (mltt_to_utt u);
  atlas_embedding_mltt_to_utt_defeq_regular :
    forall t u,
      defeq t u ->
      supports MLTT t = true ->
      supports MLTT u = true ->
      mltt_to_utt_defeq_regular t u;
  atlas_embedding_utt_to_tdtt_context :
    forall theta gamma,
      utt_wf_context gamma ->
      tdtt_wf_context theta (utt_context_to_tdtt gamma);
  atlas_embedding_utt_to_tdtt_typing :
    forall theta gamma t a,
      utt_has_type gamma t a ->
      tdtt_has_type theta
        (utt_context_to_tdtt gamma)
        (utt_to_tdtt t)
        (utt_to_tdtt a);
  atlas_embedding_utt_to_tdtt_defeq :
    forall t u,
      defeq t u ->
      defeq (utt_to_tdtt t) (utt_to_tdtt u);
  atlas_embedding_utt_to_tdtt_defeq_regular :
    forall t u,
      defeq t u ->
      supports UTT t = true ->
      supports UTT u = true ->
      utt_to_tdtt_defeq_regular t u;
  atlas_embedding_mltt_to_tdtt_context :
    forall theta gamma,
      wf_context gamma ->
      tdtt_wf_context theta (mltt_context_to_tdtt gamma);
  atlas_embedding_mltt_to_tdtt_typing :
    forall theta gamma t a,
      has_type gamma t a ->
      tdtt_has_type theta
        (mltt_context_to_tdtt gamma)
        (mltt_to_tdtt t)
        (mltt_to_tdtt a);
  atlas_embedding_mltt_to_tdtt_defeq :
    forall t u,
      defeq t u ->
      defeq (mltt_to_tdtt t) (mltt_to_tdtt u);
  atlas_embedding_mltt_to_tdtt_defeq_regular :
    forall t u,
      defeq t u ->
      supports MLTT t = true ->
      supports MLTT u = true ->
      mltt_to_tdtt_defeq_regular t u
}.

Theorem atlas_system_embedding_regularities_hold :
  atlas_system_embedding_regularities.
Proof.
  constructor.
  - intros gamma Hcontext.
    apply mltt_translation_to_utt_preserves_context.
    exact Hcontext.
  - intros gamma t a Htyping.
    apply mltt_translation_to_utt_preserves_typing.
    exact Htyping.
  - intros t u Heq.
    apply mltt_translation_to_utt_preserves_defeq.
    exact Heq.
  - intros t u Heq Ht Hu.
    apply mltt_translation_to_utt_defeq_regular.
    + exact Heq.
    + exact Ht.
    + exact Hu.
  - intros theta gamma Hcontext.
    apply utt_translation_to_tdtt_preserves_context.
    exact Hcontext.
  - intros theta gamma t a Htyping.
    apply utt_translation_to_tdtt_preserves_typing.
    exact Htyping.
  - intros t u Heq.
    apply utt_translation_to_tdtt_preserves_defeq.
    exact Heq.
  - intros t u Heq Ht Hu.
    apply utt_translation_to_tdtt_defeq_regular.
    + exact Heq.
    + exact Ht.
    + exact Hu.
  - intros theta gamma Hcontext.
    apply mltt_translation_to_tdtt_preserves_context.
    exact Hcontext.
  - intros theta gamma t a Htyping.
    apply mltt_translation_to_tdtt_preserves_typing.
    exact Htyping.
  - intros t u Heq.
    apply mltt_translation_to_tdtt_preserves_defeq.
    exact Heq.
  - intros t u Heq Ht Hu.
    apply mltt_translation_to_tdtt_defeq_regular.
    + exact Heq.
    + exact Ht.
    + exact Hu.
Qed.

Record atlas_final_summary : Prop := {
  atlas_final_coverage :
    type_theory_atlas_coverage;
  atlas_final_system_boundaries :
    atlas_system_boundary_regularities;
  atlas_final_feature_boundaries :
    atlas_feature_boundary_summary;
  atlas_final_system_comparison :
    atlas_system_comparison_matrix;
  atlas_final_system_comparison_projections :
    atlas_system_comparison_projection_summary;
  atlas_final_comparison_translation_linkage :
    atlas_comparison_translation_linkage_summary;
  atlas_final_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_final_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_final_metatheory :
    type_theory_atlas_metatheory_regularities;
  atlas_final_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard
}.

Theorem atlas_final_summary_holds :
  atlas_final_summary.
Proof.
  constructor.
  - apply type_theory_atlas_coverage_holds.
  - apply atlas_system_boundary_regularities_hold.
  - apply atlas_feature_boundary_summary_holds.
  - apply atlas_system_comparison_matrix_holds.
  - apply atlas_system_comparison_projection_summary_holds.
  - apply atlas_comparison_translation_linkage_summary_holds.
  - apply atlas_translation_reliability_summary_holds.
  - apply atlas_system_embedding_regularities_hold.
  - apply type_theory_atlas_metatheory_regularities_hold.
  - apply atlas_tdtt_regularity_dashboard_holds.
Qed.

Record atlas_layered_metatheory_summary : Prop := {
  atlas_layered_core_coverage :
    type_theory_atlas_coverage;
  atlas_layered_system_boundaries :
    atlas_system_boundary_regularities;
  atlas_layered_feature_boundaries :
    atlas_feature_boundary_summary;
  atlas_layered_comparison_matrix :
    atlas_system_comparison_matrix;
  atlas_layered_comparison_projections :
    atlas_system_comparison_projection_summary;
  atlas_layered_comparison_translation_linkage :
    atlas_comparison_translation_linkage_summary;
  atlas_layered_translation_layer :
    atlas_translation_reliability_summary;
  atlas_layered_embedding_layer :
    atlas_system_embedding_regularities;
  atlas_layered_tdtt_layer :
    atlas_tdtt_regularity_dashboard;
  atlas_layered_final_layer :
    atlas_final_summary
}.

Theorem atlas_layered_metatheory_summary_holds :
  atlas_layered_metatheory_summary.
Proof.
  constructor.
  - apply type_theory_atlas_coverage_holds.
  - apply atlas_system_boundary_regularities_hold.
  - apply atlas_feature_boundary_summary_holds.
  - apply atlas_system_comparison_matrix_holds.
  - apply atlas_system_comparison_projection_summary_holds.
  - apply atlas_comparison_translation_linkage_summary_holds.
  - apply atlas_translation_reliability_summary_holds.
  - apply atlas_system_embedding_regularities_hold.
  - apply atlas_tdtt_regularity_dashboard_holds.
  - apply atlas_final_summary_holds.
Qed.

Theorem atlas_layered_summary_gives_core_coverage :
  atlas_layered_metatheory_summary ->
  type_theory_atlas_coverage.
Proof.
  intros Hsummary.
  exact (atlas_layered_core_coverage Hsummary).
Qed.

Theorem atlas_layered_summary_gives_system_comparison :
  atlas_layered_metatheory_summary ->
  atlas_system_comparison_matrix.
Proof.
  intros Hsummary.
  exact (atlas_layered_comparison_matrix Hsummary).
Qed.

Theorem atlas_layered_summary_gives_comparison_projections :
  atlas_layered_metatheory_summary ->
  atlas_system_comparison_projection_summary.
Proof.
  intros Hsummary.
  exact (atlas_layered_comparison_projections Hsummary).
Qed.

Theorem atlas_layered_summary_gives_comparison_translation_linkage :
  atlas_layered_metatheory_summary ->
  atlas_comparison_translation_linkage_summary.
Proof.
  intros Hsummary.
  exact (atlas_layered_comparison_translation_linkage Hsummary).
Qed.

Theorem atlas_layered_summary_gives_translation_reliability :
  atlas_layered_metatheory_summary ->
  atlas_translation_reliability_summary.
Proof.
  intros Hsummary.
  exact (atlas_layered_translation_layer Hsummary).
Qed.

Theorem atlas_layered_summary_gives_tdtt_dashboard :
  atlas_layered_metatheory_summary ->
  atlas_tdtt_regularity_dashboard.
Proof.
  intros Hsummary.
  exact (atlas_layered_tdtt_layer Hsummary).
Qed.

Theorem atlas_layered_summary_gives_final_summary :
  atlas_layered_metatheory_summary ->
  atlas_final_summary.
Proof.
  intros Hsummary.
  exact (atlas_layered_final_layer Hsummary).
Qed.

Record type_theory_atlas_main_theorem : Prop := {
  atlas_main_coverage :
    type_theory_atlas_coverage;
  atlas_main_system_boundaries :
    atlas_system_boundary_regularities;
  atlas_main_feature_boundary_summary :
    atlas_feature_boundary_summary;
  atlas_main_system_comparison_matrix :
    atlas_system_comparison_matrix;
  atlas_main_system_comparison_projections :
    atlas_system_comparison_projection_summary;
  atlas_main_comparison_translation_linkage :
    atlas_comparison_translation_linkage_summary;
  atlas_main_translation_reliability_summary :
    atlas_translation_reliability_summary;
  atlas_main_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_main_metatheory :
    type_theory_atlas_metatheory_regularities;
  atlas_main_tdtt_constructor_summary :
    atlas_tdtt_constructor_regularities_summary;
  atlas_main_tdtt_regularity_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_main_typed_computation :
    tdtt_typed_computation_regularities;
  atlas_main_delayed_substitution :
    tdtt_delayed_substitution_regularities;
  atlas_main_delayed_translation_summary :
    atlas_delayed_substitution_translation_summary;
  atlas_main_final_summary :
    atlas_final_summary;
  atlas_main_layered_summary :
    atlas_layered_metatheory_summary
}.

Theorem type_theory_atlas_main_theorem_holds :
  type_theory_atlas_main_theorem.
Proof.
  constructor.
  - apply type_theory_atlas_coverage_holds.
  - apply atlas_system_boundary_regularities_hold.
  - apply atlas_feature_boundary_summary_holds.
  - apply atlas_system_comparison_matrix_holds.
  - apply atlas_system_comparison_projection_summary_holds.
  - apply atlas_comparison_translation_linkage_summary_holds.
  - apply atlas_translation_reliability_summary_holds.
  - apply atlas_system_embedding_regularities_hold.
  - apply type_theory_atlas_metatheory_regularities_hold.
  - apply atlas_tdtt_constructor_regularities_summary_holds.
  - apply atlas_tdtt_regularity_dashboard_holds.
  - apply tdtt_typed_computation_regularities_hold.
  - apply tdtt_delayed_substitution_regularities_hold.
  - apply atlas_delayed_substitution_translation_summary_holds.
  - apply atlas_final_summary_holds.
  - apply atlas_layered_metatheory_summary_holds.
Qed.

Corollary type_theory_atlas_main_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_main_translation_reliability_summary
    type_theory_atlas_main_theorem_holds).
Qed.

Corollary type_theory_atlas_main_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_main_system_comparison_matrix
    type_theory_atlas_main_theorem_holds).
Qed.

Corollary type_theory_atlas_main_gives_comparison_projections :
  atlas_system_comparison_projection_summary.
Proof.
  exact (atlas_main_system_comparison_projections
    type_theory_atlas_main_theorem_holds).
Qed.

Corollary type_theory_atlas_main_gives_comparison_translation_linkage :
  atlas_comparison_translation_linkage_summary.
Proof.
  exact (atlas_main_comparison_translation_linkage
    type_theory_atlas_main_theorem_holds).
Qed.

Corollary type_theory_atlas_main_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_main_tdtt_regularity_dashboard
    type_theory_atlas_main_theorem_holds).
Qed.

Corollary type_theory_atlas_main_gives_final_summary :
  atlas_final_summary.
Proof.
  exact (atlas_main_final_summary
    type_theory_atlas_main_theorem_holds).
Qed.

Corollary type_theory_atlas_main_gives_layered_summary :
  atlas_layered_metatheory_summary.
Proof.
  exact (atlas_main_layered_summary
    type_theory_atlas_main_theorem_holds).
Qed.

Record atlas_paper_contribution_summary : Prop := {
  atlas_paper_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_paper_system_comparison_matrix :
    atlas_system_comparison_matrix;
  atlas_paper_system_comparison_projections :
    atlas_system_comparison_projection_summary;
  atlas_paper_comparison_translation_linkage :
    atlas_comparison_translation_linkage_summary;
  atlas_paper_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_paper_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_paper_final_summary :
    atlas_final_summary;
  atlas_paper_layered_summary :
    atlas_layered_metatheory_summary;
  atlas_paper_core_coverage :
    type_theory_atlas_coverage;
  atlas_paper_layered_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_paper_layered_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_paper_layered_final_summary :
    atlas_final_summary
}.

Theorem atlas_paper_contribution_summary_holds :
  atlas_paper_contribution_summary.
Proof.
  constructor.
  - apply type_theory_atlas_main_theorem_holds.
  - apply atlas_system_comparison_matrix_holds.
  - apply atlas_system_comparison_projection_summary_holds.
  - apply atlas_comparison_translation_linkage_summary_holds.
  - apply type_theory_atlas_main_gives_translation_reliability.
  - apply type_theory_atlas_main_gives_tdtt_dashboard.
  - apply type_theory_atlas_main_gives_final_summary.
  - apply type_theory_atlas_main_gives_layered_summary.
  - apply atlas_layered_summary_gives_core_coverage.
    apply type_theory_atlas_main_gives_layered_summary.
  - apply atlas_layered_summary_gives_translation_reliability.
    apply type_theory_atlas_main_gives_layered_summary.
  - apply atlas_layered_summary_gives_tdtt_dashboard.
    apply type_theory_atlas_main_gives_layered_summary.
  - apply atlas_layered_summary_gives_final_summary.
    apply type_theory_atlas_main_gives_layered_summary.
Qed.

Record type_theory_atlas_final_paper_theorem : Prop := {
  atlas_final_paper_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_final_paper_coverage :
    type_theory_atlas_coverage;
  atlas_final_paper_system_comparison :
    atlas_system_comparison_matrix;
  atlas_final_paper_comparison_projections :
    atlas_system_comparison_projection_summary;
  atlas_final_paper_comparison_translation_linkage :
    atlas_comparison_translation_linkage_summary;
  atlas_final_paper_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_final_paper_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_final_paper_final_summary :
    atlas_final_summary;
  atlas_final_paper_layered_summary :
    atlas_layered_metatheory_summary;
  atlas_final_paper_contribution_summary :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_final_paper_theorem_holds :
  type_theory_atlas_final_paper_theorem.
Proof.
  constructor.
  - apply type_theory_atlas_main_theorem_holds.
  - apply type_theory_atlas_coverage_holds.
  - apply type_theory_atlas_main_gives_system_comparison.
  - apply type_theory_atlas_main_gives_comparison_projections.
  - apply type_theory_atlas_main_gives_comparison_translation_linkage.
  - apply type_theory_atlas_main_gives_translation_reliability.
  - apply type_theory_atlas_main_gives_tdtt_dashboard.
  - apply type_theory_atlas_main_gives_final_summary.
  - apply type_theory_atlas_main_gives_layered_summary.
  - apply atlas_paper_contribution_summary_holds.
Qed.

Corollary type_theory_atlas_final_paper_gives_coverage :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_final_paper_coverage
    type_theory_atlas_final_paper_theorem_holds).
Qed.

Corollary type_theory_atlas_final_paper_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_final_paper_system_comparison
    type_theory_atlas_final_paper_theorem_holds).
Qed.

Corollary type_theory_atlas_final_paper_gives_comparison_projections :
  atlas_system_comparison_projection_summary.
Proof.
  exact (atlas_final_paper_comparison_projections
    type_theory_atlas_final_paper_theorem_holds).
Qed.

Corollary type_theory_atlas_final_paper_gives_comparison_translation_linkage :
  atlas_comparison_translation_linkage_summary.
Proof.
  exact (atlas_final_paper_comparison_translation_linkage
    type_theory_atlas_final_paper_theorem_holds).
Qed.

Corollary type_theory_atlas_final_paper_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_final_paper_translation_reliability
    type_theory_atlas_final_paper_theorem_holds).
Qed.

Corollary type_theory_atlas_final_paper_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_final_paper_tdtt_dashboard
    type_theory_atlas_final_paper_theorem_holds).
Qed.

Corollary type_theory_atlas_final_paper_gives_contribution_summary :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_final_paper_contribution_summary
    type_theory_atlas_final_paper_theorem_holds).
Qed.

Record type_theory_atlas_completion_index : Prop := {
  atlas_completion_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_completion_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_completion_paper_contribution :
    atlas_paper_contribution_summary;
  atlas_completion_coverage_projection :
    type_theory_atlas_coverage;
  atlas_completion_system_comparison_projection :
    atlas_system_comparison_matrix;
  atlas_completion_comparison_projection_summary :
    atlas_system_comparison_projection_summary;
  atlas_completion_comparison_translation_linkage :
    atlas_comparison_translation_linkage_summary;
  atlas_completion_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_completion_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_completion_layered_summary :
    atlas_layered_metatheory_summary;
  atlas_completion_final_summary :
    atlas_final_summary
}.

Theorem type_theory_atlas_completion_index_holds :
  type_theory_atlas_completion_index.
Proof.
  constructor.
  - apply type_theory_atlas_main_theorem_holds.
  - apply type_theory_atlas_final_paper_theorem_holds.
  - apply type_theory_atlas_final_paper_gives_contribution_summary.
  - apply type_theory_atlas_final_paper_gives_coverage.
  - apply type_theory_atlas_final_paper_gives_system_comparison.
  - apply type_theory_atlas_final_paper_gives_comparison_projections.
  - apply type_theory_atlas_final_paper_gives_comparison_translation_linkage.
  - apply type_theory_atlas_final_paper_gives_translation_reliability.
  - apply type_theory_atlas_final_paper_gives_tdtt_dashboard.
  - apply type_theory_atlas_main_gives_layered_summary.
  - apply type_theory_atlas_main_gives_final_summary.
Qed.

Corollary type_theory_atlas_completion_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_completion_main_theorem
    type_theory_atlas_completion_index_holds).
Qed.

Corollary type_theory_atlas_completion_gives_final_paper_theorem :
  type_theory_atlas_final_paper_theorem.
Proof.
  exact (atlas_completion_final_paper_theorem
    type_theory_atlas_completion_index_holds).
Qed.

Corollary type_theory_atlas_completion_gives_paper_contribution :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_completion_paper_contribution
    type_theory_atlas_completion_index_holds).
Qed.

Corollary type_theory_atlas_completion_gives_coverage :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_completion_coverage_projection
    type_theory_atlas_completion_index_holds).
Qed.

Corollary type_theory_atlas_completion_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_completion_system_comparison_projection
    type_theory_atlas_completion_index_holds).
Qed.

Corollary type_theory_atlas_completion_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_completion_translation_reliability
    type_theory_atlas_completion_index_holds).
Qed.

Corollary type_theory_atlas_completion_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_completion_tdtt_dashboard
    type_theory_atlas_completion_index_holds).
Qed.

Corollary type_theory_atlas_completion_gives_layered_summary :
  atlas_layered_metatheory_summary.
Proof.
  exact (atlas_completion_layered_summary
    type_theory_atlas_completion_index_holds).
Qed.

Corollary type_theory_atlas_completion_gives_final_summary :
  atlas_final_summary.
Proof.
  exact (atlas_completion_final_summary
    type_theory_atlas_completion_index_holds).
Qed.

Record type_theory_atlas_paper_statement : Prop := {
  atlas_statement_completion_index :
    type_theory_atlas_completion_index;
  atlas_statement_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_statement_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_statement_unified_coverage :
    type_theory_atlas_coverage;
  atlas_statement_system_comparison :
    atlas_system_comparison_matrix;
  atlas_statement_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_statement_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_statement_final_summary :
    atlas_final_summary;
  atlas_statement_paper_contribution :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_paper_statement_holds :
  type_theory_atlas_paper_statement.
Proof.
  constructor.
  - apply type_theory_atlas_completion_index_holds.
  - apply type_theory_atlas_completion_gives_main_theorem.
  - apply type_theory_atlas_completion_gives_final_paper_theorem.
  - apply type_theory_atlas_completion_gives_coverage.
  - apply type_theory_atlas_completion_gives_system_comparison.
  - apply type_theory_atlas_completion_gives_translation_reliability.
  - apply type_theory_atlas_completion_gives_tdtt_dashboard.
  - apply type_theory_atlas_completion_gives_final_summary.
  - apply type_theory_atlas_completion_gives_paper_contribution.
Qed.

Corollary type_theory_atlas_paper_statement_gives_completion_index :
  type_theory_atlas_completion_index.
Proof.
  exact (atlas_statement_completion_index
    type_theory_atlas_paper_statement_holds).
Qed.

Corollary type_theory_atlas_paper_statement_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_statement_main_theorem
    type_theory_atlas_paper_statement_holds).
Qed.

Corollary type_theory_atlas_paper_statement_gives_final_paper_theorem :
  type_theory_atlas_final_paper_theorem.
Proof.
  exact (atlas_statement_final_paper_theorem
    type_theory_atlas_paper_statement_holds).
Qed.

Corollary type_theory_atlas_paper_statement_gives_unified_coverage :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_statement_unified_coverage
    type_theory_atlas_paper_statement_holds).
Qed.

Corollary type_theory_atlas_paper_statement_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_statement_system_comparison
    type_theory_atlas_paper_statement_holds).
Qed.

Corollary type_theory_atlas_paper_statement_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_statement_translation_reliability
    type_theory_atlas_paper_statement_holds).
Qed.

Corollary type_theory_atlas_paper_statement_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_statement_tdtt_dashboard
    type_theory_atlas_paper_statement_holds).
Qed.

Corollary type_theory_atlas_paper_statement_gives_final_summary :
  atlas_final_summary.
Proof.
  exact (atlas_statement_final_summary
    type_theory_atlas_paper_statement_holds).
Qed.

Corollary type_theory_atlas_paper_statement_gives_contribution_summary :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_statement_paper_contribution
    type_theory_atlas_paper_statement_holds).
Qed.

Record type_theory_atlas_project_status_certificate : Prop := {
  atlas_status_paper_statement :
    type_theory_atlas_paper_statement;
  atlas_status_completion_index :
    type_theory_atlas_completion_index;
  atlas_status_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_status_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_status_unified_coverage :
    type_theory_atlas_coverage;
  atlas_status_system_comparison :
    atlas_system_comparison_matrix;
  atlas_status_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_status_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_status_final_summary :
    atlas_final_summary;
  atlas_status_paper_contribution :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_project_status_certificate_holds :
  type_theory_atlas_project_status_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_paper_statement_holds.
  - apply type_theory_atlas_paper_statement_gives_completion_index.
  - apply type_theory_atlas_paper_statement_gives_main_theorem.
  - apply type_theory_atlas_paper_statement_gives_final_paper_theorem.
  - apply type_theory_atlas_paper_statement_gives_unified_coverage.
  - apply type_theory_atlas_paper_statement_gives_system_comparison.
  - apply type_theory_atlas_paper_statement_gives_translation_reliability.
  - apply type_theory_atlas_paper_statement_gives_tdtt_dashboard.
  - apply type_theory_atlas_paper_statement_gives_final_summary.
  - apply type_theory_atlas_paper_statement_gives_contribution_summary.
Qed.

Corollary type_theory_atlas_status_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_status_paper_statement
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_completion_index :
  type_theory_atlas_completion_index.
Proof.
  exact (atlas_status_completion_index
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_status_main_theorem
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_final_paper_theorem :
  type_theory_atlas_final_paper_theorem.
Proof.
  exact (atlas_status_final_paper_theorem
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_unified_coverage :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_status_unified_coverage
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_status_system_comparison
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_status_translation_reliability
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_status_tdtt_dashboard
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_final_summary :
  atlas_final_summary.
Proof.
  exact (atlas_status_final_summary
    type_theory_atlas_project_status_certificate_holds).
Qed.

Corollary type_theory_atlas_status_gives_contribution_summary :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_status_paper_contribution
    type_theory_atlas_project_status_certificate_holds).
Qed.

Record type_theory_atlas_release_summary : Prop := {
  atlas_release_status_certificate :
    type_theory_atlas_project_status_certificate;
  atlas_release_paper_statement :
    type_theory_atlas_paper_statement;
  atlas_release_completion_index :
    type_theory_atlas_completion_index;
  atlas_release_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_release_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_release_coverage :
    type_theory_atlas_coverage;
  atlas_release_system_comparison :
    atlas_system_comparison_matrix;
  atlas_release_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_release_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_release_final_summary :
    atlas_final_summary;
  atlas_release_contribution_summary :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_release_summary_holds :
  type_theory_atlas_release_summary.
Proof.
  constructor.
  - apply type_theory_atlas_project_status_certificate_holds.
  - apply type_theory_atlas_status_gives_paper_statement.
  - apply type_theory_atlas_status_gives_completion_index.
  - apply type_theory_atlas_status_gives_main_theorem.
  - apply type_theory_atlas_status_gives_final_paper_theorem.
  - apply type_theory_atlas_status_gives_unified_coverage.
  - apply type_theory_atlas_status_gives_system_comparison.
  - apply type_theory_atlas_status_gives_translation_reliability.
  - apply type_theory_atlas_status_gives_tdtt_dashboard.
  - apply type_theory_atlas_status_gives_final_summary.
  - apply type_theory_atlas_status_gives_contribution_summary.
Qed.

Corollary type_theory_atlas_release_gives_status_certificate :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_release_status_certificate
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_release_paper_statement
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_completion_index :
  type_theory_atlas_completion_index.
Proof.
  exact (atlas_release_completion_index
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_release_main_theorem
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_final_paper_theorem :
  type_theory_atlas_final_paper_theorem.
Proof.
  exact (atlas_release_final_paper_theorem
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_coverage :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_release_coverage
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_release_system_comparison
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_release_translation_reliability
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_release_tdtt_dashboard
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_final_summary :
  atlas_final_summary.
Proof.
  exact (atlas_release_final_summary
    type_theory_atlas_release_summary_holds).
Qed.

Corollary type_theory_atlas_release_gives_contribution_summary :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_release_contribution_summary
    type_theory_atlas_release_summary_holds).
Qed.

Record type_theory_atlas_artifact_index : Prop := {
  atlas_artifact_release_summary :
    type_theory_atlas_release_summary;
  atlas_artifact_status_certificate :
    type_theory_atlas_project_status_certificate;
  atlas_artifact_paper_statement :
    type_theory_atlas_paper_statement;
  atlas_artifact_completion_index :
    type_theory_atlas_completion_index;
  atlas_artifact_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_artifact_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_artifact_coverage :
    type_theory_atlas_coverage;
  atlas_artifact_system_comparison :
    atlas_system_comparison_matrix;
  atlas_artifact_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_artifact_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_artifact_final_summary :
    atlas_final_summary;
  atlas_artifact_contribution_summary :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_artifact_index_holds :
  type_theory_atlas_artifact_index.
Proof.
  constructor.
  - apply type_theory_atlas_release_summary_holds.
  - apply type_theory_atlas_release_gives_status_certificate.
  - apply type_theory_atlas_release_gives_paper_statement.
  - apply type_theory_atlas_release_gives_completion_index.
  - apply type_theory_atlas_release_gives_main_theorem.
  - apply type_theory_atlas_release_gives_final_paper_theorem.
  - apply type_theory_atlas_release_gives_coverage.
  - apply type_theory_atlas_release_gives_system_comparison.
  - apply type_theory_atlas_release_gives_translation_reliability.
  - apply type_theory_atlas_release_gives_tdtt_dashboard.
  - apply type_theory_atlas_release_gives_final_summary.
  - apply type_theory_atlas_release_gives_contribution_summary.
Qed.

Corollary type_theory_atlas_artifact_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_artifact_release_summary
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_status_certificate :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_artifact_status_certificate
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_artifact_paper_statement
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_completion_index :
  type_theory_atlas_completion_index.
Proof.
  exact (atlas_artifact_completion_index
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_artifact_main_theorem
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_final_paper_theorem :
  type_theory_atlas_final_paper_theorem.
Proof.
  exact (atlas_artifact_final_paper_theorem
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_coverage :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_artifact_coverage
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_artifact_system_comparison
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_artifact_translation_reliability
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_artifact_tdtt_dashboard
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_final_summary :
  atlas_final_summary.
Proof.
  exact (atlas_artifact_final_summary
    type_theory_atlas_artifact_index_holds).
Qed.

Corollary type_theory_atlas_artifact_gives_contribution_summary :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_artifact_contribution_summary
    type_theory_atlas_artifact_index_holds).
Qed.

Record type_theory_atlas_phase_order_certificate : Prop := {
  atlas_phase_unified_syntax_framework :
    type_theory_atlas_coverage;
  atlas_phase_mltt_typing_support :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_phase_utt_typing_support :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_phase_tdtt_typing_support :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_phase_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_phase_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_phase_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_phase_metatheory :
    type_theory_atlas_main_theorem;
  atlas_phase_artifact_index :
    type_theory_atlas_artifact_index
}.

Theorem type_theory_atlas_phase_order_certificate_holds :
  type_theory_atlas_phase_order_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_artifact_gives_coverage.
  - exact (atlas_mltt_typing_support
      type_theory_atlas_metatheory_regularities_hold).
  - exact (atlas_utt_typing_support
      type_theory_atlas_metatheory_regularities_hold).
  - exact (atlas_tdtt_typing_support
      type_theory_atlas_metatheory_regularities_hold).
  - apply type_theory_atlas_artifact_gives_tdtt_dashboard.
  - apply type_theory_atlas_artifact_gives_translation_reliability.
  - apply atlas_system_embedding_regularities_hold.
  - apply type_theory_atlas_artifact_gives_main_theorem.
  - apply type_theory_atlas_artifact_index_holds.
Qed.

Corollary type_theory_atlas_phase_order_gives_unified_syntax_framework :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_phase_unified_syntax_framework
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Corollary type_theory_atlas_phase_order_gives_mltt_typing_support :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_phase_mltt_typing_support
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Corollary type_theory_atlas_phase_order_gives_utt_typing_support :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_phase_utt_typing_support
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Corollary type_theory_atlas_phase_order_gives_tdtt_typing_support :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_phase_tdtt_typing_support
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Corollary type_theory_atlas_phase_order_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_phase_artifact_index
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Corollary type_theory_atlas_phase_order_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_phase_translation_reliability
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Corollary type_theory_atlas_phase_order_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_phase_system_embeddings
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Corollary type_theory_atlas_phase_order_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_phase_tdtt_dashboard
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Corollary type_theory_atlas_phase_order_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_phase_metatheory
    type_theory_atlas_phase_order_certificate_holds).
Qed.

Record type_theory_atlas_paper_section_map : Prop := {
  atlas_section_introduction_contribution :
    atlas_paper_contribution_summary;
  atlas_section_unified_syntax_framework :
    type_theory_atlas_coverage;
  atlas_section_mltt_typing_support :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_section_utt_typing_support :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_section_tdtt_typing_support :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_section_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_section_translations :
    atlas_translation_reliability_summary;
  atlas_section_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_section_metatheory :
    type_theory_atlas_main_theorem;
  atlas_section_artifact_index :
    type_theory_atlas_artifact_index
}.

Theorem type_theory_atlas_paper_section_map_holds :
  type_theory_atlas_paper_section_map.
Proof.
  constructor.
  - apply type_theory_atlas_artifact_gives_contribution_summary.
  - apply type_theory_atlas_phase_order_gives_unified_syntax_framework.
  - apply type_theory_atlas_phase_order_gives_mltt_typing_support.
  - apply type_theory_atlas_phase_order_gives_utt_typing_support.
  - apply type_theory_atlas_phase_order_gives_tdtt_typing_support.
  - apply type_theory_atlas_phase_order_gives_tdtt_dashboard.
  - apply type_theory_atlas_phase_order_gives_translation_reliability.
  - apply type_theory_atlas_phase_order_gives_system_embeddings.
  - apply type_theory_atlas_phase_order_gives_main_theorem.
  - apply type_theory_atlas_phase_order_gives_artifact_index.
Qed.

Corollary type_theory_atlas_paper_section_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_section_unified_syntax_framework
    type_theory_atlas_paper_section_map_holds).
Qed.

Corollary type_theory_atlas_paper_section_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_section_mltt_typing_support
    type_theory_atlas_paper_section_map_holds).
Qed.

Corollary type_theory_atlas_paper_section_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_section_utt_typing_support
    type_theory_atlas_paper_section_map_holds).
Qed.

Corollary type_theory_atlas_paper_section_gives_tdtt :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_section_tdtt_dashboard
    type_theory_atlas_paper_section_map_holds).
Qed.

Corollary type_theory_atlas_paper_section_gives_translations :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_section_translations
    type_theory_atlas_paper_section_map_holds).
Qed.

Corollary type_theory_atlas_paper_section_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_section_metatheory
    type_theory_atlas_paper_section_map_holds).
Qed.

Corollary type_theory_atlas_paper_section_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_section_artifact_index
    type_theory_atlas_paper_section_map_holds).
Qed.

Record type_theory_atlas_writing_checklist : Prop := {
  atlas_writing_section_map :
    type_theory_atlas_paper_section_map;
  atlas_writing_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_writing_release_summary :
    type_theory_atlas_release_summary;
  atlas_writing_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_writing_artifact_index :
    type_theory_atlas_artifact_index;
  atlas_writing_paper_statement :
    type_theory_atlas_paper_statement;
  atlas_writing_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_writing_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_writing_completion_index :
    type_theory_atlas_completion_index;
  atlas_writing_contribution_summary :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_writing_checklist_holds :
  type_theory_atlas_writing_checklist.
Proof.
  constructor.
  - apply type_theory_atlas_paper_section_map_holds.
  - apply type_theory_atlas_phase_order_certificate_holds.
  - apply type_theory_atlas_artifact_gives_release_summary.
  - apply type_theory_atlas_artifact_gives_status_certificate.
  - apply type_theory_atlas_phase_order_gives_artifact_index.
  - apply type_theory_atlas_artifact_gives_paper_statement.
  - apply type_theory_atlas_artifact_gives_main_theorem.
  - apply type_theory_atlas_artifact_gives_final_paper_theorem.
  - apply type_theory_atlas_artifact_gives_completion_index.
  - apply type_theory_atlas_artifact_gives_contribution_summary.
Qed.

Corollary type_theory_atlas_writing_checklist_gives_section_map :
  type_theory_atlas_paper_section_map.
Proof.
  exact (atlas_writing_section_map
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_writing_phase_order
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_writing_release_summary
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_writing_project_status
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_writing_artifact_index
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_writing_paper_statement
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_writing_main_theorem
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_final_paper_theorem :
  type_theory_atlas_final_paper_theorem.
Proof.
  exact (atlas_writing_final_paper_theorem
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_completion_index :
  type_theory_atlas_completion_index.
Proof.
  exact (atlas_writing_completion_index
    type_theory_atlas_writing_checklist_holds).
Qed.

Corollary type_theory_atlas_writing_checklist_gives_contribution_summary :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_writing_contribution_summary
    type_theory_atlas_writing_checklist_holds).
Qed.

Record type_theory_atlas_paper_claim_index : Prop := {
  atlas_claim_writing_checklist :
    type_theory_atlas_writing_checklist;
  atlas_claim_section_map :
    type_theory_atlas_paper_section_map;
  atlas_claim_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_claim_core_statement :
    type_theory_atlas_paper_statement;
  atlas_claim_unified_framework :
    type_theory_atlas_coverage;
  atlas_claim_system_comparison :
    atlas_system_comparison_matrix;
  atlas_claim_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_claim_tdtt_extension :
    atlas_tdtt_regularity_dashboard;
  atlas_claim_metatheory :
    type_theory_atlas_main_theorem;
  atlas_claim_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_claim_release_summary :
    type_theory_atlas_release_summary;
  atlas_claim_artifact_index :
    type_theory_atlas_artifact_index;
  atlas_claim_contribution_summary :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_paper_claim_index_holds :
  type_theory_atlas_paper_claim_index.
Proof.
  constructor.
  - apply type_theory_atlas_writing_checklist_holds.
  - apply type_theory_atlas_writing_checklist_gives_section_map.
  - apply type_theory_atlas_writing_checklist_gives_phase_order.
  - apply type_theory_atlas_writing_checklist_gives_paper_statement.
  - apply type_theory_atlas_paper_section_gives_unified_syntax.
  - apply type_theory_atlas_artifact_gives_system_comparison.
  - apply type_theory_atlas_phase_order_gives_translation_reliability.
  - apply type_theory_atlas_phase_order_gives_tdtt_dashboard.
  - apply type_theory_atlas_writing_checklist_gives_main_theorem.
  - apply type_theory_atlas_writing_checklist_gives_final_paper_theorem.
  - apply type_theory_atlas_writing_checklist_gives_release_summary.
  - apply type_theory_atlas_writing_checklist_gives_artifact_index.
  - apply type_theory_atlas_writing_checklist_gives_contribution_summary.
Qed.

Corollary type_theory_atlas_paper_claim_gives_writing_checklist :
  type_theory_atlas_writing_checklist.
Proof.
  exact (atlas_claim_writing_checklist
    type_theory_atlas_paper_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_claim_gives_core_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_claim_core_statement
    type_theory_atlas_paper_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_claim_gives_unified_framework :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_claim_unified_framework
    type_theory_atlas_paper_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_claim_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_claim_system_comparison
    type_theory_atlas_paper_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_claim_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_claim_translation_reliability
    type_theory_atlas_paper_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_claim_gives_tdtt_extension :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_claim_tdtt_extension
    type_theory_atlas_paper_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_claim_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_claim_metatheory
    type_theory_atlas_paper_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_claim_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_claim_artifact_index
    type_theory_atlas_paper_claim_index_holds).
Qed.

Record type_theory_atlas_final_delivery_index : Prop := {
  atlas_delivery_paper_claim_index :
    type_theory_atlas_paper_claim_index;
  atlas_delivery_writing_checklist :
    type_theory_atlas_writing_checklist;
  atlas_delivery_section_map :
    type_theory_atlas_paper_section_map;
  atlas_delivery_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_delivery_release_summary :
    type_theory_atlas_release_summary;
  atlas_delivery_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_delivery_artifact_index :
    type_theory_atlas_artifact_index;
  atlas_delivery_paper_statement :
    type_theory_atlas_paper_statement;
  atlas_delivery_completion_index :
    type_theory_atlas_completion_index;
  atlas_delivery_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_delivery_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_delivery_final_summary :
    atlas_final_summary;
  atlas_delivery_contribution_summary :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_final_delivery_index_holds :
  type_theory_atlas_final_delivery_index.
Proof.
  constructor.
  - apply type_theory_atlas_paper_claim_index_holds.
  - apply type_theory_atlas_paper_claim_gives_writing_checklist.
  - apply type_theory_atlas_writing_checklist_gives_section_map.
  - apply type_theory_atlas_writing_checklist_gives_phase_order.
  - apply type_theory_atlas_writing_checklist_gives_release_summary.
  - apply type_theory_atlas_writing_checklist_gives_project_status.
  - apply type_theory_atlas_paper_claim_gives_artifact_index.
  - apply type_theory_atlas_writing_checklist_gives_paper_statement.
  - apply type_theory_atlas_writing_checklist_gives_completion_index.
  - apply type_theory_atlas_paper_claim_gives_metatheory.
  - apply type_theory_atlas_writing_checklist_gives_final_paper_theorem.
  - apply type_theory_atlas_release_gives_final_summary.
  - apply type_theory_atlas_writing_checklist_gives_contribution_summary.
Qed.

Corollary type_theory_atlas_final_delivery_gives_paper_claim_index :
  type_theory_atlas_paper_claim_index.
Proof.
  exact (atlas_delivery_paper_claim_index
    type_theory_atlas_final_delivery_index_holds).
Qed.

Corollary type_theory_atlas_final_delivery_gives_writing_checklist :
  type_theory_atlas_writing_checklist.
Proof.
  exact (atlas_delivery_writing_checklist
    type_theory_atlas_final_delivery_index_holds).
Qed.

Corollary type_theory_atlas_final_delivery_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_delivery_release_summary
    type_theory_atlas_final_delivery_index_holds).
Qed.

Corollary type_theory_atlas_final_delivery_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_delivery_project_status
    type_theory_atlas_final_delivery_index_holds).
Qed.

Corollary type_theory_atlas_final_delivery_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_delivery_artifact_index
    type_theory_atlas_final_delivery_index_holds).
Qed.

Corollary type_theory_atlas_final_delivery_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_delivery_main_theorem
    type_theory_atlas_final_delivery_index_holds).
Qed.

Corollary type_theory_atlas_final_delivery_gives_final_paper_theorem :
  type_theory_atlas_final_paper_theorem.
Proof.
  exact (atlas_delivery_final_paper_theorem
    type_theory_atlas_final_delivery_index_holds).
Qed.

Corollary type_theory_atlas_final_delivery_gives_contribution_summary :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_delivery_contribution_summary
    type_theory_atlas_final_delivery_index_holds).
Qed.

Theorem type_theory_atlas_complete :
  type_theory_atlas_final_delivery_index.
Proof.
  apply type_theory_atlas_final_delivery_index_holds.
Qed.

Corollary type_theory_atlas_complete_gives_paper_claim_index :
  type_theory_atlas_paper_claim_index.
Proof.
  exact (atlas_delivery_paper_claim_index type_theory_atlas_complete).
Qed.

Corollary type_theory_atlas_complete_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_delivery_artifact_index type_theory_atlas_complete).
Qed.

Corollary type_theory_atlas_complete_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_delivery_main_theorem type_theory_atlas_complete).
Qed.

Record type_theory_atlas_automation_daily_report : Prop := {
  atlas_daily_complete_entry :
    type_theory_atlas_final_delivery_index;
  atlas_daily_paper_claim_index :
    type_theory_atlas_paper_claim_index;
  atlas_daily_artifact_index :
    type_theory_atlas_artifact_index;
  atlas_daily_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_daily_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_daily_writing_checklist :
    type_theory_atlas_writing_checklist;
  atlas_daily_release_summary :
    type_theory_atlas_release_summary;
  atlas_daily_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_daily_final_summary :
    atlas_final_summary;
  atlas_daily_contribution_summary :
    atlas_paper_contribution_summary
}.

Theorem type_theory_atlas_automation_daily_report_holds :
  type_theory_atlas_automation_daily_report.
Proof.
  constructor.
  - apply type_theory_atlas_complete.
  - apply type_theory_atlas_complete_gives_paper_claim_index.
  - apply type_theory_atlas_complete_gives_artifact_index.
  - apply type_theory_atlas_complete_gives_main_theorem.
  - exact (atlas_delivery_phase_order type_theory_atlas_complete).
  - exact (atlas_delivery_writing_checklist type_theory_atlas_complete).
  - exact (atlas_delivery_release_summary type_theory_atlas_complete).
  - exact (atlas_delivery_project_status type_theory_atlas_complete).
  - exact (atlas_delivery_final_summary type_theory_atlas_complete).
  - exact (atlas_delivery_contribution_summary type_theory_atlas_complete).
Qed.

Corollary type_theory_atlas_daily_report_gives_complete_entry :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_complete_entry
    type_theory_atlas_automation_daily_report_holds).
Qed.

Corollary type_theory_atlas_daily_report_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_daily_phase_order
    type_theory_atlas_automation_daily_report_holds).
Qed.

Corollary type_theory_atlas_daily_report_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_artifact_index
    type_theory_atlas_automation_daily_report_holds).
Qed.

Corollary type_theory_atlas_daily_report_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_main_theorem
    type_theory_atlas_automation_daily_report_holds).
Qed.

Corollary type_theory_atlas_daily_report_gives_unified_syntax_framework :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_phase_unified_syntax_framework
    type_theory_atlas_daily_report_gives_phase_order).
Qed.

Corollary type_theory_atlas_daily_report_gives_mltt_typing_support :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_phase_mltt_typing_support
    type_theory_atlas_daily_report_gives_phase_order).
Qed.

Corollary type_theory_atlas_daily_report_gives_utt_typing_support :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_phase_utt_typing_support
    type_theory_atlas_daily_report_gives_phase_order).
Qed.

Corollary type_theory_atlas_daily_report_gives_tdtt_typing_support :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_phase_tdtt_typing_support
    type_theory_atlas_daily_report_gives_phase_order).
Qed.

Corollary type_theory_atlas_daily_report_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_phase_tdtt_dashboard
    type_theory_atlas_daily_report_gives_phase_order).
Qed.

Corollary type_theory_atlas_daily_report_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_phase_system_embeddings
    type_theory_atlas_daily_report_gives_phase_order).
Qed.

Corollary type_theory_atlas_daily_report_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_phase_translation_reliability
    type_theory_atlas_daily_report_gives_phase_order).
Qed.

Corollary type_theory_atlas_daily_report_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact type_theory_atlas_daily_report_gives_main_theorem.
Qed.

Record type_theory_atlas_daily_completion_certificate : Prop := {
  atlas_daily_completion_report :
    type_theory_atlas_automation_daily_report;
  atlas_daily_completion_complete_entry :
    type_theory_atlas_final_delivery_index;
  atlas_daily_completion_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_completion_mltt_typing_support :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_completion_utt_typing_support :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_completion_tdtt_typing_support :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_completion_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_completion_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_completion_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_daily_completion_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_completion_release_summary :
    type_theory_atlas_release_summary;
  atlas_daily_completion_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_daily_completion_artifact_index :
    type_theory_atlas_artifact_index;
  atlas_daily_completion_final_summary :
    atlas_final_summary
}.

Theorem type_theory_atlas_daily_completion_certificate_holds :
  type_theory_atlas_daily_completion_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_automation_daily_report_holds.
  - apply type_theory_atlas_daily_report_gives_complete_entry.
  - apply type_theory_atlas_daily_report_gives_unified_syntax_framework.
  - apply type_theory_atlas_daily_report_gives_mltt_typing_support.
  - apply type_theory_atlas_daily_report_gives_utt_typing_support.
  - apply type_theory_atlas_daily_report_gives_tdtt_typing_support.
  - apply type_theory_atlas_daily_report_gives_tdtt_dashboard.
  - apply type_theory_atlas_daily_report_gives_system_embeddings.
  - apply type_theory_atlas_daily_report_gives_translation_reliability.
  - apply type_theory_atlas_daily_report_gives_metatheory.
  - exact (atlas_daily_release_summary
      type_theory_atlas_automation_daily_report_holds).
  - exact (atlas_daily_project_status
      type_theory_atlas_automation_daily_report_holds).
  - apply type_theory_atlas_daily_report_gives_artifact_index.
  - exact (atlas_daily_final_summary
      type_theory_atlas_automation_daily_report_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_report :
  type_theory_atlas_automation_daily_report.
Proof.
  exact (atlas_daily_completion_report
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_complete_entry :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_completion_complete_entry
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_completion_unified_syntax
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_completion_mltt_typing_support
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_completion_utt_typing_support
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_tdtt :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_completion_tdtt_dashboard
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_completion_translation_reliability
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_completion_metatheory
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_completion_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_completion_artifact_index
    type_theory_atlas_daily_completion_certificate_holds).
Qed.

Theorem type_theory_atlas_daily_complete :
  type_theory_atlas_daily_completion_certificate.
Proof.
  apply type_theory_atlas_daily_completion_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_complete_gives_report :
  type_theory_atlas_automation_daily_report.
Proof.
  exact (atlas_daily_completion_report type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_complete_entry :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_completion_complete_entry
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_completion_unified_syntax
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_completion_mltt_typing_support
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_completion_utt_typing_support
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_completion_tdtt_typing_support
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_tdtt :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_completion_tdtt_dashboard
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_completion_system_embeddings
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_completion_translation_reliability
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_completion_artifact_index
    type_theory_atlas_daily_complete).
Qed.

Corollary type_theory_atlas_daily_complete_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_completion_metatheory
    type_theory_atlas_daily_complete).
Qed.

Record type_theory_atlas_daily_stage_route_index : Prop := {
  atlas_daily_stage_route_complete :
    type_theory_atlas_daily_completion_certificate;
  atlas_daily_stage_route_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_stage_route_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_stage_route_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_stage_route_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_stage_route_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_stage_route_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_stage_route_translation :
    atlas_translation_reliability_summary;
  atlas_daily_stage_route_metatheory :
    type_theory_atlas_main_theorem
}.

Theorem type_theory_atlas_daily_stage_route_index_holds :
  type_theory_atlas_daily_stage_route_index.
Proof.
  constructor.
  - apply type_theory_atlas_daily_complete.
  - apply type_theory_atlas_daily_complete_gives_unified_syntax.
  - apply type_theory_atlas_daily_complete_gives_mltt.
  - apply type_theory_atlas_daily_complete_gives_utt.
  - apply type_theory_atlas_daily_complete_gives_tdtt_typing.
  - apply type_theory_atlas_daily_complete_gives_tdtt.
  - apply type_theory_atlas_daily_complete_gives_system_embeddings.
  - apply type_theory_atlas_daily_complete_gives_translation.
  - apply type_theory_atlas_daily_complete_gives_metatheory.
Qed.

Corollary type_theory_atlas_daily_complete_gives_stage_route_index :
  type_theory_atlas_daily_stage_route_index.
Proof.
  apply type_theory_atlas_daily_stage_route_index_holds.
Qed.

Theorem type_theory_atlas_daily_stage_route_index_from_phase_order :
  type_theory_atlas_daily_completion_certificate ->
  type_theory_atlas_phase_order_certificate ->
  type_theory_atlas_daily_stage_route_index.
Proof.
  intros Hdaily Hphase.
  constructor.
  - exact Hdaily.
  - exact (atlas_phase_unified_syntax_framework Hphase).
  - exact (atlas_phase_mltt_typing_support Hphase).
  - exact (atlas_phase_utt_typing_support Hphase).
  - exact (atlas_phase_tdtt_typing_support Hphase).
  - exact (atlas_phase_tdtt_dashboard Hphase).
  - exact (atlas_phase_system_embeddings Hphase).
  - exact (atlas_phase_translation_reliability Hphase).
  - exact (atlas_phase_metatheory Hphase).
Qed.

Record type_theory_atlas_daily_phase_route_consistency : Prop := {
  atlas_daily_phase_route_daily_complete :
    type_theory_atlas_daily_completion_certificate;
  atlas_daily_phase_route_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_daily_phase_route_daily_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_daily_phase_route_phase_built_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_daily_phase_route_artifact_index :
    type_theory_atlas_artifact_index
}.

Theorem type_theory_atlas_daily_phase_route_consistency_holds :
  type_theory_atlas_daily_phase_route_consistency.
Proof.
  constructor.
  - apply type_theory_atlas_daily_complete.
  - apply type_theory_atlas_phase_order_certificate_holds.
  - apply type_theory_atlas_daily_stage_route_index_holds.
  - apply type_theory_atlas_daily_stage_route_index_from_phase_order.
    + apply type_theory_atlas_daily_complete.
    + apply type_theory_atlas_phase_order_certificate_holds.
  - apply type_theory_atlas_phase_order_gives_artifact_index.
Qed.

Corollary type_theory_atlas_daily_complete_gives_phase_route_consistency :
  type_theory_atlas_daily_phase_route_consistency.
Proof.
  apply type_theory_atlas_daily_phase_route_consistency_holds.
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_stage_route_index :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_daily_phase_route_phase_built_index
    type_theory_atlas_daily_phase_route_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_daily_phase_route_phase_order
    type_theory_atlas_daily_phase_route_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_stage_route_unified_syntax
    type_theory_atlas_daily_phase_route_gives_stage_route_index).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_stage_route_mltt
    type_theory_atlas_daily_phase_route_gives_stage_route_index).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_stage_route_utt
    type_theory_atlas_daily_phase_route_gives_stage_route_index).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_stage_route_tdtt_typing
    type_theory_atlas_daily_phase_route_gives_stage_route_index).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_stage_route_tdtt_dashboard
    type_theory_atlas_daily_phase_route_gives_stage_route_index).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_stage_route_system_embeddings
    type_theory_atlas_daily_phase_route_gives_stage_route_index).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_stage_route_translation
    type_theory_atlas_daily_phase_route_gives_stage_route_index).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_stage_route_metatheory
    type_theory_atlas_daily_phase_route_gives_stage_route_index).
Qed.

Corollary type_theory_atlas_daily_phase_route_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_phase_route_artifact_index
    type_theory_atlas_daily_phase_route_consistency_holds).
Qed.

Record type_theory_atlas_daily_final_route_certificate : Prop := {
  atlas_daily_final_route_report :
    type_theory_atlas_automation_daily_report;
  atlas_daily_final_route_daily_complete :
    type_theory_atlas_daily_completion_certificate;
  atlas_daily_final_route_phase_consistency :
    type_theory_atlas_daily_phase_route_consistency;
  atlas_daily_final_route_stage_route_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_daily_final_route_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_daily_final_route_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_final_route_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_final_route_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_final_route_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_final_route_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_final_route_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_final_route_translation :
    atlas_translation_reliability_summary;
  atlas_daily_final_route_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_final_route_artifact_index :
    type_theory_atlas_artifact_index
}.

Theorem type_theory_atlas_daily_final_route_certificate_holds :
  type_theory_atlas_daily_final_route_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_complete_gives_report.
  - apply type_theory_atlas_daily_complete.
  - apply type_theory_atlas_daily_phase_route_consistency_holds.
  - apply type_theory_atlas_daily_phase_route_gives_stage_route_index.
  - apply type_theory_atlas_daily_phase_route_gives_phase_order.
  - apply type_theory_atlas_daily_phase_route_gives_unified_syntax.
  - apply type_theory_atlas_daily_phase_route_gives_mltt.
  - apply type_theory_atlas_daily_phase_route_gives_utt.
  - apply type_theory_atlas_daily_phase_route_gives_tdtt_typing.
  - apply type_theory_atlas_daily_phase_route_gives_tdtt_dashboard.
  - apply type_theory_atlas_daily_phase_route_gives_system_embeddings.
  - apply type_theory_atlas_daily_phase_route_gives_translation.
  - apply type_theory_atlas_daily_phase_route_gives_metatheory.
  - apply type_theory_atlas_daily_phase_route_gives_artifact_index.
Qed.

Corollary type_theory_atlas_daily_complete_gives_final_route_certificate :
  type_theory_atlas_daily_final_route_certificate.
Proof.
  apply type_theory_atlas_daily_final_route_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_final_route_gives_report :
  type_theory_atlas_automation_daily_report.
Proof.
  exact (atlas_daily_final_route_report
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_daily_complete :
  type_theory_atlas_daily_completion_certificate.
Proof.
  exact (atlas_daily_final_route_daily_complete
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_phase_consistency :
  type_theory_atlas_daily_phase_route_consistency.
Proof.
  exact (atlas_daily_final_route_phase_consistency
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_stage_route_index :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_daily_final_route_stage_route_index
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_daily_final_route_phase_order
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_final_route_unified_syntax
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_final_route_mltt
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_final_route_utt
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_final_route_tdtt_typing
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_final_route_tdtt_dashboard
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_final_route_system_embeddings
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_final_route_translation
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_final_route_metatheory
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_route_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_final_route_artifact_index
    type_theory_atlas_daily_final_route_certificate_holds).
Qed.

Record type_theory_atlas_daily_automation_final_entry_index : Prop := {
  atlas_daily_final_entry_daily_complete :
    type_theory_atlas_daily_completion_certificate;
  atlas_daily_final_entry_complete_entry :
    type_theory_atlas_final_delivery_index;
  atlas_daily_final_entry_final_route :
    type_theory_atlas_daily_final_route_certificate;
  atlas_daily_final_entry_report :
    type_theory_atlas_automation_daily_report;
  atlas_daily_final_entry_phase_consistency :
    type_theory_atlas_daily_phase_route_consistency;
  atlas_daily_final_entry_stage_route_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_daily_final_entry_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_daily_final_entry_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_final_entry_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_final_entry_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_final_entry_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_final_entry_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_final_entry_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_final_entry_translation :
    atlas_translation_reliability_summary;
  atlas_daily_final_entry_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_final_entry_artifact_index :
    type_theory_atlas_artifact_index
}.

Theorem type_theory_atlas_daily_automation_final_entry_index_holds :
  type_theory_atlas_daily_automation_final_entry_index.
Proof.
  constructor.
  - apply type_theory_atlas_daily_complete.
  - apply type_theory_atlas_daily_complete_gives_complete_entry.
  - apply type_theory_atlas_daily_final_route_certificate_holds.
  - apply type_theory_atlas_daily_final_route_gives_report.
  - apply type_theory_atlas_daily_final_route_gives_phase_consistency.
  - apply type_theory_atlas_daily_final_route_gives_stage_route_index.
  - apply type_theory_atlas_daily_final_route_gives_phase_order.
  - apply type_theory_atlas_daily_final_route_gives_unified_syntax.
  - apply type_theory_atlas_daily_final_route_gives_mltt.
  - apply type_theory_atlas_daily_final_route_gives_utt.
  - apply type_theory_atlas_daily_final_route_gives_tdtt_typing.
  - apply type_theory_atlas_daily_final_route_gives_tdtt_dashboard.
  - apply type_theory_atlas_daily_final_route_gives_system_embeddings.
  - apply type_theory_atlas_daily_final_route_gives_translation.
  - apply type_theory_atlas_daily_final_route_gives_metatheory.
  - apply type_theory_atlas_daily_final_route_gives_artifact_index.
Qed.

Corollary type_theory_atlas_daily_complete_gives_automation_final_entry_index :
  type_theory_atlas_daily_automation_final_entry_index.
Proof.
  apply type_theory_atlas_daily_automation_final_entry_index_holds.
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_daily_complete :
  type_theory_atlas_daily_completion_certificate.
Proof.
  exact (atlas_daily_final_entry_daily_complete
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_complete_entry :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_final_entry_complete_entry
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_final_route :
  type_theory_atlas_daily_final_route_certificate.
Proof.
  exact (atlas_daily_final_entry_final_route
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_report :
  type_theory_atlas_automation_daily_report.
Proof.
  exact (atlas_daily_final_entry_report
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_phase_consistency :
  type_theory_atlas_daily_phase_route_consistency.
Proof.
  exact (atlas_daily_final_entry_phase_consistency
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_stage_route_index :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_daily_final_entry_stage_route_index
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_daily_final_entry_phase_order
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_final_entry_unified_syntax
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_final_entry_mltt
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_final_entry_utt
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_final_entry_tdtt_typing
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_final_entry_tdtt_dashboard
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_final_entry_system_embeddings
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_final_entry_translation
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_final_entry_metatheory
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_entry_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_final_entry_artifact_index
    type_theory_atlas_daily_automation_final_entry_index_holds).
Qed.

Record type_theory_atlas_daily_deliverable_completion_certificate : Prop := {
  atlas_daily_deliverable_final_entry_index :
    type_theory_atlas_daily_automation_final_entry_index;
  atlas_daily_deliverable_daily_complete :
    type_theory_atlas_daily_completion_certificate;
  atlas_daily_deliverable_complete_entry :
    type_theory_atlas_final_delivery_index;
  atlas_daily_deliverable_final_route :
    type_theory_atlas_daily_final_route_certificate;
  atlas_daily_deliverable_report :
    type_theory_atlas_automation_daily_report;
  atlas_daily_deliverable_phase_consistency :
    type_theory_atlas_daily_phase_route_consistency;
  atlas_daily_deliverable_stage_route_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_daily_deliverable_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_daily_deliverable_release_summary :
    type_theory_atlas_release_summary;
  atlas_daily_deliverable_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_daily_deliverable_artifact_index :
    type_theory_atlas_artifact_index;
  atlas_daily_deliverable_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_deliverable_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_deliverable_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_deliverable_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_deliverable_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_deliverable_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_deliverable_translation :
    atlas_translation_reliability_summary;
  atlas_daily_deliverable_metatheory :
    type_theory_atlas_main_theorem
}.

Theorem type_theory_atlas_daily_deliverable_completion_certificate_holds :
  type_theory_atlas_daily_deliverable_completion_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_automation_final_entry_index_holds.
  - apply type_theory_atlas_daily_final_entry_gives_daily_complete.
  - apply type_theory_atlas_daily_final_entry_gives_complete_entry.
  - apply type_theory_atlas_daily_final_entry_gives_final_route.
  - apply type_theory_atlas_daily_final_entry_gives_report.
  - apply type_theory_atlas_daily_final_entry_gives_phase_consistency.
  - apply type_theory_atlas_daily_final_entry_gives_stage_route_index.
  - apply type_theory_atlas_daily_final_entry_gives_phase_order.
  - apply type_theory_atlas_release_summary_holds.
  - apply type_theory_atlas_project_status_certificate_holds.
  - apply type_theory_atlas_daily_final_entry_gives_artifact_index.
  - apply type_theory_atlas_daily_final_entry_gives_unified_syntax.
  - apply type_theory_atlas_daily_final_entry_gives_mltt.
  - apply type_theory_atlas_daily_final_entry_gives_utt.
  - apply type_theory_atlas_daily_final_entry_gives_tdtt_typing.
  - apply type_theory_atlas_daily_final_entry_gives_tdtt_dashboard.
  - apply type_theory_atlas_daily_final_entry_gives_system_embeddings.
  - apply type_theory_atlas_daily_final_entry_gives_translation.
  - apply type_theory_atlas_daily_final_entry_gives_metatheory.
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_completion :
  type_theory_atlas_daily_deliverable_completion_certificate.
Proof.
  apply type_theory_atlas_daily_deliverable_completion_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_final_entry_index :
  type_theory_atlas_daily_automation_final_entry_index.
Proof.
  exact (atlas_daily_deliverable_final_entry_index
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_daily_complete :
  type_theory_atlas_daily_completion_certificate.
Proof.
  exact (atlas_daily_deliverable_daily_complete
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_complete_entry :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_deliverable_complete_entry
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_final_route :
  type_theory_atlas_daily_final_route_certificate.
Proof.
  exact (atlas_daily_deliverable_final_route
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_report :
  type_theory_atlas_automation_daily_report.
Proof.
  exact (atlas_daily_deliverable_report
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_phase_consistency :
  type_theory_atlas_daily_phase_route_consistency.
Proof.
  exact (atlas_daily_deliverable_phase_consistency
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_stage_route_index :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_daily_deliverable_stage_route_index
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_daily_deliverable_phase_order
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_daily_deliverable_release_summary
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_daily_deliverable_project_status
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_deliverable_artifact_index
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_deliverable_unified_syntax
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_deliverable_mltt
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_deliverable_utt
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_deliverable_tdtt_typing
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_deliverable_tdtt_dashboard
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_deliverable_system_embeddings
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_deliverable_translation
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_deliverable_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_deliverable_metatheory
    type_theory_atlas_daily_deliverable_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_final_entry_index :
  type_theory_atlas_daily_automation_final_entry_index.
Proof.
  exact (atlas_daily_deliverable_final_entry_index
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_complete_entry :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_deliverable_complete_entry
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_final_route :
  type_theory_atlas_daily_final_route_certificate.
Proof.
  exact (atlas_daily_deliverable_final_route
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_report :
  type_theory_atlas_automation_daily_report.
Proof.
  exact (atlas_daily_deliverable_report
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_phase_consistency :
  type_theory_atlas_daily_phase_route_consistency.
Proof.
  exact (atlas_daily_deliverable_phase_consistency
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_stage_route_index :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_daily_deliverable_stage_route_index
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_daily_deliverable_phase_order
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_daily_deliverable_release_summary
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_daily_deliverable_project_status
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_deliverable_artifact_index
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_deliverable_unified_syntax
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_deliverable_mltt
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_deliverable_utt
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_deliverable_tdtt_typing
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_deliverable_tdtt_dashboard
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_deliverable_system_embeddings
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_deliverable_translation
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Corollary type_theory_atlas_daily_complete_gives_deliverable_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_deliverable_metatheory
    type_theory_atlas_daily_complete_gives_deliverable_completion).
Qed.

Record type_theory_atlas_daily_report_facade : Prop := {
  atlas_daily_facade_entry_point :
    type_theory_atlas_daily_completion_certificate;
  atlas_daily_facade_deliverable_completion :
    type_theory_atlas_daily_deliverable_completion_certificate;
  atlas_daily_facade_final_entry_index :
    type_theory_atlas_daily_automation_final_entry_index;
  atlas_daily_facade_complete_entry :
    type_theory_atlas_final_delivery_index;
  atlas_daily_facade_final_route :
    type_theory_atlas_daily_final_route_certificate;
  atlas_daily_facade_report :
    type_theory_atlas_automation_daily_report;
  atlas_daily_facade_phase_consistency :
    type_theory_atlas_daily_phase_route_consistency;
  atlas_daily_facade_stage_route_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_daily_facade_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_daily_facade_release_summary :
    type_theory_atlas_release_summary;
  atlas_daily_facade_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_daily_facade_artifact_index :
    type_theory_atlas_artifact_index;
  atlas_daily_facade_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_facade_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_facade_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_facade_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_facade_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_facade_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_facade_translation :
    atlas_translation_reliability_summary;
  atlas_daily_facade_metatheory :
    type_theory_atlas_main_theorem
}.

Theorem type_theory_atlas_daily_report_facade_holds :
  type_theory_atlas_daily_report_facade.
Proof.
  constructor.
  - apply type_theory_atlas_daily_complete.
  - apply type_theory_atlas_daily_complete_gives_deliverable_completion.
  - apply type_theory_atlas_daily_complete_gives_deliverable_final_entry_index.
  - apply type_theory_atlas_daily_complete_gives_deliverable_complete_entry.
  - apply type_theory_atlas_daily_complete_gives_deliverable_final_route.
  - apply type_theory_atlas_daily_complete_gives_deliverable_report.
  - apply type_theory_atlas_daily_complete_gives_deliverable_phase_consistency.
  - apply type_theory_atlas_daily_complete_gives_deliverable_stage_route_index.
  - apply type_theory_atlas_daily_complete_gives_deliverable_phase_order.
  - apply type_theory_atlas_daily_complete_gives_deliverable_release_summary.
  - apply type_theory_atlas_daily_complete_gives_deliverable_project_status.
  - apply type_theory_atlas_daily_complete_gives_deliverable_artifact_index.
  - apply type_theory_atlas_daily_complete_gives_deliverable_unified_syntax.
  - apply type_theory_atlas_daily_complete_gives_deliverable_mltt.
  - apply type_theory_atlas_daily_complete_gives_deliverable_utt.
  - apply type_theory_atlas_daily_complete_gives_deliverable_tdtt_typing.
  - apply type_theory_atlas_daily_complete_gives_deliverable_tdtt_dashboard.
  - apply type_theory_atlas_daily_complete_gives_deliverable_system_embeddings.
  - apply type_theory_atlas_daily_complete_gives_deliverable_translation.
  - apply type_theory_atlas_daily_complete_gives_deliverable_metatheory.
Qed.

Corollary type_theory_atlas_daily_complete_gives_report_facade :
  type_theory_atlas_daily_report_facade.
Proof.
  apply type_theory_atlas_daily_report_facade_holds.
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_entry_point :
  type_theory_atlas_daily_completion_certificate.
Proof.
  exact (atlas_daily_facade_entry_point
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_deliverable_completion :
  type_theory_atlas_daily_deliverable_completion_certificate.
Proof.
  exact (atlas_daily_facade_deliverable_completion
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_final_entry_index :
  type_theory_atlas_daily_automation_final_entry_index.
Proof.
  exact (atlas_daily_facade_final_entry_index
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_complete_entry :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_facade_complete_entry
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_final_route :
  type_theory_atlas_daily_final_route_certificate.
Proof.
  exact (atlas_daily_facade_final_route
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_report :
  type_theory_atlas_automation_daily_report.
Proof.
  exact (atlas_daily_facade_report
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_phase_consistency :
  type_theory_atlas_daily_phase_route_consistency.
Proof.
  exact (atlas_daily_facade_phase_consistency
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_stage_route_index :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_daily_facade_stage_route_index
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_daily_facade_phase_order
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_daily_facade_release_summary
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_daily_facade_project_status
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_artifact_index :
  type_theory_atlas_artifact_index.
Proof.
  exact (atlas_daily_facade_artifact_index
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_facade_unified_syntax
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_facade_mltt
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_facade_utt
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_facade_tdtt_typing
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_facade_tdtt_dashboard
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_facade_system_embeddings
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_facade_translation
    type_theory_atlas_daily_report_facade_holds).
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_facade_metatheory
    type_theory_atlas_daily_report_facade_holds).
Qed.

Record type_theory_atlas_daily_release_certificate : Prop := {
  atlas_daily_release_facade :
    type_theory_atlas_daily_report_facade;
  atlas_daily_release_stage_route_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_daily_release_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_daily_release_final_delivery_index :
    type_theory_atlas_final_delivery_index;
  atlas_daily_release_paper_claim_index :
    type_theory_atlas_paper_claim_index;
  atlas_daily_release_paper_statement :
    type_theory_atlas_paper_statement;
  atlas_daily_release_main_theorem :
    type_theory_atlas_main_theorem
}.

Theorem type_theory_atlas_daily_release_certificate_holds :
  type_theory_atlas_daily_release_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_report_facade_holds.
  - apply type_theory_atlas_daily_report_facade_gives_stage_route_index.
  - apply type_theory_atlas_daily_report_facade_gives_phase_order.
  - apply type_theory_atlas_daily_report_facade_gives_complete_entry.
  - apply type_theory_atlas_final_delivery_gives_paper_claim_index.
  - apply type_theory_atlas_paper_statement_holds.
  - apply type_theory_atlas_daily_report_facade_gives_metatheory.
Qed.

Corollary type_theory_atlas_daily_report_facade_gives_release_certificate :
  type_theory_atlas_daily_release_certificate.
Proof.
  apply type_theory_atlas_daily_release_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_release_gives_report_facade :
  type_theory_atlas_daily_report_facade.
Proof.
  exact (atlas_daily_release_facade
    type_theory_atlas_daily_release_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_release_gives_stage_route_index :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_daily_release_stage_route_index
    type_theory_atlas_daily_release_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_release_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_daily_release_phase_order
    type_theory_atlas_daily_release_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_release_gives_final_delivery_index :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_release_final_delivery_index
    type_theory_atlas_daily_release_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_release_gives_paper_claim_index :
  type_theory_atlas_paper_claim_index.
Proof.
  exact (atlas_daily_release_paper_claim_index
    type_theory_atlas_daily_release_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_release_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_release_paper_statement
    type_theory_atlas_daily_release_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_release_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_release_main_theorem
    type_theory_atlas_daily_release_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_release_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_phase_unified_syntax_framework
    (atlas_daily_release_phase_order
      type_theory_atlas_daily_release_certificate_holds)).
Qed.

Corollary type_theory_atlas_daily_release_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_phase_mltt_typing_support
    (atlas_daily_release_phase_order
      type_theory_atlas_daily_release_certificate_holds)).
Qed.

Corollary type_theory_atlas_daily_release_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_phase_utt_typing_support
    (atlas_daily_release_phase_order
      type_theory_atlas_daily_release_certificate_holds)).
Qed.

Corollary type_theory_atlas_daily_release_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_phase_tdtt_typing_support
    (atlas_daily_release_phase_order
      type_theory_atlas_daily_release_certificate_holds)).
Qed.

Corollary type_theory_atlas_daily_release_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_phase_tdtt_dashboard
    (atlas_daily_release_phase_order
      type_theory_atlas_daily_release_certificate_holds)).
Qed.

Corollary type_theory_atlas_daily_release_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_phase_system_embeddings
    (atlas_daily_release_phase_order
      type_theory_atlas_daily_release_certificate_holds)).
Qed.

Corollary type_theory_atlas_daily_release_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_phase_translation_reliability
    (atlas_daily_release_phase_order
      type_theory_atlas_daily_release_certificate_holds)).
Qed.

Corollary type_theory_atlas_daily_release_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  apply type_theory_atlas_daily_release_gives_main_theorem.
Qed.

Record type_theory_atlas_daily_release_stage_consistency : Prop := {
  atlas_release_stage_consistency_certificate :
    type_theory_atlas_daily_release_certificate;
  atlas_release_stage_consistency_phase_order :
    type_theory_atlas_phase_order_certificate;
  atlas_release_stage_consistency_stage_route_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_release_stage_consistency_phase_built_stage_route_index :
    type_theory_atlas_daily_stage_route_index;
  atlas_release_stage_consistency_unified_syntax :
    type_theory_atlas_coverage;
  atlas_release_stage_consistency_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_release_stage_consistency_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_release_stage_consistency_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_release_stage_consistency_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_release_stage_consistency_translation :
    atlas_translation_reliability_summary;
  atlas_release_stage_consistency_metatheory :
    type_theory_atlas_main_theorem
}.

Theorem type_theory_atlas_daily_release_stage_consistency_holds :
  type_theory_atlas_daily_release_stage_consistency.
Proof.
  constructor.
  - apply type_theory_atlas_daily_release_certificate_holds.
  - apply type_theory_atlas_daily_release_gives_phase_order.
  - apply type_theory_atlas_daily_release_gives_stage_route_index.
  - apply type_theory_atlas_daily_stage_route_index_from_phase_order.
    + apply type_theory_atlas_daily_report_facade_gives_entry_point.
    + apply type_theory_atlas_daily_release_gives_phase_order.
  - apply type_theory_atlas_daily_release_gives_unified_syntax.
  - apply type_theory_atlas_daily_release_gives_mltt.
  - apply type_theory_atlas_daily_release_gives_utt.
  - apply type_theory_atlas_daily_release_gives_tdtt_typing.
  - apply type_theory_atlas_daily_release_gives_system_embeddings.
  - apply type_theory_atlas_daily_release_gives_translation.
  - apply type_theory_atlas_daily_release_gives_metatheory.
Qed.

Corollary type_theory_atlas_daily_release_gives_stage_consistency :
  type_theory_atlas_daily_release_stage_consistency.
Proof.
  apply type_theory_atlas_daily_release_stage_consistency_holds.
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_release :
  type_theory_atlas_daily_release_certificate.
Proof.
  exact (atlas_release_stage_consistency_certificate
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_stage_route :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_release_stage_consistency_stage_route_index
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_phase_built_route :
  type_theory_atlas_daily_stage_route_index.
Proof.
  exact (atlas_release_stage_consistency_phase_built_stage_route_index
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_phase_order :
  type_theory_atlas_phase_order_certificate.
Proof.
  exact (atlas_release_stage_consistency_phase_order
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_release_stage_consistency_unified_syntax
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_release_stage_consistency_mltt
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_release_stage_consistency_utt
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_release_stage_consistency_tdtt_typing
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_stage_route_tdtt_dashboard
    (atlas_release_stage_consistency_stage_route_index
      type_theory_atlas_daily_release_stage_consistency_holds)).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_release_stage_consistency_system_embeddings
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_release_stage_consistency_translation
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Corollary type_theory_atlas_daily_release_stage_consistency_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_release_stage_consistency_metatheory
    type_theory_atlas_daily_release_stage_consistency_holds).
Qed.

Record type_theory_atlas_daily_report_conclusion : Prop := {
  atlas_daily_conclusion_release_certificate :
    type_theory_atlas_daily_release_certificate;
  atlas_daily_conclusion_stage_consistency :
    type_theory_atlas_daily_release_stage_consistency;
  atlas_daily_conclusion_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_conclusion_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_conclusion_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_conclusion_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_conclusion_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_conclusion_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_conclusion_translation :
    atlas_translation_reliability_summary;
  atlas_daily_conclusion_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_conclusion_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_report_conclusion_holds :
  type_theory_atlas_daily_report_conclusion.
Proof.
  constructor.
  - apply type_theory_atlas_daily_release_certificate_holds.
  - apply type_theory_atlas_daily_release_stage_consistency_holds.
  - apply type_theory_atlas_daily_release_stage_consistency_gives_unified_syntax.
  - apply type_theory_atlas_daily_release_stage_consistency_gives_mltt.
  - apply type_theory_atlas_daily_release_stage_consistency_gives_utt.
  - apply type_theory_atlas_daily_release_stage_consistency_gives_tdtt_typing.
  - apply type_theory_atlas_daily_release_stage_consistency_gives_tdtt_dashboard.
  - apply type_theory_atlas_daily_release_stage_consistency_gives_system_embeddings.
  - apply type_theory_atlas_daily_release_stage_consistency_gives_translation.
  - apply type_theory_atlas_daily_release_stage_consistency_gives_metatheory.
  - apply type_theory_atlas_daily_release_gives_paper_statement.
Qed.

Corollary type_theory_atlas_daily_release_gives_report_conclusion :
  type_theory_atlas_daily_report_conclusion.
Proof.
  apply type_theory_atlas_daily_report_conclusion_holds.
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_release_certificate :
  type_theory_atlas_daily_release_certificate.
Proof.
  exact (atlas_daily_conclusion_release_certificate
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_stage_consistency :
  type_theory_atlas_daily_release_stage_consistency.
Proof.
  exact (atlas_daily_conclusion_stage_consistency
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_conclusion_unified_syntax
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_conclusion_mltt
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_conclusion_utt
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_conclusion_tdtt_typing
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_conclusion_tdtt_dashboard
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_conclusion_system_embeddings
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_conclusion_translation
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_conclusion_metatheory
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_conclusion_paper_statement
    type_theory_atlas_daily_report_conclusion_holds).
Qed.

Record type_theory_atlas_daily_conclusion_stage_order_summary : Prop := {
  atlas_daily_conclusion_stage_order_conclusion :
    type_theory_atlas_daily_report_conclusion;
  atlas_daily_conclusion_stage1_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_conclusion_stage2_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_conclusion_stage3_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_conclusion_stage4_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_conclusion_stage4_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_conclusion_stage5_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_conclusion_stage5_translation :
    atlas_translation_reliability_summary;
  atlas_daily_conclusion_stage6_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_conclusion_stage6_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_conclusion_stage_order_summary_holds :
  type_theory_atlas_daily_conclusion_stage_order_summary.
Proof.
  constructor.
  - apply type_theory_atlas_daily_report_conclusion_holds.
  - apply type_theory_atlas_daily_report_conclusion_gives_unified_syntax.
  - apply type_theory_atlas_daily_report_conclusion_gives_mltt.
  - apply type_theory_atlas_daily_report_conclusion_gives_utt.
  - apply type_theory_atlas_daily_report_conclusion_gives_tdtt_typing.
  - apply type_theory_atlas_daily_report_conclusion_gives_tdtt_dashboard.
  - apply type_theory_atlas_daily_report_conclusion_gives_system_embeddings.
  - apply type_theory_atlas_daily_report_conclusion_gives_translation.
  - apply type_theory_atlas_daily_report_conclusion_gives_metatheory.
  - apply type_theory_atlas_daily_report_conclusion_gives_paper_statement.
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_stage_order_summary :
  type_theory_atlas_daily_conclusion_stage_order_summary.
Proof.
  apply type_theory_atlas_daily_conclusion_stage_order_summary_holds.
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_conclusion :
  type_theory_atlas_daily_report_conclusion.
Proof.
  exact (atlas_daily_conclusion_stage_order_conclusion
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_conclusion_stage1_unified_syntax
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_conclusion_stage2_mltt
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_conclusion_stage3_utt
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_conclusion_stage4_tdtt_typing
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_conclusion_stage4_tdtt_dashboard
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_conclusion_stage5_system_embeddings
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage5_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_conclusion_stage5_translation
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_conclusion_stage6_metatheory
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Corollary type_theory_atlas_daily_conclusion_stage_order_gives_stage6_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_conclusion_stage6_paper_statement
    type_theory_atlas_daily_conclusion_stage_order_summary_holds).
Qed.

Record type_theory_atlas_daily_final_report_index : Prop := {
  atlas_daily_final_report_conclusion :
    type_theory_atlas_daily_report_conclusion;
  atlas_daily_final_report_stage_order_summary :
    type_theory_atlas_daily_conclusion_stage_order_summary;
  atlas_daily_final_report_release_certificate :
    type_theory_atlas_daily_release_certificate;
  atlas_daily_final_report_stage_consistency :
    type_theory_atlas_daily_release_stage_consistency;
  atlas_daily_final_report_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_final_report_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_final_report_index_holds :
  type_theory_atlas_daily_final_report_index.
Proof.
  constructor.
  - apply type_theory_atlas_daily_report_conclusion_holds.
  - apply type_theory_atlas_daily_conclusion_stage_order_summary_holds.
  - apply type_theory_atlas_daily_report_conclusion_gives_release_certificate.
  - apply type_theory_atlas_daily_report_conclusion_gives_stage_consistency.
  - apply type_theory_atlas_daily_report_conclusion_gives_metatheory.
  - apply type_theory_atlas_daily_report_conclusion_gives_paper_statement.
Qed.

Corollary type_theory_atlas_daily_report_conclusion_gives_final_report_index :
  type_theory_atlas_daily_final_report_index.
Proof.
  apply type_theory_atlas_daily_final_report_index_holds.
Qed.

Corollary type_theory_atlas_daily_final_report_gives_conclusion :
  type_theory_atlas_daily_report_conclusion.
Proof.
  exact (atlas_daily_final_report_conclusion
    type_theory_atlas_daily_final_report_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage_order_summary :
  type_theory_atlas_daily_conclusion_stage_order_summary.
Proof.
  exact (atlas_daily_final_report_stage_order_summary
    type_theory_atlas_daily_final_report_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_release_certificate :
  type_theory_atlas_daily_release_certificate.
Proof.
  exact (atlas_daily_final_report_release_certificate
    type_theory_atlas_daily_final_report_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage_consistency :
  type_theory_atlas_daily_release_stage_consistency.
Proof.
  exact (atlas_daily_final_report_stage_consistency
    type_theory_atlas_daily_final_report_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_final_report_metatheory
    type_theory_atlas_daily_final_report_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_final_report_paper_statement
    type_theory_atlas_daily_final_report_index_holds).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_conclusion_stage1_unified_syntax
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_conclusion_stage2_mltt
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_conclusion_stage3_utt
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_conclusion_stage4_tdtt_typing
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_conclusion_stage4_tdtt_dashboard
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_conclusion_stage5_system_embeddings
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage5_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_conclusion_stage5_translation
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_conclusion_stage6_metatheory
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage6_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_conclusion_stage6_paper_statement
    (atlas_daily_final_report_stage_order_summary
      type_theory_atlas_daily_final_report_index_holds)).
Qed.

Record type_theory_atlas_daily_final_stage_sync_certificate : Prop := {
  atlas_daily_final_stage_sync_final_report :
    type_theory_atlas_daily_final_report_index;
  atlas_daily_final_stage_sync_stage_order_summary :
    type_theory_atlas_daily_conclusion_stage_order_summary;
  atlas_daily_final_stage_sync_stage1_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_final_stage_sync_stage2_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_final_stage_sync_stage3_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_final_stage_sync_stage4_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_final_stage_sync_stage4_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_final_stage_sync_stage5_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_final_stage_sync_stage5_translation :
    atlas_translation_reliability_summary;
  atlas_daily_final_stage_sync_stage6_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_final_stage_sync_stage6_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_final_stage_sync_certificate_holds :
  type_theory_atlas_daily_final_stage_sync_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_final_report_index_holds.
  - apply type_theory_atlas_daily_final_report_gives_stage_order_summary.
  - apply type_theory_atlas_daily_final_report_gives_stage1_unified_syntax.
  - apply type_theory_atlas_daily_final_report_gives_stage2_mltt.
  - apply type_theory_atlas_daily_final_report_gives_stage3_utt.
  - apply type_theory_atlas_daily_final_report_gives_stage4_tdtt_typing.
  - apply type_theory_atlas_daily_final_report_gives_stage4_tdtt_dashboard.
  - apply type_theory_atlas_daily_final_report_gives_stage5_system_embeddings.
  - apply type_theory_atlas_daily_final_report_gives_stage5_translation.
  - apply type_theory_atlas_daily_final_report_gives_stage6_metatheory.
  - apply type_theory_atlas_daily_final_report_gives_stage6_paper_statement.
Qed.

Corollary type_theory_atlas_daily_final_report_gives_stage_sync_certificate :
  type_theory_atlas_daily_final_stage_sync_certificate.
Proof.
  apply type_theory_atlas_daily_final_stage_sync_certificate_holds.
Qed.

Record type_theory_atlas_daily_automation_summary_certificate : Prop := {
  atlas_daily_automation_summary_final_report :
    type_theory_atlas_daily_final_report_index;
  atlas_daily_automation_summary_stage_sync :
    type_theory_atlas_daily_final_stage_sync_certificate;
  atlas_daily_automation_summary_conclusion :
    type_theory_atlas_daily_report_conclusion;
  atlas_daily_automation_summary_release_certificate :
    type_theory_atlas_daily_release_certificate;
  atlas_daily_automation_summary_facade :
    type_theory_atlas_daily_report_facade;
  atlas_daily_automation_summary_daily_complete :
    type_theory_atlas_daily_completion_certificate;
  atlas_daily_automation_summary_artifact_complete :
    type_theory_atlas_final_delivery_index;
  atlas_daily_automation_summary_release_summary :
    type_theory_atlas_release_summary;
  atlas_daily_automation_summary_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_daily_automation_summary_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_automation_summary_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_automation_summary_certificate_holds :
  type_theory_atlas_daily_automation_summary_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_final_report_index_holds.
  - apply type_theory_atlas_daily_final_stage_sync_certificate_holds.
  - apply type_theory_atlas_daily_final_report_gives_conclusion.
  - apply type_theory_atlas_daily_final_report_gives_release_certificate.
  - apply type_theory_atlas_daily_release_gives_report_facade.
  - apply type_theory_atlas_daily_complete.
  - apply type_theory_atlas_complete.
  - apply type_theory_atlas_daily_report_facade_gives_release_summary.
  - apply type_theory_atlas_daily_report_facade_gives_project_status.
  - apply type_theory_atlas_daily_final_report_gives_metatheory.
  - apply type_theory_atlas_daily_final_report_gives_paper_statement.
Qed.

Corollary type_theory_atlas_daily_final_report_gives_automation_summary_certificate :
  type_theory_atlas_daily_automation_summary_certificate.
Proof.
  apply type_theory_atlas_daily_automation_summary_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_final_report :
  type_theory_atlas_daily_final_report_index.
Proof.
  exact (atlas_daily_automation_summary_final_report
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage_sync :
  type_theory_atlas_daily_final_stage_sync_certificate.
Proof.
  exact (atlas_daily_automation_summary_stage_sync
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_conclusion :
  type_theory_atlas_daily_report_conclusion.
Proof.
  exact (atlas_daily_automation_summary_conclusion
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_release_certificate :
  type_theory_atlas_daily_release_certificate.
Proof.
  exact (atlas_daily_automation_summary_release_certificate
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_facade :
  type_theory_atlas_daily_report_facade.
Proof.
  exact (atlas_daily_automation_summary_facade
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_daily_complete :
  type_theory_atlas_daily_completion_certificate.
Proof.
  exact (atlas_daily_automation_summary_daily_complete
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_artifact_complete :
  type_theory_atlas_final_delivery_index.
Proof.
  exact (atlas_daily_automation_summary_artifact_complete
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_daily_automation_summary_release_summary
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_daily_automation_summary_project_status
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_automation_summary_metatheory
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_automation_summary_paper_statement
    type_theory_atlas_daily_automation_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_final_stage_sync_stage1_unified_syntax
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_final_stage_sync_stage2_mltt
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_final_stage_sync_stage3_utt
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_final_stage_sync_stage4_tdtt_typing
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_final_stage_sync_stage4_tdtt_dashboard
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_final_stage_sync_stage5_system_embeddings
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage5_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_final_stage_sync_stage5_translation
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_final_stage_sync_stage6_metatheory
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage6_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_final_stage_sync_stage6_paper_statement
    type_theory_atlas_daily_automation_summary_gives_stage_sync).
Qed.

Record type_theory_atlas_daily_automation_stage_route_certificate : Prop := {
  atlas_daily_automation_stage_route_summary :
    type_theory_atlas_daily_automation_summary_certificate;
  atlas_daily_automation_stage_route_stage_sync :
    type_theory_atlas_daily_final_stage_sync_certificate;
  atlas_daily_automation_stage_route_stage1_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_automation_stage_route_stage2_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_automation_stage_route_stage3_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_automation_stage_route_stage4_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_automation_stage_route_stage4_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_automation_stage_route_stage5_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_automation_stage_route_stage5_translation :
    atlas_translation_reliability_summary;
  atlas_daily_automation_stage_route_stage6_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_automation_stage_route_stage6_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_automation_stage_route_certificate_holds :
  type_theory_atlas_daily_automation_stage_route_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_automation_summary_certificate_holds.
  - apply type_theory_atlas_daily_automation_summary_gives_stage_sync.
  - apply type_theory_atlas_daily_automation_summary_gives_stage1_unified_syntax.
  - apply type_theory_atlas_daily_automation_summary_gives_stage2_mltt.
  - apply type_theory_atlas_daily_automation_summary_gives_stage3_utt.
  - apply type_theory_atlas_daily_automation_summary_gives_stage4_tdtt_typing.
  - apply type_theory_atlas_daily_automation_summary_gives_stage4_tdtt_dashboard.
  - apply type_theory_atlas_daily_automation_summary_gives_stage5_system_embeddings.
  - apply type_theory_atlas_daily_automation_summary_gives_stage5_translation.
  - apply type_theory_atlas_daily_automation_summary_gives_stage6_metatheory.
  - apply type_theory_atlas_daily_automation_summary_gives_stage6_paper_statement.
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_stage_route_certificate :
  type_theory_atlas_daily_automation_stage_route_certificate.
Proof.
  apply type_theory_atlas_daily_automation_stage_route_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_summary :
  type_theory_atlas_daily_automation_summary_certificate.
Proof.
  exact (atlas_daily_automation_stage_route_summary
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage_sync :
  type_theory_atlas_daily_final_stage_sync_certificate.
Proof.
  exact (atlas_daily_automation_stage_route_stage_sync
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_automation_stage_route_stage1_unified_syntax
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_automation_stage_route_stage2_mltt
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_automation_stage_route_stage3_utt
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_automation_stage_route_stage4_tdtt_typing
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_automation_stage_route_stage4_tdtt_dashboard
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_automation_stage_route_stage5_system_embeddings
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage5_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_automation_stage_route_stage5_translation
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_automation_stage_route_stage6_metatheory
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_automation_stage_route_gives_stage6_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_automation_stage_route_stage6_paper_statement
    type_theory_atlas_daily_automation_stage_route_certificate_holds).
Qed.

Record type_theory_atlas_daily_final_dashboard_certificate : Prop := {
  atlas_daily_final_dashboard_automation_summary :
    type_theory_atlas_daily_automation_summary_certificate;
  atlas_daily_final_dashboard_stage_route :
    type_theory_atlas_daily_automation_stage_route_certificate;
  atlas_daily_final_dashboard_final_report :
    type_theory_atlas_daily_final_report_index;
  atlas_daily_final_dashboard_stage_sync :
    type_theory_atlas_daily_final_stage_sync_certificate;
  atlas_daily_final_dashboard_release_summary :
    type_theory_atlas_release_summary;
  atlas_daily_final_dashboard_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_daily_final_dashboard_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_final_dashboard_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_final_dashboard_certificate_holds :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_automation_summary_certificate_holds.
  - apply type_theory_atlas_daily_automation_stage_route_certificate_holds.
  - apply type_theory_atlas_daily_automation_summary_gives_final_report.
  - apply type_theory_atlas_daily_automation_summary_gives_stage_sync.
  - apply type_theory_atlas_daily_automation_summary_gives_release_summary.
  - apply type_theory_atlas_daily_automation_summary_gives_project_status.
  - apply type_theory_atlas_daily_automation_summary_gives_metatheory.
  - apply type_theory_atlas_daily_automation_summary_gives_paper_statement.
Qed.

Corollary type_theory_atlas_daily_automation_summary_gives_final_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  apply type_theory_atlas_daily_final_dashboard_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_automation_summary :
  type_theory_atlas_daily_automation_summary_certificate.
Proof.
  exact (atlas_daily_final_dashboard_automation_summary
    type_theory_atlas_daily_final_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage_route :
  type_theory_atlas_daily_automation_stage_route_certificate.
Proof.
  exact (atlas_daily_final_dashboard_stage_route
    type_theory_atlas_daily_final_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_final_report :
  type_theory_atlas_daily_final_report_index.
Proof.
  exact (atlas_daily_final_dashboard_final_report
    type_theory_atlas_daily_final_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage_sync :
  type_theory_atlas_daily_final_stage_sync_certificate.
Proof.
  exact (atlas_daily_final_dashboard_stage_sync
    type_theory_atlas_daily_final_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_daily_final_dashboard_release_summary
    type_theory_atlas_daily_final_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_daily_final_dashboard_project_status
    type_theory_atlas_daily_final_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_final_dashboard_metatheory
    type_theory_atlas_daily_final_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_final_dashboard_paper_statement
    type_theory_atlas_daily_final_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_automation_stage_route_stage1_unified_syntax
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_automation_stage_route_stage2_mltt
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_automation_stage_route_stage3_utt
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_automation_stage_route_stage4_tdtt_typing
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_automation_stage_route_stage4_tdtt_dashboard
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_automation_stage_route_stage5_system_embeddings
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage5_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_automation_stage_route_stage5_translation
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_automation_stage_route_stage6_metatheory
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage6_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_automation_stage_route_stage6_paper_statement
    type_theory_atlas_daily_final_dashboard_gives_stage_route).
Qed.

Record type_theory_atlas_daily_final_dashboard_stage_route_certificate : Prop := {
  atlas_daily_final_dashboard_stage_route_dashboard :
    type_theory_atlas_daily_final_dashboard_certificate;
  atlas_daily_final_dashboard_stage_route_route :
    type_theory_atlas_daily_automation_stage_route_certificate;
  atlas_daily_final_dashboard_stage_route_stage1_unified_syntax :
    type_theory_atlas_coverage;
  atlas_daily_final_dashboard_stage_route_stage2_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_daily_final_dashboard_stage_route_stage3_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_daily_final_dashboard_stage_route_stage4_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_daily_final_dashboard_stage_route_stage4_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_daily_final_dashboard_stage_route_stage5_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_daily_final_dashboard_stage_route_stage5_translation :
    atlas_translation_reliability_summary;
  atlas_daily_final_dashboard_stage_route_stage6_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_final_dashboard_stage_route_stage6_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds :
  type_theory_atlas_daily_final_dashboard_stage_route_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_final_dashboard_certificate_holds.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage_route.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage1_unified_syntax.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage2_mltt.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage3_utt.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage4_tdtt_typing.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage4_tdtt_dashboard.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage5_system_embeddings.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage5_translation.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage6_metatheory.
  - apply type_theory_atlas_daily_final_dashboard_gives_stage6_paper_statement.
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_stage_route_certificate :
  type_theory_atlas_daily_final_dashboard_stage_route_certificate.
Proof.
  apply type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_dashboard
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_route :
  type_theory_atlas_daily_automation_stage_route_certificate.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_route
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage1_unified_syntax
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage2_mltt
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage3_utt
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage4_tdtt_typing
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage4_tdtt_dashboard
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage5_system_embeddings
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage5_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage5_translation
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage6_metatheory
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_stage_route_gives_stage6_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage6_paper_statement
    type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds).
Qed.

Record type_theory_atlas_daily_final_dashboard_completion_certificate : Prop := {
  atlas_daily_final_dashboard_completion_dashboard :
    type_theory_atlas_daily_final_dashboard_certificate;
  atlas_daily_final_dashboard_completion_stage_route :
    type_theory_atlas_daily_final_dashboard_stage_route_certificate;
  atlas_daily_final_dashboard_completion_automation_summary :
    type_theory_atlas_daily_automation_summary_certificate;
  atlas_daily_final_dashboard_completion_final_report :
    type_theory_atlas_daily_final_report_index;
  atlas_daily_final_dashboard_completion_release_summary :
    type_theory_atlas_release_summary;
  atlas_daily_final_dashboard_completion_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_daily_final_dashboard_completion_metatheory :
    type_theory_atlas_main_theorem;
  atlas_daily_final_dashboard_completion_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_daily_final_dashboard_completion_certificate_holds :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_final_dashboard_certificate_holds.
  - apply type_theory_atlas_daily_final_dashboard_stage_route_certificate_holds.
  - apply type_theory_atlas_daily_final_dashboard_gives_automation_summary.
  - apply type_theory_atlas_daily_final_dashboard_gives_final_report.
  - apply type_theory_atlas_daily_final_dashboard_gives_release_summary.
  - apply type_theory_atlas_daily_final_dashboard_gives_project_status.
  - apply type_theory_atlas_daily_final_dashboard_gives_metatheory.
  - apply type_theory_atlas_daily_final_dashboard_gives_paper_statement.
Qed.

Corollary type_theory_atlas_daily_final_dashboard_gives_completion_certificate :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  apply type_theory_atlas_daily_final_dashboard_completion_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  exact (atlas_daily_final_dashboard_completion_dashboard
    type_theory_atlas_daily_final_dashboard_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage_route :
  type_theory_atlas_daily_final_dashboard_stage_route_certificate.
Proof.
  exact (atlas_daily_final_dashboard_completion_stage_route
    type_theory_atlas_daily_final_dashboard_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_automation_summary :
  type_theory_atlas_daily_automation_summary_certificate.
Proof.
  exact (atlas_daily_final_dashboard_completion_automation_summary
    type_theory_atlas_daily_final_dashboard_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_final_report :
  type_theory_atlas_daily_final_report_index.
Proof.
  exact (atlas_daily_final_dashboard_completion_final_report
    type_theory_atlas_daily_final_dashboard_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_daily_final_dashboard_completion_release_summary
    type_theory_atlas_daily_final_dashboard_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_daily_final_dashboard_completion_project_status
    type_theory_atlas_daily_final_dashboard_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_final_dashboard_completion_metatheory
    type_theory_atlas_daily_final_dashboard_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_final_dashboard_completion_paper_statement
    type_theory_atlas_daily_final_dashboard_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage1_unified_syntax
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage2_mltt
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage3_utt
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage4_tdtt_typing
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage4_tdtt_dashboard
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage5_system_embeddings
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage5_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage5_translation
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage6_metatheory
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_stage6_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_daily_final_dashboard_stage_route_stage6_paper_statement
    type_theory_atlas_daily_final_dashboard_completion_gives_stage_route).
Qed.

Record type_theory_atlas_paper_ready_completion_certificate : Prop := {
  atlas_paper_ready_completion_handle :
    type_theory_atlas_daily_final_dashboard_completion_certificate;
  atlas_paper_ready_dashboard :
    type_theory_atlas_daily_final_dashboard_certificate;
  atlas_paper_ready_stage_route :
    type_theory_atlas_daily_final_dashboard_stage_route_certificate;
  atlas_paper_ready_unified_syntax :
    type_theory_atlas_coverage;
  atlas_paper_ready_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_paper_ready_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_paper_ready_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_paper_ready_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_paper_ready_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_paper_ready_translation :
    atlas_translation_reliability_summary;
  atlas_paper_ready_metatheory :
    type_theory_atlas_main_theorem;
  atlas_paper_ready_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_paper_ready_completion_certificate_holds :
  type_theory_atlas_paper_ready_completion_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_daily_final_dashboard_completion_certificate_holds.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_dashboard.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage_route.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage1_unified_syntax.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage2_mltt.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage3_utt.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_typing.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_dashboard.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage5_system_embeddings.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage5_translation.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage6_metatheory.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage6_paper_statement.
Qed.

Corollary type_theory_atlas_daily_final_dashboard_completion_gives_paper_ready_certificate :
  type_theory_atlas_paper_ready_completion_certificate.
Proof.
  apply type_theory_atlas_paper_ready_completion_certificate_holds.
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_completion_handle :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  exact (atlas_paper_ready_completion_handle
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  exact (atlas_paper_ready_dashboard
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_stage_route :
  type_theory_atlas_daily_final_dashboard_stage_route_certificate.
Proof.
  exact (atlas_paper_ready_stage_route
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_paper_ready_unified_syntax
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_paper_ready_mltt
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_paper_ready_utt
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_paper_ready_tdtt_typing
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_paper_ready_tdtt_dashboard
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_paper_ready_system_embeddings
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_paper_ready_translation
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_metatheory
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_paper_statement
    type_theory_atlas_paper_ready_completion_certificate_holds).
Qed.

Record type_theory_atlas_paper_ready_claim_index : Prop := {
  atlas_paper_ready_claim_completion :
    type_theory_atlas_paper_ready_completion_certificate;
  atlas_paper_ready_claim_index :
    type_theory_atlas_paper_claim_index;
  atlas_paper_ready_claim_statement :
    type_theory_atlas_paper_statement;
  atlas_paper_ready_claim_final_paper_theorem :
    type_theory_atlas_final_paper_theorem;
  atlas_paper_ready_claim_contribution_summary :
    atlas_paper_contribution_summary;
  atlas_paper_ready_claim_system_comparison :
    atlas_system_comparison_matrix;
  atlas_paper_ready_claim_translation :
    atlas_translation_reliability_summary;
  atlas_paper_ready_claim_tdtt :
    atlas_tdtt_regularity_dashboard;
  atlas_paper_ready_claim_metatheory :
    type_theory_atlas_main_theorem
}.

Theorem type_theory_atlas_paper_ready_claim_index_holds :
  type_theory_atlas_paper_ready_claim_index.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_completion_certificate_holds.
  - apply type_theory_atlas_paper_claim_index_holds.
  - apply type_theory_atlas_paper_ready_completion_gives_paper_statement.
  - exact (atlas_claim_final_paper_theorem
      type_theory_atlas_paper_claim_index_holds).
  - exact (atlas_claim_contribution_summary
      type_theory_atlas_paper_claim_index_holds).
  - apply type_theory_atlas_paper_claim_gives_system_comparison.
  - apply type_theory_atlas_paper_ready_completion_gives_translation.
  - apply type_theory_atlas_paper_ready_completion_gives_tdtt_dashboard.
  - apply type_theory_atlas_paper_ready_completion_gives_metatheory.
Qed.

Corollary type_theory_atlas_paper_ready_completion_gives_claim_index :
  type_theory_atlas_paper_ready_claim_index.
Proof.
  apply type_theory_atlas_paper_ready_claim_index_holds.
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_completion :
  type_theory_atlas_paper_ready_completion_certificate.
Proof.
  exact (atlas_paper_ready_claim_completion
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_claim_index :
  type_theory_atlas_paper_claim_index.
Proof.
  exact (atlas_paper_ready_claim_index
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_claim_statement
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_final_paper_theorem :
  type_theory_atlas_final_paper_theorem.
Proof.
  exact (atlas_paper_ready_claim_final_paper_theorem
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_contribution_summary :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_paper_ready_claim_contribution_summary
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_system_comparison :
  atlas_system_comparison_matrix.
Proof.
  exact (atlas_paper_ready_claim_system_comparison
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_paper_ready_claim_translation
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_tdtt :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_paper_ready_claim_tdtt
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_claim_metatheory
    type_theory_atlas_paper_ready_claim_index_holds).
Qed.

Record type_theory_atlas_paper_ready_abstract_certificate : Prop := {
  atlas_paper_ready_abstract_claim_index :
    type_theory_atlas_paper_ready_claim_index;
  atlas_paper_ready_abstract_completion :
    type_theory_atlas_paper_ready_completion_certificate;
  atlas_paper_ready_abstract_unified_framework :
    type_theory_atlas_coverage;
  atlas_paper_ready_abstract_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_paper_ready_abstract_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_paper_ready_abstract_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_paper_ready_abstract_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_paper_ready_abstract_translation :
    atlas_translation_reliability_summary;
  atlas_paper_ready_abstract_metatheory :
    type_theory_atlas_main_theorem;
  atlas_paper_ready_abstract_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_paper_ready_abstract_certificate_holds :
  type_theory_atlas_paper_ready_abstract_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_claim_index_holds.
  - apply type_theory_atlas_paper_ready_claim_gives_completion.
  - apply type_theory_atlas_paper_ready_completion_gives_unified_syntax.
  - apply type_theory_atlas_paper_ready_completion_gives_mltt.
  - apply type_theory_atlas_paper_ready_completion_gives_utt.
  - apply type_theory_atlas_paper_ready_completion_gives_tdtt_typing.
  - apply type_theory_atlas_paper_ready_claim_gives_tdtt.
  - apply type_theory_atlas_paper_ready_claim_gives_translation.
  - apply type_theory_atlas_paper_ready_claim_gives_metatheory.
  - apply type_theory_atlas_paper_ready_claim_gives_statement.
Qed.

Corollary type_theory_atlas_paper_ready_claim_gives_abstract_certificate :
  type_theory_atlas_paper_ready_abstract_certificate.
Proof.
  apply type_theory_atlas_paper_ready_abstract_certificate_holds.
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_claim_index :
  type_theory_atlas_paper_ready_claim_index.
Proof.
  exact (atlas_paper_ready_abstract_claim_index
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_completion :
  type_theory_atlas_paper_ready_completion_certificate.
Proof.
  exact (atlas_paper_ready_abstract_completion
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_unified_framework :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_paper_ready_abstract_unified_framework
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_paper_ready_abstract_mltt
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_paper_ready_abstract_utt
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_paper_ready_abstract_tdtt_typing
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_paper_ready_abstract_tdtt_dashboard
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_translation :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_paper_ready_abstract_translation
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_abstract_metatheory
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_abstract_paper_statement
    type_theory_atlas_paper_ready_abstract_certificate_holds).
Qed.

Record type_theory_atlas_paper_ready_four_sentence_index : Prop := {
  atlas_paper_ready_sentence_unified_framework :
    type_theory_atlas_coverage;
  atlas_paper_ready_sentence_three_systems :
    (forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true) /\
    (forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true) /\
    (forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true);
  atlas_paper_ready_sentence_translations :
    atlas_translation_reliability_summary;
  atlas_paper_ready_sentence_metatheory :
    type_theory_atlas_main_theorem;
  atlas_paper_ready_sentence_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_paper_ready_four_sentence_index_holds :
  type_theory_atlas_paper_ready_four_sentence_index.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_abstract_gives_unified_framework.
  - split.
    + apply type_theory_atlas_paper_ready_abstract_gives_mltt.
    + split.
      * apply type_theory_atlas_paper_ready_abstract_gives_utt.
      * apply type_theory_atlas_paper_ready_abstract_gives_tdtt_typing.
  - apply type_theory_atlas_paper_ready_abstract_gives_translation.
  - apply type_theory_atlas_paper_ready_abstract_gives_metatheory.
  - apply type_theory_atlas_paper_ready_abstract_gives_paper_statement.
Qed.

Corollary type_theory_atlas_paper_ready_abstract_gives_four_sentence_index :
  type_theory_atlas_paper_ready_four_sentence_index.
Proof.
  apply type_theory_atlas_paper_ready_four_sentence_index_holds.
Qed.

Corollary type_theory_atlas_paper_ready_four_sentence_gives_unified_framework :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_paper_ready_sentence_unified_framework
    type_theory_atlas_paper_ready_four_sentence_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_four_sentence_gives_three_systems :
  (forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true) /\
  (forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true) /\
  (forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true).
Proof.
  exact (atlas_paper_ready_sentence_three_systems
    type_theory_atlas_paper_ready_four_sentence_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_four_sentence_gives_translations :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_paper_ready_sentence_translations
    type_theory_atlas_paper_ready_four_sentence_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_four_sentence_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_sentence_metatheory
    type_theory_atlas_paper_ready_four_sentence_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_four_sentence_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_sentence_paper_statement
    type_theory_atlas_paper_ready_four_sentence_index_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_sentence_1_unified_framework :
  type_theory_atlas_coverage.
Proof.
  apply type_theory_atlas_paper_ready_four_sentence_gives_unified_framework.
Qed.

Corollary type_theory_atlas_paper_ready_abstract_sentence_2_three_systems :
  (forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true) /\
  (forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true) /\
  (forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true).
Proof.
  apply type_theory_atlas_paper_ready_four_sentence_gives_three_systems.
Qed.

Corollary type_theory_atlas_paper_ready_abstract_sentence_3_translations :
  atlas_translation_reliability_summary.
Proof.
  apply type_theory_atlas_paper_ready_four_sentence_gives_translations.
Qed.

Corollary type_theory_atlas_paper_ready_abstract_sentence_4_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  apply type_theory_atlas_paper_ready_four_sentence_gives_metatheory.
Qed.

Record type_theory_atlas_paper_ready_abstract_final_certificate : Prop := {
  atlas_paper_ready_abstract_final_four_sentence_index :
    type_theory_atlas_paper_ready_four_sentence_index;
  atlas_paper_ready_abstract_final_sentence_1 :
    type_theory_atlas_coverage;
  atlas_paper_ready_abstract_final_sentence_2 :
    (forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true) /\
    (forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true) /\
    (forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true);
  atlas_paper_ready_abstract_final_sentence_3 :
    atlas_translation_reliability_summary;
  atlas_paper_ready_abstract_final_sentence_4 :
    type_theory_atlas_main_theorem;
  atlas_paper_ready_abstract_final_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_paper_ready_abstract_final_certificate_holds :
  type_theory_atlas_paper_ready_abstract_final_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_four_sentence_index_holds.
  - apply type_theory_atlas_paper_ready_abstract_sentence_1_unified_framework.
  - apply type_theory_atlas_paper_ready_abstract_sentence_2_three_systems.
  - apply type_theory_atlas_paper_ready_abstract_sentence_3_translations.
  - apply type_theory_atlas_paper_ready_abstract_sentence_4_metatheory.
  - apply type_theory_atlas_paper_ready_four_sentence_gives_paper_statement.
Qed.

Corollary type_theory_atlas_paper_ready_four_sentence_gives_abstract_final_certificate :
  type_theory_atlas_paper_ready_abstract_final_certificate.
Proof.
  apply type_theory_atlas_paper_ready_abstract_final_certificate_holds.
Qed.

Corollary type_theory_atlas_paper_ready_abstract_final_gives_four_sentence_index :
  type_theory_atlas_paper_ready_four_sentence_index.
Proof.
  exact (atlas_paper_ready_abstract_final_four_sentence_index
    type_theory_atlas_paper_ready_abstract_final_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_final_gives_sentence_1 :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_paper_ready_abstract_final_sentence_1
    type_theory_atlas_paper_ready_abstract_final_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_final_gives_sentence_2 :
  (forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true) /\
  (forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true) /\
  (forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true).
Proof.
  exact (atlas_paper_ready_abstract_final_sentence_2
    type_theory_atlas_paper_ready_abstract_final_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_final_gives_sentence_3 :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_paper_ready_abstract_final_sentence_3
    type_theory_atlas_paper_ready_abstract_final_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_final_gives_sentence_4 :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_abstract_final_sentence_4
    type_theory_atlas_paper_ready_abstract_final_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_abstract_final_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_abstract_final_paper_statement
    type_theory_atlas_paper_ready_abstract_final_certificate_holds).
Qed.

Record type_theory_atlas_paper_ready_final_report_certificate : Prop := {
  atlas_paper_ready_final_report_abstract_final :
    type_theory_atlas_paper_ready_abstract_final_certificate;
  atlas_paper_ready_final_report_daily_completion :
    type_theory_atlas_daily_final_dashboard_completion_certificate;
  atlas_paper_ready_final_report_daily_report :
    type_theory_atlas_daily_final_report_index;
  atlas_paper_ready_final_report_dashboard :
    type_theory_atlas_daily_final_dashboard_certificate;
  atlas_paper_ready_final_report_stage_route :
    type_theory_atlas_daily_final_dashboard_stage_route_certificate;
  atlas_paper_ready_final_report_four_sentence_index :
    type_theory_atlas_paper_ready_four_sentence_index;
  atlas_paper_ready_final_report_metatheory :
    type_theory_atlas_main_theorem;
  atlas_paper_ready_final_report_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_paper_ready_final_report_certificate_holds :
  type_theory_atlas_paper_ready_final_report_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_abstract_final_certificate_holds.
  - apply type_theory_atlas_daily_final_dashboard_completion_certificate_holds.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_final_report.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_dashboard.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage_route.
  - apply type_theory_atlas_paper_ready_abstract_final_gives_four_sentence_index.
  - apply type_theory_atlas_paper_ready_abstract_final_gives_sentence_4.
  - apply type_theory_atlas_paper_ready_abstract_final_gives_paper_statement.
Qed.

Corollary type_theory_atlas_paper_ready_abstract_final_gives_final_report_certificate :
  type_theory_atlas_paper_ready_final_report_certificate.
Proof.
  apply type_theory_atlas_paper_ready_final_report_certificate_holds.
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_abstract_final :
  type_theory_atlas_paper_ready_abstract_final_certificate.
Proof.
  exact (atlas_paper_ready_final_report_abstract_final
    type_theory_atlas_paper_ready_final_report_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_daily_completion :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  exact (atlas_paper_ready_final_report_daily_completion
    type_theory_atlas_paper_ready_final_report_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_daily_report :
  type_theory_atlas_daily_final_report_index.
Proof.
  exact (atlas_paper_ready_final_report_daily_report
    type_theory_atlas_paper_ready_final_report_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  exact (atlas_paper_ready_final_report_dashboard
    type_theory_atlas_paper_ready_final_report_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_stage_route :
  type_theory_atlas_daily_final_dashboard_stage_route_certificate.
Proof.
  exact (atlas_paper_ready_final_report_stage_route
    type_theory_atlas_paper_ready_final_report_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_four_sentence_index :
  type_theory_atlas_paper_ready_four_sentence_index.
Proof.
  exact (atlas_paper_ready_final_report_four_sentence_index
    type_theory_atlas_paper_ready_final_report_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_final_report_metatheory
    type_theory_atlas_paper_ready_final_report_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_final_report_paper_statement
    type_theory_atlas_paper_ready_final_report_certificate_holds).
Qed.

Record type_theory_atlas_paper_ready_delivery_certificate : Prop := {
  atlas_paper_ready_delivery_final_report :
    type_theory_atlas_paper_ready_final_report_certificate;
  atlas_paper_ready_delivery_daily_completion :
    type_theory_atlas_daily_final_dashboard_completion_certificate;
  atlas_paper_ready_delivery_release_summary :
    type_theory_atlas_release_summary;
  atlas_paper_ready_delivery_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_paper_ready_delivery_dashboard :
    type_theory_atlas_daily_final_dashboard_certificate;
  atlas_paper_ready_delivery_abstract_final :
    type_theory_atlas_paper_ready_abstract_final_certificate;
  atlas_paper_ready_delivery_four_sentence_index :
    type_theory_atlas_paper_ready_four_sentence_index;
  atlas_paper_ready_delivery_metatheory :
    type_theory_atlas_main_theorem;
  atlas_paper_ready_delivery_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_paper_ready_delivery_certificate_holds :
  type_theory_atlas_paper_ready_delivery_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_final_report_certificate_holds.
  - apply type_theory_atlas_paper_ready_final_report_gives_daily_completion.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_release_summary.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_project_status.
  - apply type_theory_atlas_paper_ready_final_report_gives_dashboard.
  - apply type_theory_atlas_paper_ready_final_report_gives_abstract_final.
  - apply type_theory_atlas_paper_ready_final_report_gives_four_sentence_index.
  - apply type_theory_atlas_paper_ready_final_report_gives_metatheory.
  - apply type_theory_atlas_paper_ready_final_report_gives_paper_statement.
Qed.

Corollary type_theory_atlas_paper_ready_final_report_gives_delivery_certificate :
  type_theory_atlas_paper_ready_delivery_certificate.
Proof.
  apply type_theory_atlas_paper_ready_delivery_certificate_holds.
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_final_report :
  type_theory_atlas_paper_ready_final_report_certificate.
Proof.
  exact (atlas_paper_ready_delivery_final_report
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_daily_completion :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  exact (atlas_paper_ready_delivery_daily_completion
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_paper_ready_delivery_release_summary
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_paper_ready_delivery_project_status
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  exact (atlas_paper_ready_delivery_dashboard
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_abstract_final :
  type_theory_atlas_paper_ready_abstract_final_certificate.
Proof.
  exact (atlas_paper_ready_delivery_abstract_final
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_four_sentence_index :
  type_theory_atlas_paper_ready_four_sentence_index.
Proof.
  exact (atlas_paper_ready_delivery_four_sentence_index
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_delivery_metatheory
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_delivery_paper_statement
    type_theory_atlas_paper_ready_delivery_certificate_holds).
Qed.

Record type_theory_atlas_paper_ready_project_cover_certificate : Prop := {
  atlas_paper_ready_project_cover_delivery :
    type_theory_atlas_paper_ready_delivery_certificate;
  atlas_paper_ready_project_cover_paper_statement :
    type_theory_atlas_paper_statement;
  atlas_paper_ready_project_cover_core_contribution :
    atlas_paper_contribution_summary;
  atlas_paper_ready_project_cover_abstract_final :
    type_theory_atlas_paper_ready_abstract_final_certificate;
  atlas_paper_ready_project_cover_four_sentence_index :
    type_theory_atlas_paper_ready_four_sentence_index;
  atlas_paper_ready_project_cover_release_summary :
    type_theory_atlas_release_summary;
  atlas_paper_ready_project_cover_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_paper_ready_project_cover_daily_completion :
    type_theory_atlas_daily_final_dashboard_completion_certificate;
  atlas_paper_ready_project_cover_validation_dashboard :
    type_theory_atlas_daily_final_dashboard_certificate;
  atlas_paper_ready_project_cover_metatheory :
    type_theory_atlas_main_theorem
}.

Theorem type_theory_atlas_paper_ready_project_cover_certificate_holds :
  type_theory_atlas_paper_ready_project_cover_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_delivery_certificate_holds.
  - apply type_theory_atlas_paper_ready_delivery_gives_paper_statement.
  - apply type_theory_atlas_paper_ready_claim_gives_contribution_summary.
  - apply type_theory_atlas_paper_ready_delivery_gives_abstract_final.
  - apply type_theory_atlas_paper_ready_delivery_gives_four_sentence_index.
  - apply type_theory_atlas_paper_ready_delivery_gives_release_summary.
  - apply type_theory_atlas_paper_ready_delivery_gives_project_status.
  - apply type_theory_atlas_paper_ready_delivery_gives_daily_completion.
  - apply type_theory_atlas_paper_ready_delivery_gives_dashboard.
  - apply type_theory_atlas_paper_ready_delivery_gives_metatheory.
Qed.

Corollary type_theory_atlas_paper_ready_delivery_gives_project_cover_certificate :
  type_theory_atlas_paper_ready_project_cover_certificate.
Proof.
  apply type_theory_atlas_paper_ready_project_cover_certificate_holds.
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_delivery :
  type_theory_atlas_paper_ready_delivery_certificate.
Proof.
  exact (atlas_paper_ready_project_cover_delivery
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_project_cover_paper_statement
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_core_contribution :
  atlas_paper_contribution_summary.
Proof.
  exact (atlas_paper_ready_project_cover_core_contribution
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_abstract_final :
  type_theory_atlas_paper_ready_abstract_final_certificate.
Proof.
  exact (atlas_paper_ready_project_cover_abstract_final
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_four_sentence_index :
  type_theory_atlas_paper_ready_four_sentence_index.
Proof.
  exact (atlas_paper_ready_project_cover_four_sentence_index
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_paper_ready_project_cover_release_summary
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_paper_ready_project_cover_project_status
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_daily_completion :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  exact (atlas_paper_ready_project_cover_daily_completion
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_validation_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  exact (atlas_paper_ready_project_cover_validation_dashboard
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_project_cover_metatheory
    type_theory_atlas_paper_ready_project_cover_certificate_holds).
Qed.

Record type_theory_atlas_paper_ready_automation_archive_certificate : Prop := {
  atlas_paper_ready_archive_project_cover :
    type_theory_atlas_paper_ready_project_cover_certificate;
  atlas_paper_ready_archive_delivery :
    type_theory_atlas_paper_ready_delivery_certificate;
  atlas_paper_ready_archive_daily_completion :
    type_theory_atlas_daily_final_dashboard_completion_certificate;
  atlas_paper_ready_archive_automation_summary :
    type_theory_atlas_daily_automation_summary_certificate;
  atlas_paper_ready_archive_final_dashboard :
    type_theory_atlas_daily_final_dashboard_certificate;
  atlas_paper_ready_archive_release_summary :
    type_theory_atlas_release_summary;
  atlas_paper_ready_archive_project_status :
    type_theory_atlas_project_status_certificate;
  atlas_paper_ready_archive_stage_route :
    type_theory_atlas_daily_final_dashboard_stage_route_certificate;
  atlas_paper_ready_archive_metatheory :
    type_theory_atlas_main_theorem;
  atlas_paper_ready_archive_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_paper_ready_automation_archive_certificate_holds :
  type_theory_atlas_paper_ready_automation_archive_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_project_cover_certificate_holds.
  - apply type_theory_atlas_paper_ready_project_cover_gives_delivery.
  - apply type_theory_atlas_paper_ready_project_cover_gives_daily_completion.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_automation_summary.
  - apply type_theory_atlas_paper_ready_project_cover_gives_validation_dashboard.
  - apply type_theory_atlas_paper_ready_project_cover_gives_release_summary.
  - apply type_theory_atlas_paper_ready_project_cover_gives_project_status.
  - apply type_theory_atlas_daily_final_dashboard_completion_gives_stage_route.
  - apply type_theory_atlas_paper_ready_project_cover_gives_metatheory.
  - apply type_theory_atlas_paper_ready_project_cover_gives_paper_statement.
Qed.

Corollary type_theory_atlas_paper_ready_project_cover_gives_automation_archive_certificate :
  type_theory_atlas_paper_ready_automation_archive_certificate.
Proof.
  apply type_theory_atlas_paper_ready_automation_archive_certificate_holds.
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_project_cover :
  type_theory_atlas_paper_ready_project_cover_certificate.
Proof.
  exact (atlas_paper_ready_archive_project_cover
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_delivery :
  type_theory_atlas_paper_ready_delivery_certificate.
Proof.
  exact (atlas_paper_ready_archive_delivery
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_daily_completion :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  exact (atlas_paper_ready_archive_daily_completion
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_automation_summary :
  type_theory_atlas_daily_automation_summary_certificate.
Proof.
  exact (atlas_paper_ready_archive_automation_summary
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_final_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  exact (atlas_paper_ready_archive_final_dashboard
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_release_summary :
  type_theory_atlas_release_summary.
Proof.
  exact (atlas_paper_ready_archive_release_summary
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_project_status :
  type_theory_atlas_project_status_certificate.
Proof.
  exact (atlas_paper_ready_archive_project_status
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_stage_route :
  type_theory_atlas_daily_final_dashboard_stage_route_certificate.
Proof.
  exact (atlas_paper_ready_archive_stage_route
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_archive_metatheory
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_archive_paper_statement
    type_theory_atlas_paper_ready_automation_archive_certificate_holds).
Qed.

Record type_theory_atlas_paper_ready_automation_complete_certificate : Prop := {
  atlas_paper_ready_complete_archive :
    type_theory_atlas_paper_ready_automation_archive_certificate;
  atlas_paper_ready_complete_project_cover :
    type_theory_atlas_paper_ready_project_cover_certificate;
  atlas_paper_ready_complete_delivery :
    type_theory_atlas_paper_ready_delivery_certificate;
  atlas_paper_ready_complete_four_sentence_index :
    type_theory_atlas_paper_ready_four_sentence_index;
  atlas_paper_ready_complete_daily_completion :
    type_theory_atlas_daily_final_dashboard_completion_certificate;
  atlas_paper_ready_complete_automation_summary :
    type_theory_atlas_daily_automation_summary_certificate;
  atlas_paper_ready_complete_final_dashboard :
    type_theory_atlas_daily_final_dashboard_certificate;
  atlas_paper_ready_complete_stage_route :
    type_theory_atlas_daily_final_dashboard_stage_route_certificate;
  atlas_paper_ready_complete_metatheory :
    type_theory_atlas_main_theorem;
  atlas_paper_ready_complete_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_paper_ready_automation_complete_certificate_holds :
  type_theory_atlas_paper_ready_automation_complete_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_paper_ready_automation_archive_certificate_holds.
  - apply type_theory_atlas_paper_ready_archive_gives_project_cover.
  - apply type_theory_atlas_paper_ready_archive_gives_delivery.
  - apply type_theory_atlas_paper_ready_project_cover_gives_four_sentence_index.
  - apply type_theory_atlas_paper_ready_archive_gives_daily_completion.
  - apply type_theory_atlas_paper_ready_archive_gives_automation_summary.
  - apply type_theory_atlas_paper_ready_archive_gives_final_dashboard.
  - apply type_theory_atlas_paper_ready_archive_gives_stage_route.
  - apply type_theory_atlas_paper_ready_archive_gives_metatheory.
  - apply type_theory_atlas_paper_ready_archive_gives_paper_statement.
Qed.

Corollary type_theory_atlas_paper_ready_archive_gives_automation_complete_certificate :
  type_theory_atlas_paper_ready_automation_complete_certificate.
Proof.
  apply type_theory_atlas_paper_ready_automation_complete_certificate_holds.
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_archive :
  type_theory_atlas_paper_ready_automation_archive_certificate.
Proof.
  exact (atlas_paper_ready_complete_archive
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_project_cover :
  type_theory_atlas_paper_ready_project_cover_certificate.
Proof.
  exact (atlas_paper_ready_complete_project_cover
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_delivery :
  type_theory_atlas_paper_ready_delivery_certificate.
Proof.
  exact (atlas_paper_ready_complete_delivery
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_four_sentence_index :
  type_theory_atlas_paper_ready_four_sentence_index.
Proof.
  exact (atlas_paper_ready_complete_four_sentence_index
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_daily_completion :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  exact (atlas_paper_ready_complete_daily_completion
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_automation_summary :
  type_theory_atlas_daily_automation_summary_certificate.
Proof.
  exact (atlas_paper_ready_complete_automation_summary
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_final_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  exact (atlas_paper_ready_complete_final_dashboard
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_stage_route :
  type_theory_atlas_daily_final_dashboard_stage_route_certificate.
Proof.
  exact (atlas_paper_ready_complete_stage_route
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_paper_ready_complete_metatheory
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_paper_ready_complete_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_paper_ready_complete_paper_statement
    type_theory_atlas_paper_ready_automation_complete_certificate_holds).
Qed.

Definition type_theory_atlas_public_entry : Prop :=
  type_theory_atlas_paper_ready_automation_complete_certificate.

Theorem type_theory_atlas_public_entry_holds :
  type_theory_atlas_public_entry.
Proof.
  apply type_theory_atlas_paper_ready_automation_complete_certificate_holds.
Qed.

Corollary type_theory_atlas_public_entry_gives_paper_ready_complete :
  type_theory_atlas_paper_ready_automation_complete_certificate.
Proof.
  apply type_theory_atlas_public_entry_holds.
Qed.

Corollary type_theory_atlas_public_entry_gives_daily_completion :
  type_theory_atlas_daily_final_dashboard_completion_certificate.
Proof.
  apply type_theory_atlas_paper_ready_complete_gives_daily_completion.
Qed.

Corollary type_theory_atlas_public_entry_gives_automation_summary :
  type_theory_atlas_daily_automation_summary_certificate.
Proof.
  apply type_theory_atlas_paper_ready_complete_gives_automation_summary.
Qed.

Corollary type_theory_atlas_public_entry_gives_final_dashboard :
  type_theory_atlas_daily_final_dashboard_certificate.
Proof.
  apply type_theory_atlas_paper_ready_complete_gives_final_dashboard.
Qed.

Corollary type_theory_atlas_public_entry_gives_stage_route :
  type_theory_atlas_daily_final_dashboard_stage_route_certificate.
Proof.
  apply type_theory_atlas_paper_ready_complete_gives_stage_route.
Qed.

Corollary type_theory_atlas_public_entry_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  apply type_theory_atlas_daily_final_dashboard_completion_gives_stage1_unified_syntax.
Qed.

Corollary type_theory_atlas_public_entry_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  apply type_theory_atlas_daily_final_dashboard_completion_gives_stage2_mltt.
Qed.

Corollary type_theory_atlas_public_entry_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  apply type_theory_atlas_daily_final_dashboard_completion_gives_stage3_utt.
Qed.

Corollary type_theory_atlas_public_entry_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  apply type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_typing.
Qed.

Corollary type_theory_atlas_public_entry_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  apply type_theory_atlas_daily_final_dashboard_completion_gives_stage4_tdtt_dashboard.
Qed.

Corollary type_theory_atlas_public_entry_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  apply type_theory_atlas_daily_final_dashboard_completion_gives_stage5_system_embeddings.
Qed.

Corollary type_theory_atlas_public_entry_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  apply type_theory_atlas_daily_final_dashboard_completion_gives_stage5_translation.
Qed.

Corollary type_theory_atlas_public_entry_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  apply type_theory_atlas_paper_ready_complete_gives_metatheory.
Qed.

Corollary type_theory_atlas_public_entry_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  apply type_theory_atlas_paper_ready_complete_gives_paper_statement.
Qed.

Record type_theory_atlas_public_route_certificate : Prop := {
  atlas_public_route_entry :
    type_theory_atlas_public_entry;
  atlas_public_route_unified_syntax :
    type_theory_atlas_coverage;
  atlas_public_route_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_public_route_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_public_route_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_public_route_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_public_route_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_public_route_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_public_route_metatheory :
    type_theory_atlas_main_theorem;
  atlas_public_route_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_public_route_certificate_holds :
  type_theory_atlas_public_route_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_public_entry_holds.
  - apply type_theory_atlas_public_entry_gives_unified_syntax.
  - apply type_theory_atlas_public_entry_gives_mltt.
  - apply type_theory_atlas_public_entry_gives_utt.
  - apply type_theory_atlas_public_entry_gives_tdtt_typing.
  - apply type_theory_atlas_public_entry_gives_tdtt_dashboard.
  - apply type_theory_atlas_public_entry_gives_system_embeddings.
  - apply type_theory_atlas_public_entry_gives_translation_reliability.
  - apply type_theory_atlas_public_entry_gives_main_theorem.
  - apply type_theory_atlas_public_entry_gives_paper_statement.
Qed.

Corollary type_theory_atlas_public_entry_gives_route_certificate :
  type_theory_atlas_public_route_certificate.
Proof.
  apply type_theory_atlas_public_route_certificate_holds.
Qed.

Corollary type_theory_atlas_public_route_gives_entry :
  type_theory_atlas_public_entry.
Proof.
  exact (atlas_public_route_entry
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_route_unified_syntax
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_route_mltt
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_route_utt
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_route_tdtt_typing
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_route_tdtt_dashboard
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_route_system_embeddings
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_route_translation_reliability
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_public_route_metatheory
    type_theory_atlas_public_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_route_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_public_route_paper_statement
    type_theory_atlas_public_route_certificate_holds).
Qed.

Definition type_theory_atlas_public_theorem : Prop :=
  type_theory_atlas_public_route_certificate.

Theorem type_theory_atlas_public_theorem_holds :
  type_theory_atlas_public_theorem.
Proof.
  apply type_theory_atlas_public_route_certificate_holds.
Qed.

Corollary type_theory_atlas_public_theorem_gives_route_certificate :
  type_theory_atlas_public_route_certificate.
Proof.
  apply type_theory_atlas_public_theorem_holds.
Qed.

Corollary type_theory_atlas_public_theorem_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_route_unified_syntax
    type_theory_atlas_public_theorem_holds).
Qed.

Corollary type_theory_atlas_public_theorem_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_route_mltt
    type_theory_atlas_public_theorem_holds).
Qed.

Corollary type_theory_atlas_public_theorem_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_route_utt
    type_theory_atlas_public_theorem_holds).
Qed.

Corollary type_theory_atlas_public_theorem_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_route_tdtt_typing
    type_theory_atlas_public_theorem_holds).
Qed.

Corollary type_theory_atlas_public_theorem_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_route_tdtt_dashboard
    type_theory_atlas_public_theorem_holds).
Qed.

Corollary type_theory_atlas_public_theorem_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_route_system_embeddings
    type_theory_atlas_public_theorem_holds).
Qed.

Corollary type_theory_atlas_public_theorem_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_route_translation_reliability
    type_theory_atlas_public_theorem_holds).
Qed.

Corollary type_theory_atlas_public_theorem_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  apply type_theory_atlas_public_route_gives_main_theorem.
Qed.

Corollary type_theory_atlas_public_theorem_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  apply type_theory_atlas_public_route_gives_paper_statement.
Qed.

Record type_theory_atlas_public_summary_certificate : Prop := {
  atlas_public_summary_theorem :
    type_theory_atlas_public_theorem;
  atlas_public_summary_route_certificate :
    type_theory_atlas_public_route_certificate;
  atlas_public_summary_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_public_summary_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_public_summary_certificate_holds :
  type_theory_atlas_public_summary_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_public_theorem_holds.
  - apply type_theory_atlas_public_theorem_gives_route_certificate.
  - apply type_theory_atlas_public_theorem_gives_main_theorem.
  - apply type_theory_atlas_public_theorem_gives_paper_statement.
Qed.

Corollary type_theory_atlas_public_theorem_gives_summary_certificate :
  type_theory_atlas_public_summary_certificate.
Proof.
  apply type_theory_atlas_public_summary_certificate_holds.
Qed.

Corollary type_theory_atlas_public_summary_gives_public_theorem :
  type_theory_atlas_public_theorem.
Proof.
  exact (atlas_public_summary_theorem
    type_theory_atlas_public_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_public_summary_gives_route_certificate :
  type_theory_atlas_public_route_certificate.
Proof.
  exact (atlas_public_summary_route_certificate
    type_theory_atlas_public_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_public_summary_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_route_unified_syntax
    (atlas_public_summary_route_certificate
      type_theory_atlas_public_summary_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_summary_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_route_mltt
    (atlas_public_summary_route_certificate
      type_theory_atlas_public_summary_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_summary_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_route_utt
    (atlas_public_summary_route_certificate
      type_theory_atlas_public_summary_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_summary_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_route_tdtt_typing
    (atlas_public_summary_route_certificate
      type_theory_atlas_public_summary_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_summary_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_route_tdtt_dashboard
    (atlas_public_summary_route_certificate
      type_theory_atlas_public_summary_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_summary_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_route_system_embeddings
    (atlas_public_summary_route_certificate
      type_theory_atlas_public_summary_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_summary_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_route_translation_reliability
    (atlas_public_summary_route_certificate
      type_theory_atlas_public_summary_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_summary_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_public_summary_main_theorem
    type_theory_atlas_public_summary_certificate_holds).
Qed.

Corollary type_theory_atlas_public_summary_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_public_summary_paper_statement
    type_theory_atlas_public_summary_certificate_holds).
Qed.

Record type_theory_atlas_public_delivery_certificate : Prop := {
  atlas_public_delivery_summary :
    type_theory_atlas_public_summary_certificate;
  atlas_public_delivery_theorem :
    type_theory_atlas_public_theorem;
  atlas_public_delivery_route_certificate :
    type_theory_atlas_public_route_certificate;
  atlas_public_delivery_unified_syntax :
    type_theory_atlas_coverage;
  atlas_public_delivery_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_public_delivery_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_public_delivery_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_public_delivery_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_public_delivery_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_public_delivery_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_public_delivery_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_public_delivery_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_public_delivery_certificate_holds :
  type_theory_atlas_public_delivery_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_public_summary_certificate_holds.
  - apply type_theory_atlas_public_summary_gives_public_theorem.
  - apply type_theory_atlas_public_summary_gives_route_certificate.
  - apply type_theory_atlas_public_summary_gives_unified_syntax.
  - apply type_theory_atlas_public_summary_gives_mltt.
  - apply type_theory_atlas_public_summary_gives_utt.
  - apply type_theory_atlas_public_summary_gives_tdtt_typing.
  - apply type_theory_atlas_public_summary_gives_tdtt_dashboard.
  - apply type_theory_atlas_public_summary_gives_system_embeddings.
  - apply type_theory_atlas_public_summary_gives_translation_reliability.
  - apply type_theory_atlas_public_summary_gives_main_theorem.
  - apply type_theory_atlas_public_summary_gives_paper_statement.
Qed.

Corollary type_theory_atlas_public_summary_gives_delivery_certificate :
  type_theory_atlas_public_delivery_certificate.
Proof.
  apply type_theory_atlas_public_delivery_certificate_holds.
Qed.

Corollary type_theory_atlas_public_delivery_gives_summary :
  type_theory_atlas_public_summary_certificate.
Proof.
  exact (atlas_public_delivery_summary
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_public_theorem :
  type_theory_atlas_public_theorem.
Proof.
  exact (atlas_public_delivery_theorem
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_route_certificate :
  type_theory_atlas_public_route_certificate.
Proof.
  exact (atlas_public_delivery_route_certificate
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_delivery_unified_syntax
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_delivery_mltt
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_delivery_utt
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_delivery_tdtt_typing
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_delivery_tdtt_dashboard
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_delivery_system_embeddings
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_delivery_translation_reliability
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_public_delivery_main_theorem
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Corollary type_theory_atlas_public_delivery_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_public_delivery_paper_statement
    type_theory_atlas_public_delivery_certificate_holds).
Qed.

Record type_theory_atlas_public_final_certificate : Prop := {
  atlas_public_final_delivery :
    type_theory_atlas_public_delivery_certificate;
  atlas_public_final_summary :
    type_theory_atlas_public_summary_certificate;
  atlas_public_final_theorem :
    type_theory_atlas_public_theorem;
  atlas_public_final_route_certificate :
    type_theory_atlas_public_route_certificate;
  atlas_public_final_entry :
    type_theory_atlas_public_entry;
  atlas_public_final_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_public_final_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_public_final_certificate_holds :
  type_theory_atlas_public_final_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_public_delivery_certificate_holds.
  - apply type_theory_atlas_public_delivery_gives_summary.
  - apply type_theory_atlas_public_delivery_gives_public_theorem.
  - apply type_theory_atlas_public_delivery_gives_route_certificate.
  - apply type_theory_atlas_public_route_gives_entry.
  - apply type_theory_atlas_public_delivery_gives_main_theorem.
  - apply type_theory_atlas_public_delivery_gives_paper_statement.
Qed.

Corollary type_theory_atlas_public_delivery_gives_final_certificate :
  type_theory_atlas_public_final_certificate.
Proof.
  apply type_theory_atlas_public_final_certificate_holds.
Qed.

Corollary type_theory_atlas_public_final_gives_delivery :
  type_theory_atlas_public_delivery_certificate.
Proof.
  exact (atlas_public_final_delivery
    type_theory_atlas_public_final_certificate_holds).
Qed.

Corollary type_theory_atlas_public_final_gives_summary :
  type_theory_atlas_public_summary_certificate.
Proof.
  exact (atlas_public_final_summary
    type_theory_atlas_public_final_certificate_holds).
Qed.

Corollary type_theory_atlas_public_final_gives_public_theorem :
  type_theory_atlas_public_theorem.
Proof.
  exact (atlas_public_final_theorem
    type_theory_atlas_public_final_certificate_holds).
Qed.

Corollary type_theory_atlas_public_final_gives_route_certificate :
  type_theory_atlas_public_route_certificate.
Proof.
  exact (atlas_public_final_route_certificate
    type_theory_atlas_public_final_certificate_holds).
Qed.

Corollary type_theory_atlas_public_final_gives_entry :
  type_theory_atlas_public_entry.
Proof.
  exact (atlas_public_final_entry
    type_theory_atlas_public_final_certificate_holds).
Qed.

Corollary type_theory_atlas_public_final_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_delivery_unified_syntax
    (atlas_public_final_delivery
      type_theory_atlas_public_final_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_final_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_delivery_mltt
    (atlas_public_final_delivery
      type_theory_atlas_public_final_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_final_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_delivery_utt
    (atlas_public_final_delivery
      type_theory_atlas_public_final_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_final_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_delivery_tdtt_typing
    (atlas_public_final_delivery
      type_theory_atlas_public_final_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_final_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_delivery_tdtt_dashboard
    (atlas_public_final_delivery
      type_theory_atlas_public_final_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_final_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_delivery_system_embeddings
    (atlas_public_final_delivery
      type_theory_atlas_public_final_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_final_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_delivery_translation_reliability
    (atlas_public_final_delivery
      type_theory_atlas_public_final_certificate_holds)).
Qed.

Corollary type_theory_atlas_public_final_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_public_final_main_theorem
    type_theory_atlas_public_final_certificate_holds).
Qed.

Corollary type_theory_atlas_public_final_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_public_final_paper_statement
    type_theory_atlas_public_final_certificate_holds).
Qed.

Definition type_theory_atlas_final_public_theorem : Prop :=
  type_theory_atlas_public_final_certificate.

Theorem type_theory_atlas_final_public_theorem_holds :
  type_theory_atlas_final_public_theorem.
Proof.
  apply type_theory_atlas_public_final_certificate_holds.
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_final_certificate :
  type_theory_atlas_public_final_certificate.
Proof.
  apply type_theory_atlas_final_public_theorem_holds.
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_delivery_unified_syntax
    (atlas_public_final_delivery
      type_theory_atlas_final_public_theorem_holds)).
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_delivery_mltt
    (atlas_public_final_delivery
      type_theory_atlas_final_public_theorem_holds)).
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_delivery_utt
    (atlas_public_final_delivery
      type_theory_atlas_final_public_theorem_holds)).
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_delivery_tdtt_typing
    (atlas_public_final_delivery
      type_theory_atlas_final_public_theorem_holds)).
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_delivery_tdtt_dashboard
    (atlas_public_final_delivery
      type_theory_atlas_final_public_theorem_holds)).
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_delivery_system_embeddings
    (atlas_public_final_delivery
      type_theory_atlas_final_public_theorem_holds)).
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_delivery_translation_reliability
    (atlas_public_final_delivery
      type_theory_atlas_final_public_theorem_holds)).
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  apply type_theory_atlas_public_final_gives_main_theorem.
Qed.

Corollary type_theory_atlas_final_public_theorem_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  apply type_theory_atlas_public_final_gives_paper_statement.
Qed.

Definition type_theory_atlas_automation_done : Prop :=
  type_theory_atlas_final_public_theorem.

Theorem type_theory_atlas_automation_done_holds :
  type_theory_atlas_automation_done.
Proof.
  apply type_theory_atlas_final_public_theorem_holds.
Qed.

Corollary type_theory_atlas_automation_done_gives_final_public_theorem :
  type_theory_atlas_final_public_theorem.
Proof.
  apply type_theory_atlas_automation_done_holds.
Qed.

Corollary type_theory_atlas_automation_done_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_unified_syntax.
Qed.

Corollary type_theory_atlas_automation_done_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_mltt.
Qed.

Corollary type_theory_atlas_automation_done_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_utt.
Qed.

Corollary type_theory_atlas_automation_done_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_tdtt_typing.
Qed.

Corollary type_theory_atlas_automation_done_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_tdtt_dashboard.
Qed.

Corollary type_theory_atlas_automation_done_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_system_embeddings.
Qed.

Corollary type_theory_atlas_automation_done_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_translation_reliability.
Qed.

Corollary type_theory_atlas_automation_done_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_main_theorem.
Qed.

Corollary type_theory_atlas_automation_done_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  apply type_theory_atlas_final_public_theorem_gives_paper_statement.
Qed.

Record type_theory_atlas_automation_done_dashboard_certificate : Prop := {
  atlas_automation_done_dashboard_done :
    type_theory_atlas_automation_done;
  atlas_automation_done_dashboard_final_public_theorem :
    type_theory_atlas_final_public_theorem;
  atlas_automation_done_dashboard_unified_syntax :
    type_theory_atlas_coverage;
  atlas_automation_done_dashboard_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_automation_done_dashboard_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_automation_done_dashboard_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_automation_done_dashboard_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_automation_done_dashboard_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_automation_done_dashboard_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_automation_done_dashboard_main_theorem :
    type_theory_atlas_main_theorem;
  atlas_automation_done_dashboard_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_automation_done_dashboard_certificate_holds :
  type_theory_atlas_automation_done_dashboard_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_automation_done_holds.
  - apply type_theory_atlas_automation_done_gives_final_public_theorem.
  - apply type_theory_atlas_automation_done_gives_unified_syntax.
  - apply type_theory_atlas_automation_done_gives_mltt.
  - apply type_theory_atlas_automation_done_gives_utt.
  - apply type_theory_atlas_automation_done_gives_tdtt_typing.
  - apply type_theory_atlas_automation_done_gives_tdtt_dashboard.
  - apply type_theory_atlas_automation_done_gives_system_embeddings.
  - apply type_theory_atlas_automation_done_gives_translation_reliability.
  - apply type_theory_atlas_automation_done_gives_main_theorem.
  - apply type_theory_atlas_automation_done_gives_paper_statement.
Qed.

Corollary type_theory_atlas_automation_done_gives_dashboard_certificate :
  type_theory_atlas_automation_done_dashboard_certificate.
Proof.
  apply type_theory_atlas_automation_done_dashboard_certificate_holds.
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_done :
  type_theory_atlas_automation_done.
Proof.
  exact (atlas_automation_done_dashboard_done
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_final_public_theorem :
  type_theory_atlas_final_public_theorem.
Proof.
  exact (atlas_automation_done_dashboard_final_public_theorem
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_automation_done_dashboard_unified_syntax
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_automation_done_dashboard_mltt
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_automation_done_dashboard_utt
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_automation_done_dashboard_tdtt_typing
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_automation_done_dashboard_tdtt_dashboard
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_automation_done_dashboard_system_embeddings
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_automation_done_dashboard_translation_reliability
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_main_theorem :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_automation_done_dashboard_main_theorem
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Corollary type_theory_atlas_automation_dashboard_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_automation_done_dashboard_paper_statement
    type_theory_atlas_automation_done_dashboard_certificate_holds).
Qed.

Definition type_theory_atlas_daily_automation_report_complete : Prop :=
  type_theory_atlas_automation_done_dashboard_certificate.

Theorem type_theory_atlas_daily_automation_report_complete_holds :
  type_theory_atlas_daily_automation_report_complete.
Proof.
  apply type_theory_atlas_automation_done_dashboard_certificate_holds.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_dashboard :
  type_theory_atlas_automation_done_dashboard_certificate.
Proof.
  apply type_theory_atlas_daily_automation_report_complete_holds.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_done :
  type_theory_atlas_automation_done.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_done.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_final_public_theorem :
  type_theory_atlas_final_public_theorem.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_final_public_theorem.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_unified_syntax.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_mltt.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_utt.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_tdtt_typing.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_tdtt_dashboard.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_system_embeddings.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage5_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_translation_reliability.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_main_theorem.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_stage6_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  apply type_theory_atlas_automation_dashboard_gives_paper_statement.
Qed.

Record type_theory_atlas_public_release_manifest : Prop := {
  atlas_public_release_manifest_daily_report :
    type_theory_atlas_daily_automation_report_complete;
  atlas_public_release_manifest_dashboard :
    type_theory_atlas_automation_done_dashboard_certificate;
  atlas_public_release_manifest_final_public_theorem :
    type_theory_atlas_final_public_theorem;
  atlas_public_release_manifest_final_certificate :
    type_theory_atlas_public_final_certificate;
  atlas_public_release_manifest_stage1_unified_syntax :
    type_theory_atlas_coverage;
  atlas_public_release_manifest_stage2_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_public_release_manifest_stage3_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_public_release_manifest_stage4_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_public_release_manifest_stage4_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_public_release_manifest_stage5_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_public_release_manifest_stage5_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_public_release_manifest_stage6_metatheory :
    type_theory_atlas_main_theorem;
  atlas_public_release_manifest_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_public_release_manifest_holds :
  type_theory_atlas_public_release_manifest.
Proof.
  constructor.
  - apply type_theory_atlas_daily_automation_report_complete_holds.
  - apply type_theory_atlas_daily_automation_report_complete_gives_dashboard.
  - apply type_theory_atlas_daily_automation_report_complete_gives_final_public_theorem.
  - apply type_theory_atlas_final_public_theorem_gives_final_certificate.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage1_unified_syntax.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage2_mltt.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage3_utt.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_typing.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage4_tdtt_dashboard.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage5_system_embeddings.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage5_translation_reliability.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage6_metatheory.
  - apply type_theory_atlas_daily_automation_report_complete_gives_stage6_paper_statement.
Qed.

Corollary type_theory_atlas_daily_automation_report_complete_gives_release_manifest :
  type_theory_atlas_public_release_manifest.
Proof.
  apply type_theory_atlas_public_release_manifest_holds.
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_daily_report :
  type_theory_atlas_daily_automation_report_complete.
Proof.
  exact (atlas_public_release_manifest_daily_report
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_dashboard :
  type_theory_atlas_automation_done_dashboard_certificate.
Proof.
  exact (atlas_public_release_manifest_dashboard
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_final_public_theorem :
  type_theory_atlas_final_public_theorem.
Proof.
  exact (atlas_public_release_manifest_final_public_theorem
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_final_certificate :
  type_theory_atlas_public_final_certificate.
Proof.
  exact (atlas_public_release_manifest_final_certificate
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_release_manifest_stage1_unified_syntax
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_release_manifest_stage2_mltt
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_release_manifest_stage3_utt
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_release_manifest_stage4_tdtt_typing
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_release_manifest_stage4_tdtt_dashboard
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_release_manifest_stage5_system_embeddings
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_stage5_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_release_manifest_stage5_translation_reliability
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_public_release_manifest_stage6_metatheory
    type_theory_atlas_public_release_manifest_holds).
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_public_release_manifest_paper_statement
    type_theory_atlas_public_release_manifest_holds).
Qed.

Record type_theory_atlas_public_release_complete_certificate : Prop := {
  atlas_public_release_complete_manifest :
    type_theory_atlas_public_release_manifest;
  atlas_public_release_complete_daily_report :
    type_theory_atlas_daily_automation_report_complete;
  atlas_public_release_complete_dashboard :
    type_theory_atlas_automation_done_dashboard_certificate;
  atlas_public_release_complete_final_public_theorem :
    type_theory_atlas_final_public_theorem;
  atlas_public_release_complete_final_certificate :
    type_theory_atlas_public_final_certificate;
  atlas_public_release_complete_stage1_unified_syntax :
    type_theory_atlas_coverage;
  atlas_public_release_complete_stage2_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_public_release_complete_stage3_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_public_release_complete_stage4_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_public_release_complete_stage4_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_public_release_complete_stage5_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_public_release_complete_stage5_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_public_release_complete_stage6_metatheory :
    type_theory_atlas_main_theorem;
  atlas_public_release_complete_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_public_release_complete_certificate_holds :
  type_theory_atlas_public_release_complete_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_public_release_manifest_holds.
  - apply type_theory_atlas_public_release_manifest_gives_daily_report.
  - apply type_theory_atlas_public_release_manifest_gives_dashboard.
  - apply type_theory_atlas_public_release_manifest_gives_final_public_theorem.
  - apply type_theory_atlas_public_release_manifest_gives_final_certificate.
  - apply type_theory_atlas_public_release_manifest_gives_stage1_unified_syntax.
  - apply type_theory_atlas_public_release_manifest_gives_stage2_mltt.
  - apply type_theory_atlas_public_release_manifest_gives_stage3_utt.
  - apply type_theory_atlas_public_release_manifest_gives_stage4_tdtt_typing.
  - apply type_theory_atlas_public_release_manifest_gives_stage4_tdtt_dashboard.
  - apply type_theory_atlas_public_release_manifest_gives_stage5_system_embeddings.
  - apply type_theory_atlas_public_release_manifest_gives_stage5_translation_reliability.
  - apply type_theory_atlas_public_release_manifest_gives_stage6_metatheory.
  - apply type_theory_atlas_public_release_manifest_gives_paper_statement.
Qed.

Corollary type_theory_atlas_public_release_manifest_gives_complete_certificate :
  type_theory_atlas_public_release_complete_certificate.
Proof.
  apply type_theory_atlas_public_release_complete_certificate_holds.
Qed.

Corollary type_theory_atlas_public_release_complete_gives_manifest :
  type_theory_atlas_public_release_manifest.
Proof.
  exact (atlas_public_release_complete_manifest
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_daily_report :
  type_theory_atlas_daily_automation_report_complete.
Proof.
  exact (atlas_public_release_complete_daily_report
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_dashboard :
  type_theory_atlas_automation_done_dashboard_certificate.
Proof.
  exact (atlas_public_release_complete_dashboard
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_final_public_theorem :
  type_theory_atlas_final_public_theorem.
Proof.
  exact (atlas_public_release_complete_final_public_theorem
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_final_certificate :
  type_theory_atlas_public_final_certificate.
Proof.
  exact (atlas_public_release_complete_final_certificate
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_release_complete_stage1_unified_syntax
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_release_complete_stage2_mltt
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_release_complete_stage3_utt
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_release_complete_stage4_tdtt_typing
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_release_complete_stage4_tdtt_dashboard
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_release_complete_stage5_system_embeddings
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_stage5_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_release_complete_stage5_translation_reliability
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_public_release_complete_stage6_metatheory
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_complete_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_public_release_complete_paper_statement
    type_theory_atlas_public_release_complete_certificate_holds).
Qed.

Definition type_theory_atlas_public_release_complete : Prop :=
  type_theory_atlas_public_release_complete_certificate.

Theorem type_theory_atlas_public_release_complete_holds :
  type_theory_atlas_public_release_complete.
Proof.
  apply type_theory_atlas_public_release_complete_certificate_holds.
Qed.

Corollary type_theory_atlas_public_release_complete_gives_certificate :
  type_theory_atlas_public_release_complete_certificate.
Proof.
  apply type_theory_atlas_public_release_complete_holds.
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_release_complete_stage1_unified_syntax
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_release_complete_stage2_mltt
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_release_complete_stage3_utt
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_release_complete_stage4_tdtt_typing
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_release_complete_stage4_tdtt_dashboard
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_release_complete_stage5_system_embeddings
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_stage5_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_release_complete_stage5_translation_reliability
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_public_release_complete_stage6_metatheory
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Corollary type_theory_atlas_public_release_complete_entry_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_public_release_complete_paper_statement
    type_theory_atlas_public_release_complete_gives_certificate).
Qed.

Record type_theory_atlas_public_release_paper_route_certificate : Prop := {
  atlas_public_release_paper_route_complete :
    type_theory_atlas_public_release_complete;
  atlas_public_release_paper_route_stage1_unified_syntax :
    type_theory_atlas_coverage;
  atlas_public_release_paper_route_stage2_mltt :
    forall gamma t a,
      has_type gamma t a ->
      supports MLTT t = true /\
      supports MLTT a = true;
  atlas_public_release_paper_route_stage3_utt :
    forall gamma t a,
      utt_has_type gamma t a ->
      supports UTT t = true /\
      supports UTT a = true;
  atlas_public_release_paper_route_stage4_tdtt_typing :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      supports TDTT t = true /\
      supports TDTT a = true;
  atlas_public_release_paper_route_stage4_tdtt_dashboard :
    atlas_tdtt_regularity_dashboard;
  atlas_public_release_paper_route_stage5_system_embeddings :
    atlas_system_embedding_regularities;
  atlas_public_release_paper_route_stage5_translation_reliability :
    atlas_translation_reliability_summary;
  atlas_public_release_paper_route_stage6_metatheory :
    type_theory_atlas_main_theorem;
  atlas_public_release_paper_route_paper_statement :
    type_theory_atlas_paper_statement
}.

Theorem type_theory_atlas_public_release_paper_route_certificate_holds :
  type_theory_atlas_public_release_paper_route_certificate.
Proof.
  constructor.
  - apply type_theory_atlas_public_release_complete_holds.
  - apply type_theory_atlas_public_release_complete_entry_gives_stage1_unified_syntax.
  - apply type_theory_atlas_public_release_complete_entry_gives_stage2_mltt.
  - apply type_theory_atlas_public_release_complete_entry_gives_stage3_utt.
  - apply type_theory_atlas_public_release_complete_entry_gives_stage4_tdtt_typing.
  - apply type_theory_atlas_public_release_complete_entry_gives_stage4_tdtt_dashboard.
  - apply type_theory_atlas_public_release_complete_entry_gives_stage5_system_embeddings.
  - apply type_theory_atlas_public_release_complete_entry_gives_stage5_translation_reliability.
  - apply type_theory_atlas_public_release_complete_entry_gives_stage6_metatheory.
  - apply type_theory_atlas_public_release_complete_entry_gives_paper_statement.
Qed.

Corollary type_theory_atlas_public_release_complete_gives_paper_route_certificate :
  type_theory_atlas_public_release_paper_route_certificate.
Proof.
  apply type_theory_atlas_public_release_paper_route_certificate_holds.
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_complete :
  type_theory_atlas_public_release_complete.
Proof.
  exact (atlas_public_release_paper_route_complete
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_stage1_unified_syntax :
  type_theory_atlas_coverage.
Proof.
  exact (atlas_public_release_paper_route_stage1_unified_syntax
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_stage2_mltt :
  forall gamma t a,
    has_type gamma t a ->
    supports MLTT t = true /\
    supports MLTT a = true.
Proof.
  exact (atlas_public_release_paper_route_stage2_mltt
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_stage3_utt :
  forall gamma t a,
    utt_has_type gamma t a ->
    supports UTT t = true /\
    supports UTT a = true.
Proof.
  exact (atlas_public_release_paper_route_stage3_utt
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_stage4_tdtt_typing :
  forall theta gamma t a,
    tdtt_has_type theta gamma t a ->
    supports TDTT t = true /\
    supports TDTT a = true.
Proof.
  exact (atlas_public_release_paper_route_stage4_tdtt_typing
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_stage4_tdtt_dashboard :
  atlas_tdtt_regularity_dashboard.
Proof.
  exact (atlas_public_release_paper_route_stage4_tdtt_dashboard
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_stage5_system_embeddings :
  atlas_system_embedding_regularities.
Proof.
  exact (atlas_public_release_paper_route_stage5_system_embeddings
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_stage5_translation_reliability :
  atlas_translation_reliability_summary.
Proof.
  exact (atlas_public_release_paper_route_stage5_translation_reliability
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_stage6_metatheory :
  type_theory_atlas_main_theorem.
Proof.
  exact (atlas_public_release_paper_route_stage6_metatheory
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.

Corollary type_theory_atlas_public_release_paper_route_gives_paper_statement :
  type_theory_atlas_paper_statement.
Proof.
  exact (atlas_public_release_paper_route_paper_statement
    type_theory_atlas_public_release_paper_route_certificate_holds).
Qed.
