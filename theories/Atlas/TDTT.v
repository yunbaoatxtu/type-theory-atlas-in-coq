(** A first Temporal Dependent Type Theory core.

    This layer is deliberately conservative.  It extends the UTT rules with
    abstract time parameters, explicit temporal indexing [tAt], a [tLater]
    type former, [tNext] introduction, and guarded fixed-point rules.  The
    indexed variants make the clock parameter explicit.  A first clock
    quantification layer adds clock products, clock abstractions, and clock
    applications.  Clock beta equality is part of the shared definitional
    equality; delayed substitutions are left for later extensions.
 *)

From Stdlib Require Import Arith.PeanoNat List.
From Atlas Require Import Syntax Ops Context DefEq UTT TemporalContext.

Import ListNotations.

Inductive tdtt_wf_context : temporal_context -> context -> Prop :=
| tdtt_wf_empty :
    forall theta,
      tdtt_wf_context theta []
| tdtt_wf_extend :
    forall theta gamma a sort,
      tdtt_wf_context theta gamma ->
      tdtt_has_type theta gamma a (utt_sort_term sort) ->
      tdtt_wf_context theta (a :: gamma)
with tdtt_has_type : temporal_context -> context -> term -> term -> Prop :=
| tdtt_ty_prop :
    forall theta gamma,
      tdtt_wf_context theta gamma ->
      tdtt_has_type theta gamma tProp (tUniverse 0)
| tdtt_ty_universe :
    forall theta gamma level,
      tdtt_wf_context theta gamma ->
      tdtt_has_type theta gamma (tUniverse level) (tUniverse (S level))
| tdtt_ty_var :
    forall theta gamma index a,
      tdtt_wf_context theta gamma ->
      lookup gamma index a ->
      tdtt_has_type theta gamma (tVar index) a
| tdtt_ty_pi :
    forall theta gamma a b domain_sort codomain_sort,
      tdtt_has_type theta gamma a (utt_sort_term domain_sort) ->
      tdtt_has_type theta (a :: gamma) b (utt_sort_term codomain_sort) ->
      tdtt_has_type theta gamma (tPi a b)
        (utt_sort_term (utt_product_sort domain_sort codomain_sort))
| tdtt_ty_lam :
    forall theta gamma a body b domain_sort codomain_sort,
      tdtt_has_type theta gamma a (utt_sort_term domain_sort) ->
      tdtt_has_type theta (a :: gamma) b (utt_sort_term codomain_sort) ->
      tdtt_has_type theta (a :: gamma) body b ->
      tdtt_has_type theta gamma (tLam body) (tPi a b)
| tdtt_ty_app :
    forall theta gamma f argument a b,
      tdtt_has_type theta gamma f (tPi a b) ->
      tdtt_has_type theta gamma argument a ->
      tdtt_has_type theta gamma (tApp f argument) (subst_term argument 0 b)
| tdtt_ty_sigma :
    forall theta gamma a b domain_sort level_b,
      tdtt_has_type theta gamma a (utt_sort_term domain_sort) ->
      tdtt_has_type theta (a :: gamma) b (tUniverse level_b) ->
      tdtt_has_type theta gamma (tSigma a b)
        (tUniverse (utt_sigma_level domain_sort level_b))
| tdtt_ty_pair :
    forall theta gamma a b first second domain_sort level_b,
      tdtt_has_type theta gamma a (utt_sort_term domain_sort) ->
      tdtt_has_type theta (a :: gamma) b (tUniverse level_b) ->
      tdtt_has_type theta gamma first a ->
      tdtt_has_type theta gamma second (subst_term first 0 b) ->
      tdtt_has_type theta gamma (tPair first second) (tSigma a b)
| tdtt_ty_fst :
    forall theta gamma pair a b,
      tdtt_has_type theta gamma pair (tSigma a b) ->
      tdtt_has_type theta gamma (tFst pair) a
| tdtt_ty_snd :
    forall theta gamma pair a b,
      tdtt_has_type theta gamma pair (tSigma a b) ->
      tdtt_has_type theta gamma (tSnd pair) (subst_term (tFst pair) 0 b)
| tdtt_ty_id :
    forall theta gamma a x y level,
      tdtt_has_type theta gamma a (tUniverse level) ->
      tdtt_has_type theta gamma x a ->
      tdtt_has_type theta gamma y a ->
      tdtt_has_type theta gamma (tId a x y) (tUniverse level)
| tdtt_ty_refl :
    forall theta gamma a x,
      tdtt_has_type theta gamma x a ->
      tdtt_has_type theta gamma (tRefl x) (tId a x x)
| tdtt_ty_conv :
    forall theta gamma t a b sort,
      tdtt_has_type theta gamma t a ->
      tdtt_has_type theta gamma b (utt_sort_term sort) ->
      defeq a b ->
      tdtt_has_type theta gamma t b
| tdtt_ty_prop_lift :
    forall theta gamma proposition level,
      tdtt_has_type theta gamma proposition tProp ->
      tdtt_has_type theta gamma proposition (tUniverse level)
| tdtt_ty_type_lift :
    forall theta gamma a lower upper,
      tdtt_has_type theta gamma a (tUniverse lower) ->
      lower <= upper ->
      tdtt_has_type theta gamma a (tUniverse upper)
| tdtt_ty_at :
    forall theta gamma a time sort,
      tdtt_has_type theta gamma a (utt_sort_term sort) ->
      temporal_wf theta time ->
      tdtt_has_type theta gamma (tAt a time) (utt_sort_term sort)
| tdtt_ty_later :
    forall theta gamma a sort,
      tdtt_has_type theta gamma a (utt_sort_term sort) ->
      tdtt_has_type theta gamma (tLater a) (utt_sort_term sort)
| tdtt_ty_next :
    forall theta gamma t a,
      tdtt_has_type theta gamma t a ->
      tdtt_has_type theta gamma (tNext t) (tLater a)
| tdtt_ty_fix :
    forall theta gamma a body sort,
      tdtt_has_type theta gamma a (utt_sort_term sort) ->
      tdtt_has_type theta (tLater a :: gamma) body (shift_term 1 0 a) ->
      tdtt_has_type theta gamma (tFix body) a
| tdtt_ty_later_at :
    forall theta gamma clock a sort,
      temporal_wf theta clock ->
      tdtt_has_type theta gamma a (utt_sort_term sort) ->
      tdtt_has_type theta gamma (tLaterAt clock a) (utt_sort_term sort)
| tdtt_ty_next_at :
    forall theta gamma clock t a,
      temporal_wf theta clock ->
      tdtt_has_type theta gamma t a ->
      tdtt_has_type theta gamma (tNextAt clock t) (tLaterAt clock a)
| tdtt_ty_fix_at :
    forall theta gamma clock a body sort,
      temporal_wf theta clock ->
      tdtt_has_type theta gamma a (utt_sort_term sort) ->
      tdtt_has_type theta (tLaterAt clock a :: gamma) body (shift_term 1 0 a) ->
      tdtt_has_type theta gamma (tFixAt clock body) a
| tdtt_ty_clock_pi :
    forall theta gamma a sort,
      tdtt_wf_context theta gamma ->
      tdtt_has_type
        (tc_extend theta)
        (shift_time_context 1 0 gamma)
        a
        (utt_sort_term sort) ->
      tdtt_has_type theta gamma (tClockPi a) (utt_sort_term sort)
| tdtt_ty_clock_lam :
    forall theta gamma body a sort,
      tdtt_wf_context theta gamma ->
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
      tdtt_has_type theta gamma (tClockLam body) (tClockPi a)
| tdtt_ty_clock_app :
    forall theta gamma f clock a,
      tdtt_has_type theta gamma f (tClockPi a) ->
      temporal_wf theta clock ->
      tdtt_has_type theta gamma (tClockApp f clock) (subst_time clock 0 a)
| tdtt_ty_delayed_subst :
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
        (subst_time clock 0 a).

Scheme tdtt_wf_context_ind' := Induction for tdtt_wf_context Sort Prop
with tdtt_has_type_ind' := Induction for tdtt_has_type Sort Prop.

Combined Scheme tdtt_typing_mutind
  from tdtt_wf_context_ind', tdtt_has_type_ind'.

Theorem utt_embeds_in_tdtt :
  forall theta,
    (forall gamma,
        utt_wf_context gamma ->
        tdtt_wf_context theta gamma) /\
    (forall gamma t a,
        utt_has_type gamma t a ->
        tdtt_has_type theta gamma t a).
Proof.
  intros theta.
  apply utt_typing_mutind
    with (P := fun gamma _ => tdtt_wf_context theta gamma)
         (P0 := fun gamma t a _ => tdtt_has_type theta gamma t a).
  - apply tdtt_wf_empty.
  - intros gamma a sort _ Hgamma _ Ha.
    apply tdtt_wf_extend with (sort := sort).
    + exact Hgamma.
    + exact Ha.
  - intros gamma _ Hgamma.
    apply tdtt_ty_prop.
    exact Hgamma.
  - intros gamma level _ Hgamma.
    apply tdtt_ty_universe.
    exact Hgamma.
  - intros gamma index a _ Hgamma Hlookup.
    apply tdtt_ty_var.
    + exact Hgamma.
    + exact Hlookup.
  - intros gamma a b domain_sort codomain_sort _ Ha _ Hb.
    apply tdtt_ty_pi with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + exact Ha.
    + exact Hb.
  - intros gamma a body b domain_sort codomain_sort _ Ha _ Hb _ Hbody.
    apply tdtt_ty_lam with
        (domain_sort := domain_sort)
        (codomain_sort := codomain_sort).
    + exact Ha.
    + exact Hb.
    + exact Hbody.
  - intros gamma f argument a b _ Hf _ Hargument.
    apply tdtt_ty_app with (a := a) (b := b).
    + exact Hf.
    + exact Hargument.
  - intros gamma a b domain_sort level_b _ Ha _ Hb.
    apply tdtt_ty_sigma with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + exact Ha.
    + exact Hb.
  - intros gamma a b first second domain_sort level_b
      _ Ha _ Hb _ Hfirst _ Hsecond.
    apply tdtt_ty_pair with
        (domain_sort := domain_sort)
        (level_b := level_b).
    + exact Ha.
    + exact Hb.
    + exact Hfirst.
    + exact Hsecond.
  - intros gamma pair a b _ Hpair.
    apply tdtt_ty_fst with (b := b).
    exact Hpair.
  - intros gamma pair a b _ Hpair.
    apply tdtt_ty_snd with (a := a) (b := b).
    exact Hpair.
  - intros gamma a x y level _ Ha _ Hx _ Hy.
    apply tdtt_ty_id with (level := level).
    + exact Ha.
    + exact Hx.
    + exact Hy.
  - intros gamma a x _ Hx.
    apply tdtt_ty_refl.
    exact Hx.
  - intros gamma t a b sort _ Ht _ Hb Heq.
    apply tdtt_ty_conv with (a := a) (sort := sort).
    + exact Ht.
    + exact Hb.
    + exact Heq.
  - intros gamma proposition level _ Hproposition.
    apply tdtt_ty_prop_lift.
    exact Hproposition.
  - intros gamma a lower upper _ Ha Hle.
    apply tdtt_ty_type_lift with (lower := lower).
    + exact Ha.
    + exact Hle.
Qed.

Corollary utt_context_embeds_in_tdtt :
  forall theta gamma,
    utt_wf_context gamma ->
    tdtt_wf_context theta gamma.
Proof.
  intros theta.
  apply utt_embeds_in_tdtt.
Qed.

Corollary utt_typing_embeds_in_tdtt :
  forall theta gamma t a,
    utt_has_type gamma t a ->
    tdtt_has_type theta gamma t a.
Proof.
  intros theta.
  apply utt_embeds_in_tdtt.
Qed.

Example tdtt_prop_at_current_time :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tAt tProp (tTimeVar 0))
    (tUniverse 0).
Proof.
  apply tdtt_ty_at with (sort := usType 0).
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
  - apply temporal_wf_var.
    apply temporal_lookup_here.
Qed.

Example tdtt_later_prop_at_current_time :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tLater (tAt tProp (tTimeVar 0)))
    (tUniverse 0).
Proof.
  apply tdtt_ty_later with (sort := usType 0).
  apply tdtt_prop_at_current_time.
Qed.

Example tdtt_next_prop :
  tdtt_has_type
    tc_empty
    []
    (tNext tProp)
    (tLater (tUniverse 0)).
Proof.
  apply tdtt_ty_next.
  apply tdtt_ty_prop.
  apply tdtt_wf_empty.
Qed.

Example tdtt_constant_guarded_fix :
  tdtt_has_type
    tc_empty
    []
    (tFix tProp)
    (tUniverse 0).
Proof.
  apply tdtt_ty_fix with (sort := usType 1).
  - apply tdtt_ty_universe.
    apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_extend with (sort := usType 1).
    + apply tdtt_wf_empty.
    + apply tdtt_ty_later with (sort := usType 1).
      apply tdtt_ty_universe.
      apply tdtt_wf_empty.
Qed.

Example tdtt_clocked_next_prop :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tNextAt (tTimeVar 0) tProp)
    (tLaterAt (tTimeVar 0) (tUniverse 0)).
Proof.
  apply tdtt_ty_next_at.
  - apply temporal_wf_var.
    apply temporal_lookup_here.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
Qed.

Example tdtt_constant_clocked_guarded_fix :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tFixAt (tTimeVar 0) tProp)
    (tUniverse 0).
Proof.
  apply tdtt_ty_fix_at with (sort := usType 1).
  - apply temporal_wf_var.
    apply temporal_lookup_here.
  - apply tdtt_ty_universe.
    apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_extend with (sort := usType 1).
    + apply tdtt_wf_empty.
    + apply tdtt_ty_later_at with (sort := usType 1).
      * apply temporal_wf_var.
        apply temporal_lookup_here.
      * apply tdtt_ty_universe.
        apply tdtt_wf_empty.
Qed.

Example tdtt_clock_polymorphic_prop :
  tdtt_has_type
    tc_empty
    []
    (tClockPi tProp)
    (tUniverse 0).
Proof.
  apply tdtt_ty_clock_pi with (sort := usType 0).
  - apply tdtt_wf_empty.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
Qed.

Example tdtt_clock_polymorphic_prop_application :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tClockApp (tClockLam tProp) (tTimeVar 0))
    (tUniverse 0).
Proof.
  change (tdtt_has_type
    (tc_extend tc_empty)
    []
    (tClockApp (tClockLam tProp) (tTimeVar 0))
    (subst_time (tTimeVar 0) 0 (tUniverse 0))).
  apply tdtt_ty_clock_app.
  - apply tdtt_ty_clock_lam with (sort := usType 1).
    + apply tdtt_wf_empty.
    + apply tdtt_ty_universe.
      apply tdtt_wf_empty.
    + apply tdtt_ty_prop.
      apply tdtt_wf_empty.
  - apply temporal_wf_var.
    apply temporal_lookup_here.
Qed.

Example tdtt_delayed_substitution_prop :
  tdtt_has_type
    (tc_extend tc_empty)
    []
    (tDelayedSubst (tTimeVar 0) tProp)
    (tUniverse 0).
Proof.
  change (tdtt_has_type
    (tc_extend tc_empty)
    []
    (tDelayedSubst (tTimeVar 0) tProp)
    (subst_time (tTimeVar 0) 0 (tUniverse 0))).
  apply tdtt_ty_delayed_subst.
  - apply tdtt_wf_empty.
  - apply temporal_wf_var.
    apply temporal_lookup_here.
  - apply tdtt_ty_prop.
    apply tdtt_wf_empty.
Qed.

Example utt_impredicative_product_is_a_tdtt_term :
  tdtt_has_type
    tc_empty
    []
    (tPi tProp (tVar 0))
    tProp.
Proof.
  apply utt_typing_embeds_in_tdtt.
  apply utt_impredicative_product.
Qed.
