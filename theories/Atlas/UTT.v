(** A conservative Unified Type Theory core.

    This layer follows the ECC-style basis used by Luo's UTT: propositions
    inhabit an impredicative sort [tProp], while data types inhabit a
    predicative hierarchy [tUniverse level].  Inductive schemata are left for
    a later extension.
 *)

From Stdlib Require Import Arith.PeanoNat List.
From Atlas Require Import Syntax Ops Context DefEq MLTT.

Import ListNotations.

Inductive utt_sort : Type :=
| usProp
| usType : nat -> utt_sort.

Definition utt_sort_term (sort : utt_sort) : term :=
  match sort with
  | usProp => tProp
  | usType level => tUniverse level
  end.

Lemma shift_term_utt_sort_term :
  forall amount cutoff sort,
    shift_term amount cutoff (utt_sort_term sort) =
    utt_sort_term sort.
Proof.
  intros amount cutoff [| level]; reflexivity.
Qed.

Lemma subst_term_utt_sort_term :
  forall replacement cutoff sort,
    subst_term replacement cutoff (utt_sort_term sort) =
    utt_sort_term sort.
Proof.
  intros replacement cutoff [| level]; reflexivity.
Qed.

Lemma shift_time_utt_sort_term :
  forall amount cutoff sort,
    shift_time amount cutoff (utt_sort_term sort) =
    utt_sort_term sort.
Proof.
  intros amount cutoff [| level]; reflexivity.
Qed.

Lemma subst_time_utt_sort_term :
  forall replacement cutoff sort,
    subst_time replacement cutoff (utt_sort_term sort) =
    utt_sort_term sort.
Proof.
  intros replacement cutoff [| level]; reflexivity.
Qed.

Definition utt_product_sort (domain codomain : utt_sort) : utt_sort :=
  match codomain with
  | usProp => usProp
  | usType level_b =>
      match domain with
      | usProp => usType level_b
      | usType level_a => usType (Nat.max level_a level_b)
      end
  end.

Definition utt_sigma_level (domain : utt_sort) (level_b : nat) : nat :=
  match domain with
  | usProp => level_b
  | usType level_a => Nat.max level_a level_b
  end.

Inductive utt_wf_context : context -> Prop :=
| utt_wf_empty :
    utt_wf_context []
| utt_wf_extend :
    forall gamma a sort,
      utt_wf_context gamma ->
      utt_has_type gamma a (utt_sort_term sort) ->
      utt_wf_context (a :: gamma)
with utt_has_type : context -> term -> term -> Prop :=
| utt_ty_prop :
    forall gamma,
      utt_wf_context gamma ->
      utt_has_type gamma tProp (tUniverse 0)
| utt_ty_universe :
    forall gamma level,
      utt_wf_context gamma ->
      utt_has_type gamma (tUniverse level) (tUniverse (S level))
| utt_ty_var :
    forall gamma index a,
      utt_wf_context gamma ->
      lookup gamma index a ->
      utt_has_type gamma (tVar index) a
| utt_ty_pi :
    forall gamma a b domain_sort codomain_sort,
      utt_has_type gamma a (utt_sort_term domain_sort) ->
      utt_has_type (a :: gamma) b (utt_sort_term codomain_sort) ->
      utt_has_type gamma (tPi a b)
        (utt_sort_term (utt_product_sort domain_sort codomain_sort))
| utt_ty_lam :
    forall gamma a body b domain_sort codomain_sort,
      utt_has_type gamma a (utt_sort_term domain_sort) ->
      utt_has_type (a :: gamma) b (utt_sort_term codomain_sort) ->
      utt_has_type (a :: gamma) body b ->
      utt_has_type gamma (tLam body) (tPi a b)
| utt_ty_app :
    forall gamma f argument a b,
      utt_has_type gamma f (tPi a b) ->
      utt_has_type gamma argument a ->
      utt_has_type gamma (tApp f argument) (subst_term argument 0 b)
| utt_ty_sigma :
    forall gamma a b domain_sort level_b,
      utt_has_type gamma a (utt_sort_term domain_sort) ->
      utt_has_type (a :: gamma) b (tUniverse level_b) ->
      utt_has_type gamma (tSigma a b)
        (tUniverse (utt_sigma_level domain_sort level_b))
| utt_ty_pair :
    forall gamma a b first second domain_sort level_b,
      utt_has_type gamma a (utt_sort_term domain_sort) ->
      utt_has_type (a :: gamma) b (tUniverse level_b) ->
      utt_has_type gamma first a ->
      utt_has_type gamma second (subst_term first 0 b) ->
      utt_has_type gamma (tPair first second) (tSigma a b)
| utt_ty_fst :
    forall gamma pair a b,
      utt_has_type gamma pair (tSigma a b) ->
      utt_has_type gamma (tFst pair) a
| utt_ty_snd :
    forall gamma pair a b,
      utt_has_type gamma pair (tSigma a b) ->
      utt_has_type gamma (tSnd pair) (subst_term (tFst pair) 0 b)
| utt_ty_id :
    forall gamma a x y level,
      utt_has_type gamma a (tUniverse level) ->
      utt_has_type gamma x a ->
      utt_has_type gamma y a ->
      utt_has_type gamma (tId a x y) (tUniverse level)
| utt_ty_refl :
    forall gamma a x,
      utt_has_type gamma x a ->
      utt_has_type gamma (tRefl x) (tId a x x)
| utt_ty_conv :
    forall gamma t a b sort,
      utt_has_type gamma t a ->
      utt_has_type gamma b (utt_sort_term sort) ->
      defeq a b ->
      utt_has_type gamma t b
| utt_ty_prop_lift :
    forall gamma proposition level,
      utt_has_type gamma proposition tProp ->
      utt_has_type gamma proposition (tUniverse level)
| utt_ty_type_lift :
    forall gamma a lower upper,
      utt_has_type gamma a (tUniverse lower) ->
      lower <= upper ->
      utt_has_type gamma a (tUniverse upper).

Scheme utt_wf_context_ind' := Induction for utt_wf_context Sort Prop
with utt_has_type_ind' := Induction for utt_has_type Sort Prop.

Combined Scheme utt_typing_mutind
  from utt_wf_context_ind', utt_has_type_ind'.

Theorem mltt_embeds_in_utt :
  (forall gamma,
      wf_context gamma ->
      utt_wf_context gamma) /\
  (forall gamma t a,
      has_type gamma t a ->
      utt_has_type gamma t a).
Proof.
  apply mltt_typing_mutind
    with (P := fun gamma _ => utt_wf_context gamma)
         (P0 := fun gamma t a _ => utt_has_type gamma t a).
  - apply utt_wf_empty.
  - intros gamma a level _ Hgamma _ Ha.
    apply utt_wf_extend with (sort := usType level).
    + exact Hgamma.
    + exact Ha.
  - intros gamma level _ Hgamma.
    apply utt_ty_universe.
    exact Hgamma.
  - intros gamma index a _ Hgamma Hlookup.
    apply utt_ty_var.
    + exact Hgamma.
    + exact Hlookup.
  - intros gamma a b level_a level_b _ Ha _ Hb.
    apply utt_ty_pi with
        (domain_sort := usType level_a)
        (codomain_sort := usType level_b).
    + exact Ha.
    + exact Hb.
  - intros gamma a body b level_a level_b _ Ha _ Hb _ Hbody.
    apply utt_ty_lam with
        (domain_sort := usType level_a)
        (codomain_sort := usType level_b).
    + exact Ha.
    + exact Hb.
    + exact Hbody.
  - intros gamma f argument a b _ Hf _ Hargument.
    apply utt_ty_app with (a := a) (b := b).
    + exact Hf.
    + exact Hargument.
  - intros gamma a b level_a level_b _ Ha _ Hb.
    apply utt_ty_sigma with
        (domain_sort := usType level_a)
        (level_b := level_b).
    + exact Ha.
    + exact Hb.
  - intros gamma a b first second level_a level_b
      _ Ha _ Hb _ Hfirst _ Hsecond.
    apply utt_ty_pair with
        (domain_sort := usType level_a)
        (level_b := level_b).
    + exact Ha.
    + exact Hb.
    + exact Hfirst.
    + exact Hsecond.
  - intros gamma pair a b _ Hpair.
    apply utt_ty_fst with (b := b).
    exact Hpair.
  - intros gamma pair a b _ Hpair.
    apply utt_ty_snd with (a := a) (b := b).
    exact Hpair.
  - intros gamma a x y level _ Ha _ Hx _ Hy.
    apply utt_ty_id with (level := level).
    + exact Ha.
    + exact Hx.
    + exact Hy.
  - intros gamma a x _ Hx.
    apply utt_ty_refl.
    exact Hx.
  - intros gamma t a b level _ Ht _ Hb Heq.
    apply utt_ty_conv with (a := a) (sort := usType level).
    + exact Ht.
    + exact Hb.
    + exact Heq.
Qed.

Corollary mltt_context_embeds_in_utt :
  forall gamma,
    wf_context gamma ->
    utt_wf_context gamma.
Proof.
  apply mltt_embeds_in_utt.
Qed.

Corollary mltt_typing_embeds_in_utt :
  forall gamma t a,
    has_type gamma t a ->
    utt_has_type gamma t a.
Proof.
  apply mltt_embeds_in_utt.
Qed.

Example utt_prop_is_a_small_type :
  utt_has_type [] tProp (tUniverse 0).
Proof.
  apply utt_ty_prop.
  apply utt_wf_empty.
Qed.

Example utt_products_into_prop_are_impredicative :
  utt_product_sort (usType 7) usProp = usProp.
Proof. reflexivity. Qed.

Example utt_strong_sums_remain_predicative :
  utt_sigma_level (usType 2) 4 = 4.
Proof. reflexivity. Qed.

Example utt_impredicative_product :
  utt_has_type []
    (tPi tProp (tVar 0))
    tProp.
Proof.
  apply utt_ty_pi with
      (domain_sort := usType 0)
      (codomain_sort := usProp).
  - apply utt_ty_prop.
    apply utt_wf_empty.
  - apply utt_ty_var.
    + apply utt_wf_extend with (sort := usType 0).
      * apply utt_wf_empty.
      * apply utt_ty_prop.
        apply utt_wf_empty.
    + apply lookup_here.
Qed.

Example mltt_identity_function_is_a_utt_term :
  utt_has_type []
    (tLam (tVar 0))
    (tPi (tUniverse 1) (tUniverse 1)).
Proof.
  apply mltt_typing_embeds_in_utt.
  apply identity_function_on_small_types.
Qed.
