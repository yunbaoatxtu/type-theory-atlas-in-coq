(** Shared definitional equality.

    The equality relation is syntax directed and independent of an object
    theory's typing rules.  MLTT, UTT, and TDTT can therefore share the core
    computation rules while controlling admissible terms through typing.
 *)

From Atlas Require Import Syntax Ops.

Inductive defeq : term -> term -> Prop :=
| de_refl :
    forall t,
      defeq t t
| de_sym :
    forall t u,
      defeq t u ->
      defeq u t
| de_trans :
    forall t u v,
      defeq t u ->
      defeq u v ->
      defeq t v
| de_beta :
    forall body argument,
      defeq (tApp (tLam body) argument)
            (subst_term argument 0 body)
| de_fst_pair :
    forall first second,
      defeq (tFst (tPair first second)) first
| de_snd_pair :
    forall first second,
      defeq (tSnd (tPair first second)) second
| de_pi :
    forall a a' b b',
      defeq a a' ->
      defeq b b' ->
      defeq (tPi a b) (tPi a' b')
| de_lam :
    forall body body',
      defeq body body' ->
      defeq (tLam body) (tLam body')
| de_app :
    forall f f' argument argument',
      defeq f f' ->
      defeq argument argument' ->
      defeq (tApp f argument) (tApp f' argument')
| de_sigma :
    forall a a' b b',
      defeq a a' ->
      defeq b b' ->
      defeq (tSigma a b) (tSigma a' b')
| de_pair :
    forall first first' second second',
      defeq first first' ->
      defeq second second' ->
      defeq (tPair first second) (tPair first' second')
| de_fst :
    forall pair pair',
      defeq pair pair' ->
      defeq (tFst pair) (tFst pair')
| de_snd :
    forall pair pair',
      defeq pair pair' ->
      defeq (tSnd pair) (tSnd pair')
| de_id :
    forall a a' x x' y y',
      defeq a a' ->
      defeq x x' ->
      defeq y y' ->
      defeq (tId a x y) (tId a' x' y')
| de_refl_term :
    forall x x',
      defeq x x' ->
      defeq (tRefl x) (tRefl x')
| de_at :
    forall a a' time time',
      defeq a a' ->
      defeq time time' ->
      defeq (tAt a time) (tAt a' time')
| de_later :
    forall a a',
      defeq a a' ->
      defeq (tLater a) (tLater a')
| de_next :
    forall a a',
      defeq a a' ->
      defeq (tNext a) (tNext a')
| de_fix_unfold :
    forall body,
      defeq (tFix body)
        (subst_term (tNext (tFix body)) 0 body)
| de_fix :
    forall body body',
      defeq body body' ->
      defeq (tFix body) (tFix body')
| de_later_at :
    forall clock clock' a a',
      defeq clock clock' ->
      defeq a a' ->
      defeq (tLaterAt clock a) (tLaterAt clock' a')
| de_next_at :
    forall clock clock' t t',
      defeq clock clock' ->
      defeq t t' ->
      defeq (tNextAt clock t) (tNextAt clock' t')
| de_fix_at_unfold :
    forall clock body,
      defeq (tFixAt clock body)
        (subst_term (tNextAt clock (tFixAt clock body)) 0 body)
| de_fix_at :
    forall clock clock' body body',
      defeq clock clock' ->
      defeq body body' ->
      defeq (tFixAt clock body) (tFixAt clock' body')
| de_clock_beta :
    forall body clock_index,
      defeq (tClockApp (tClockLam body) (tTimeVar clock_index))
            (subst_time (tTimeVar clock_index) 0 body)
| de_clock_pi :
    forall body body',
      defeq body body' ->
      defeq (tClockPi body) (tClockPi body')
| de_clock_lam :
    forall body body',
      defeq body body' ->
      defeq (tClockLam body) (tClockLam body')
| de_clock_app :
    forall f f' clock clock',
      defeq f f' ->
      defeq clock clock' ->
      defeq (tClockApp f clock) (tClockApp f' clock')
| de_delayed_subst_compute :
    forall body clock_index,
      defeq (tDelayedSubst (tTimeVar clock_index) body)
            (subst_time (tTimeVar clock_index) 0 body)
| de_delayed_subst :
    forall clock clock' body body',
      defeq clock clock' ->
      defeq body body' ->
      defeq (tDelayedSubst clock body) (tDelayedSubst clock' body').

Lemma defeq_reflexive :
  forall t, defeq t t.
Proof. apply de_refl. Qed.

Lemma defeq_symmetric :
  forall t u, defeq t u -> defeq u t.
Proof. apply de_sym. Qed.

Lemma defeq_transitive :
  forall t u v, defeq t u -> defeq u v -> defeq t v.
Proof. apply de_trans. Qed.

Example beta_identity_on_universe_zero :
  defeq
    (tApp (tLam (tVar 0)) (tUniverse 0))
    (tUniverse 0).
Proof. apply de_beta. Qed.

Example first_projection_of_pair :
  defeq
    (tFst (tPair (tUniverse 0) (tUniverse 1)))
    (tUniverse 0).
Proof. apply de_fst_pair. Qed.

Example temporal_congruence :
  defeq
    (tLater (tApp (tLam (tVar 0)) (tUniverse 0)))
    (tLater (tUniverse 0)).
Proof.
  apply de_later.
  apply de_beta.
Qed.

Example guarded_fix_unfolds :
  defeq (tFix tProp) tProp.
Proof. apply de_fix_unfold. Qed.

Example clocked_guarded_fix_unfolds :
  defeq (tFixAt (tTimeVar 0) tProp) tProp.
Proof. apply de_fix_at_unfold. Qed.

Example clock_application_computes :
  defeq
    (tClockApp (tClockLam tProp) (tTimeVar 0))
    tProp.
Proof. apply de_clock_beta. Qed.

Example delayed_substitution_computes :
  defeq
    (tDelayedSubst (tTimeVar 0) tProp)
    tProp.
Proof. apply de_delayed_subst_compute. Qed.
