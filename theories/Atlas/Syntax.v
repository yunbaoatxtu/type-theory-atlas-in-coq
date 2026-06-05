(** Shared syntax for the Type Theory Atlas.

    The common representation is intentionally permissive.  Each object
    theory is selected by a [system] profile and [supports] rules out syntax
    that is not available in that system.
 *)

From Stdlib Require Import Bool.

Inductive system : Type :=
| MLTT
| UTT
| TDTT.

Record features : Type := {
  propositional_universe : bool;
  temporal_operators : bool;
  temporal_dependency : bool;
  guarded_recursion : bool;
  clock_quantification : bool
}.

Definition features_of (s : system) : features :=
  match s with
  | MLTT => {| propositional_universe := false;
               temporal_operators := false;
               temporal_dependency := false;
               guarded_recursion := false;
               clock_quantification := false |}
  | UTT => {| propositional_universe := true;
              temporal_operators := false;
              temporal_dependency := false;
              guarded_recursion := false;
              clock_quantification := false |}
  | TDTT => {| propositional_universe := true;
               temporal_operators := true;
               temporal_dependency := true;
               guarded_recursion := true;
               clock_quantification := true |}
  end.

(** De Bruijn indices keep binding representation independent of names. *)
Inductive term : Type :=
| tVar : nat -> term
| tUniverse : nat -> term
| tProp : term
| tPi : term -> term -> term
| tLam : term -> term
| tApp : term -> term -> term
| tSigma : term -> term -> term
| tPair : term -> term -> term
| tFst : term -> term
| tSnd : term -> term
| tId : term -> term -> term -> term
| tRefl : term -> term
| tTimeVar : nat -> term
| tAt : term -> term -> term
| tLater : term -> term
| tNext : term -> term
| tFix : term -> term
| tLaterAt : term -> term -> term
| tNextAt : term -> term -> term
| tFixAt : term -> term -> term
| tClockPi : term -> term
| tClockLam : term -> term
| tClockApp : term -> term -> term
| tDelayedSubst : term -> term -> term.

Definition has_temporal_operators (s : system) : bool :=
  temporal_operators (features_of s).

Definition has_propositional_universe (s : system) : bool :=
  propositional_universe (features_of s).

Definition has_temporal_dependency (s : system) : bool :=
  temporal_dependency (features_of s).

Definition has_guarded_recursion (s : system) : bool :=
  guarded_recursion (features_of s).

Definition has_clock_quantification (s : system) : bool :=
  clock_quantification (features_of s).

Fixpoint supports (s : system) (t : term) : bool :=
  match t with
  | tVar _ => true
  | tUniverse _ => true
  | tProp => has_propositional_universe s
  | tPi a b => supports s a && supports s b
  | tLam body => supports s body
  | tApp f a => supports s f && supports s a
  | tSigma a b => supports s a && supports s b
  | tPair a b => supports s a && supports s b
  | tFst p => supports s p
  | tSnd p => supports s p
  | tId a x y => supports s a && supports s x && supports s y
  | tRefl x => supports s x
  | tTimeVar _ => has_temporal_dependency s
  | tAt a time =>
      has_temporal_dependency s && supports s a && supports s time
  | tLater a => has_temporal_operators s && supports s a
  | tNext a => has_temporal_operators s && supports s a
  | tFix body => has_guarded_recursion s && supports s body
  | tLaterAt clock a =>
      has_temporal_operators s && supports s clock && supports s a
  | tNextAt clock t =>
      has_temporal_operators s && supports s clock && supports s t
  | tFixAt clock body =>
      has_guarded_recursion s && supports s clock && supports s body
  | tClockPi body => has_clock_quantification s && supports s body
  | tClockLam body => has_clock_quantification s && supports s body
  | tClockApp f clock =>
      has_clock_quantification s && supports s f && supports s clock
  | tDelayedSubst clock body =>
      has_clock_quantification s && supports s clock && supports s body
  end.

Definition temporal_identity : term :=
  tLater (tId (tUniverse 0) (tTimeVar 0) (tTimeVar 0)).

Example mltt_supports_dependent_functions :
  supports MLTT (tPi (tUniverse 0) (tVar 0)) = true.
Proof. reflexivity. Qed.

Example utt_supports_dependent_pairs :
  supports UTT (tSigma (tUniverse 0) (tVar 0)) = true.
Proof. reflexivity. Qed.

Example mltt_rejects_propositional_universe :
  supports MLTT tProp = false.
Proof. reflexivity. Qed.

Example utt_supports_propositional_universe :
  supports UTT tProp = true.
Proof. reflexivity. Qed.

Example mltt_rejects_temporal_identity :
  supports MLTT temporal_identity = false.
Proof. reflexivity. Qed.

Example tdtt_supports_temporal_identity :
  supports TDTT temporal_identity = true.
Proof. reflexivity. Qed.

Example utt_rejects_guarded_fix :
  supports UTT (tFix tProp) = false.
Proof. reflexivity. Qed.

Example tdtt_supports_guarded_fix :
  supports TDTT (tFix tProp) = true.
Proof. reflexivity. Qed.

Example utt_rejects_clocked_later :
  supports UTT (tLaterAt (tTimeVar 0) tProp) = false.
Proof. reflexivity. Qed.

Example tdtt_supports_clocked_later :
  supports TDTT (tLaterAt (tTimeVar 0) tProp) = true.
Proof. reflexivity. Qed.

Example utt_rejects_clock_quantification :
  supports UTT (tClockPi tProp) = false.
Proof. reflexivity. Qed.

Example tdtt_supports_clock_quantification :
  supports TDTT (tClockPi tProp) = true.
Proof. reflexivity. Qed.

Example utt_rejects_delayed_substitution :
  supports UTT (tDelayedSubst (tTimeVar 0) tProp) = false.
Proof. reflexivity. Qed.

Example tdtt_supports_delayed_substitution :
  supports TDTT (tDelayedSubst (tTimeVar 0) tProp) = true.
Proof. reflexivity. Qed.
