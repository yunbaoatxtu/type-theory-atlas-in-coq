(** Ordinary variable contexts for the shared syntax.

    Context entries are stored newest first.  Looking up an entry shifts its
    type into the current context, one binder at a time.
 *)

From Stdlib Require Import List.
From Atlas Require Import Syntax Ops.

Import ListNotations.

Definition context : Type := list term.

Definition shift_time_context
    (amount cutoff : nat) (gamma : context) : context :=
  map (shift_time amount cutoff) gamma.

Definition subst_time_context
    (replacement : term) (cutoff : nat) (gamma : context) : context :=
  map (subst_time replacement cutoff) gamma.

Inductive lookup : context -> nat -> term -> Prop :=
| lookup_here :
    forall gamma a,
      lookup (a :: gamma) 0 (shift_term 1 0 a)
| lookup_there :
    forall gamma a index b,
      lookup gamma index b ->
      lookup (a :: gamma) (S index) (shift_term 1 0 b).

Example lookup_nearest_universe :
  lookup [tUniverse 0] 0 (tUniverse 0).
Proof. apply lookup_here. Qed.

Example lookup_outer_universe :
  lookup [tUniverse 0; tUniverse 1] 1 (tUniverse 1).
Proof.
  change (lookup [tUniverse 0; tUniverse 1] 1
    (shift_term 1 0 (tUniverse 1))).
  apply lookup_there.
  apply lookup_here.
Qed.
