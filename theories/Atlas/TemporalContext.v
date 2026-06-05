(** Abstract time parameters for the first TDTT layer.

    Temporal parameters use their own De Bruijn namespace.  They are kept
    separate from ordinary term declarations so later temporal weakening and
    substitution lemmas can evolve independently.
 *)

From Atlas Require Import Syntax Ops.

Inductive temporal_context : Type :=
| tc_empty
| tc_extend : temporal_context -> temporal_context.

Inductive temporal_lookup : temporal_context -> nat -> Prop :=
| temporal_lookup_here :
    forall theta,
      temporal_lookup (tc_extend theta) 0
| temporal_lookup_there :
    forall theta index,
      temporal_lookup theta index ->
      temporal_lookup (tc_extend theta) (S index).

Inductive temporal_wf : temporal_context -> term -> Prop :=
| temporal_wf_var :
    forall theta index,
      temporal_lookup theta index ->
      temporal_wf theta (tTimeVar index).

Lemma temporal_wf_supports_tdtt :
  forall theta time,
    temporal_wf theta time ->
    supports TDTT time = true.
Proof.
  intros theta time Htime.
  inversion Htime.
  reflexivity.
Qed.

Lemma temporal_wf_shift_term :
  forall theta time,
    temporal_wf theta time ->
    forall amount cutoff,
      temporal_wf theta (shift_term amount cutoff time).
Proof.
  intros theta time Htime amount cutoff.
  inversion Htime; subst.
  simpl.
  apply temporal_wf_var.
  assumption.
Qed.

Lemma temporal_wf_subst_term :
  forall theta time,
    temporal_wf theta time ->
    forall replacement cutoff,
      temporal_wf theta (subst_term replacement cutoff time).
Proof.
  intros theta time Htime replacement cutoff.
  inversion Htime; subst.
  simpl.
  apply temporal_wf_var.
  assumption.
Qed.

Example nearest_temporal_parameter :
  temporal_lookup (tc_extend tc_empty) 0.
Proof.
  apply temporal_lookup_here.
Qed.

Example outer_temporal_parameter :
  temporal_lookup (tc_extend (tc_extend tc_empty)) 1.
Proof.
  apply temporal_lookup_there.
  apply temporal_lookup_here.
Qed.
