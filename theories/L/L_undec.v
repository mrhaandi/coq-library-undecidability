Require Import Undecidability.L.L.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.Synthetic Require Import
  DecidabilityFacts EnumerabilityFacts.
Require Import Undecidability.L.Enumerators.term_enum.

Require Import Undecidability.TM.TM.
Require Import Undecidability.TM.TM_undec.
Require Import Undecidability.MinskyMachines.MMA2_undec.
Require Undecidability.L.Reductions.MMA_HALTING_to_HaltLclosed.

(** ** HaltL is undecidable *)

Lemma HaltL_undec :
  undecidable (HaltL).
Proof.
Admitted.
(*
  apply (undecidability_from_reducibility HaltMTM_undec).
  eapply HaltMTM_to_HaltL.
Qed.
*)
Lemma HaltLclosed_undec :
  undecidable (HaltLclosed).
Proof.
  apply (undecidability_from_reducibility MMA2_HALTING_undec).
  eapply MMA_HALTING_to_HaltLclosed.reduction.
Qed.
