(*
  Undecidability Results(s):
    Two Counter Machine with Swap Halting (CM2X_HALT)
*)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.CounterMachines Require Import CM2X.
From Undecidability.MinskyMachines Require Import MM2_undec.

From Undecidability.CounterMachines.Reductions Require
  MM2_ZERO_HALTING_to_CM2X_HALT.

(* Undecidability of Two Counter Machine with Swap Halting *)
Lemma CM2X_HALT_undec : undecidable CM2X_HALT.
Proof.
  apply (undecidability_from_reducibility MM2_ZERO_HALTING_undec).
  exact MM2_ZERO_HALTING_to_CM2X_HALT.reduction.
Qed.

Check CM2X_HALT_undec.
