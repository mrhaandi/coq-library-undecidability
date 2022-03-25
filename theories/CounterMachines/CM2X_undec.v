(*
  Undecidability Results(s):
    Two Counter Machine with Swap Halting (CM2X_HALT)
*)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.CounterMachines Require Import CM2X CM2_undec.

From Undecidability.CounterMachines.Reductions Require
  CM2_HALT_to_CM2X_HALT.

(* Undecidability of Two Counter Machine with Swap Halting *)
Lemma CM2X_HALT_undec : undecidable CM2X_HALT.
Proof.
  apply (undecidability_from_reducibility CM2_HALT_undec).
  exact CM2_HALT_to_CM2X_HALT.reduction.
Qed.

Check CM2X_HALT_undec.
