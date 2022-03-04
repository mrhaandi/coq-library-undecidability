(* 
  Undecidability Result(s):
    Krivine machine halting (KrivineM_HALT)
*)

From Undecidability.Synthetic Require Import Undecidability.

Require Import Undecidability.LambdaCalculus.Krivine.
From Undecidability.LambdaCalculus.Reductions Require
  wCBNclosed_to_KrivineM_HALT.

Require Import Undecidability.LambdaCalculus.wCBN_undec.

(* Undecidability of Krivine machine halting *)
Theorem KrivineM_HALT_undec : undecidable KrivineM_HALT.
Proof.
  apply (undecidability_from_reducibility wCBNclosed_undec).
  exact wCBNclosed_to_KrivineM_HALT.reduction.
Qed.

Check KrivineM_HALT_undec.
