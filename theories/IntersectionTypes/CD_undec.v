(*
  Autor(s):
    Andrej Dudenhefner (1)
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Undecidability Result(s):
    Intersection Type Inhabitation (CD_INH)
    Intersection Type Typability (CD_TYP)
    Intersection Type Type Checking (CD_TC)
*)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Undecidability.IntersectionTypes.CD.
From Undecidability.IntersectionTypes.Reductions Require SSTS01_to_CD_INH.

Require Import Undecidability.StringRewriting.SSTS_undec.

(* Undecidability of Intersection Type Inhabitation *)
Theorem CD_INH_undec : undecidable CD_INH.
Proof.
  apply (undecidability_from_reducibility SSTS01_undec).
  exact SSTS01_to_CD_INH.reduction.
Qed.

Check CD_INH_undec.

(* Undecidability of Intersection Type Typability *)
Theorem CD_TYP_undec : undecidable CD_TYP.
Proof.
Admitted.


(* Undecidability of Intersection Type Type Checking *)
Theorem CD_TC_undec : undecidable CD_TC.
Proof.
Admitted.
