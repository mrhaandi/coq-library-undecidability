(* Andrej: the following content could be added to unscoped.v *)

Require Import Undecidability.SemiUnification.autosubst.unscoped.

(* associativity of functio composition *)
Lemma funcomp_assoc {X1 X2 X3 X4} {f : X1 -> X2} {g : X2 -> X3} {h : X3 -> X4} : 
  funcomp h (funcomp g f) = funcomp (funcomp h g) f.
Proof. reflexivity. Qed.