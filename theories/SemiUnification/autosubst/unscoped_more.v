(* Andrej: the following content could be added to unscoped.v *)

Require Import Undecidability.SemiUnification.autosubst.unscoped.

(* associativity of functio composition *)
Definition funcomp_assoc {X1 X2 X3 X4} {f : X1 -> X2} {g : X2 -> X3} {h : X3 -> X4} : 
  funcomp h (funcomp g f) = funcomp (funcomp h g) f :=
  eq_refl.

(* extensionality principle for scons *)
Definition ext_scons {X: Type} {s t: X} {f g: nat -> X} :
  s = t -> 
  (forall x, f x = g x) -> 
  forall x, scons s f x = scons t g x :=
  fun Hst Hfg x => match x with | 0 => Hst | S x => Hfg x end.
