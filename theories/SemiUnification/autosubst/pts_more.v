(* Andrej: the contents of this file could be incorporated into autosubst generated files 
Here, I use ssreflect for convenience. Actual generated proofs should be terms.
*)

Require Import Undecidability.SemiUnification.autosubst.pts.

Require Import ssreflect.

(* TODO part of autosubst? *)
Lemma upRen_term_term_id x : upRen_term_term id x = x.
Proof. by case: x. Qed.

Lemma up_term_term_var x : up_term_term var x = var x.
Proof. by case: x. Qed.

(* TODO autosubst? *)
Lemma shift_up_term_term sigma x : 
  (shift >> up_term_term sigma) x = (sigma >> ren_term shift) x.
Proof. by case: x. Qed.

(* TODO autosubst? sometimes more easy to use *)
Lemma up_ren_subst_term_term' xi sigma x:
  (upRen_term_term xi >> up_term_term sigma) x = up_term_term (xi >> sigma) x.
Proof. by apply: up_ren_subst_term_term. Qed.

(* TODO autosubst? *)
Lemma up_term_term_funcomp {xi sigma x} : 
  up_term_term (xi >> sigma) x = (upRen_term_term xi >> up_term_term sigma) x.
Proof.
  by case: x.
Qed.

(*TODO part of autosubst? no funext *)
Lemma ren_term_id {P} : ren_term id P = P.
Proof.
  elim: P.
  - done.
  - done.
  - by move=> /= ? -> ? ->.
  - move=> /= ? -> ?.
    under [ren_term (upRen_term_term id) _]extRen_term => ? do 
      rewrite upRen_term_term_id.
    by move=> ->.
  - move=> /= ? -> ?.
    under [ren_term (upRen_term_term id) _]extRen_term => ? do 
      rewrite upRen_term_term_id.
    by move=> ->.
Qed.

(*TODO part of autosubst? no funext *)
Lemma subst_term_var {P} : subst_term var P = P.
Proof.
  elim: P.
  - done.
  - done.
  - by move=> /= ? -> ? ->.
  - move=> /= ? -> ?.
    under [subst_term (up_term_term var) _]ext_term => ? do 
      rewrite up_term_term_var.
    by move=> ->.
  - move=> /= ? -> ?.
    under [subst_term (up_term_term var) _]ext_term => ? do 
      rewrite up_term_term_var.
    by move=> ->.
Qed.

(* TODO autosubst? *)
Lemma ext_ren_term' {xi zeta P Q} : 
  (forall x, xi x = zeta x) -> P = Q -> ren_term xi P = ren_term zeta Q.
Proof. by move=> /extRen_term + ->. Qed.

(* TODO rinstId_term uses funext, which is bad *)
(* alternative: ren_term_id *)
Definition term_norm := (compRen_term, renRen_term, @ren_term_id, renComp_term, compComp_term).

(* such that simpl evaluates funcomp f g x *)
Arguments funcomp {X Y Z} _ _ _ /.
(* such that simpl evaluates id x*)
Arguments unscoped.id _ _/.