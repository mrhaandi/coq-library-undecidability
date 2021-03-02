(* Andrej: the contents of this file could be incorporated into autosubst generated files 
Here, I use ssreflect for convenience. Actual generated proofs should be terms.
*)

Require Import Undecidability.SemiUnification.autosubst.unscoped.
Require Import Undecidability.SemiUnification.autosubst.pts.
Require Import Undecidability.SemiUnification.autosubst.unscoped_more.

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

(* AUTOSUBST EXPERIMENTS *)

Lemma ad {X Y: Type} {s: X} {f: nat -> Y} {g: Y -> X} {t: Y}: 
  s = g t ->
  forall x, scons s (funcomp g f) x = funcomp g (scons t f) x.
Proof.
  move=> H. by case.
Qed.

(* this is the important property! not ad-hoc, no sigma*)
Definition up_subst_ren_term_term_underlying
(zeta_term : forall _ : nat, nat): forall s,
ren_term (upRen_term_term zeta_term) (ren_term ↑ s) =
ren_term ↑ (ren_term zeta_term s) :=
fun (s : term) =>
  eq_trans
    (compRenRen_term ↑ (upRen_term_term zeta_term) 
    (zeta_term >> ↑) (fun x : nat => eq_refl) s)
    (eq_sym
      (compRenRen_term zeta_term ↑ (zeta_term >> ↑) 
          (fun x : nat => eq_refl) s)).

(* this is the important property! not ad-hoc, no sigma*)
Definition up_subst_subst_term_term_underlying
(tau_term : forall _ : nat, term): forall s,
subst_term (up_term_term tau_term) (ren_term shift s) =
ren_term shift (subst_term tau_term s) :=
fun (s : term) =>
eq_trans
  (compRenSubst_term ↑ (up_term_term tau_term) (tau_term >> ren_term ↑)
   (fun _ => eq_refl) s)
  (eq_sym
     (compSubstRen_term tau_term ↑ (tau_term >> ren_term ↑)
        (fun _ => eq_refl) s)).

(*
H is ren_term shift
z is var 0

F f : subst_term f
G f : subst_term (up_term_term f)

or

F f : ren_term f
G f : ren_term (upRen_term_term f)
*)

(* maybe this is even more general ? *)
(* does not depend on term *)
Definition more_general_principle3 {X Y : Type}
  {sigma : nat -> Y} {F: (nat -> X) -> Y -> Y} {G: X -> X} {H: Y -> Y}
  {tau_term : nat -> X} {theta : nat -> Y} {x: X} (y: Y)
  (Eq : forall x, funcomp (F tau_term) sigma x = theta x)
  (Eq1 : F (x .: tau_term >> G) y = y)
  (Eq2 : forall s, F (x .: tau_term >> G) (H s) = F (tau_term >> G) s)
  (Eq3 : forall s, H (F tau_term s) = F (tau_term >> G) s)
  :
  forall (n: nat),
  (funcomp (F (x .: tau_term >> G)) (scons y (sigma >> H)) n) = 
  (scons y (theta >> H) n).
Proof.
  intros [|n].
  - apply Eq1.
  - apply (eq_trans (Eq2 _)).
    apply (eq_trans (eq_sym (Eq3 _))).
    apply (ap H).
    apply Eq.
Qed.

(*showcase 1 more_general_principle3 *)
Definition up_subst_subst_term_term_using_test (sigma : forall _ : nat, term)
  (tau_term : forall _ : nat, term) (theta : forall _ : nat, term)
  (Eq : forall x, eq (funcomp (subst_term tau_term) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x)
    (up_term_term theta x).
Proof.
  eapply (more_general_principle3).
  exact Eq.
  reflexivity.
  apply compRenSubst_term.
  reflexivity.
  apply compSubstRen_term.
  reflexivity.
  Show Proof.
Qed.

(*showcase 2 more_general_principle3 *)
Definition up_subst_ren_term_term (sigma : forall _ : nat, term)
         (zeta_term : forall _ : nat, nat) (theta : forall _ : nat, term)
         (Eq : forall x, eq (funcomp (ren_term zeta_term) sigma x) (theta x)) :
         forall x,
         eq (funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x)
           (up_term_term theta x).
Proof.
  eapply (more_general_principle3).
  exact Eq.
  reflexivity.
  apply compRenRen_term.
  reflexivity.
  apply compRenRen_term.
  reflexivity.
  Show Proof.
Qed.


(* this is maybe the general lemma 
independent of autosubst (unscoped)
skeleton of the actual proof *)
Definition more_general_principle2 {X Y : Type}
  (sigma : nat -> Y) {F G: X -> Y -> Y} {H: Y -> Y}
  (tau_term : X) (theta : nat -> Y) (z: Y)
  (Eq : forall x, funcomp (F tau_term) sigma x = theta x)
  (Eq1 : G tau_term z = z)
  (Eq2 : forall s, G tau_term (H s) = H (F tau_term s))
  :
  forall (x: nat),
  (funcomp (G tau_term) (scons z (sigma >> H)) x) = 
  (scons z (theta >> H) x).
Proof.
  intros [|x].
  - apply Eq1.
  - eapply eq_trans.
    apply Eq2.
    apply (ap H). apply Eq.
    Show Proof.
Qed.

(*showcase 1 more_general_principle2 *)
Definition up_subst_subst_term_term_using_test' (sigma : forall _ : nat, term)
  (tau_term : forall _ : nat, term) (theta : forall _ : nat, term)
  (Eq : forall x, eq (funcomp (subst_term tau_term) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x)
    (up_term_term theta x).
Proof.
  eapply (more_general_principle2 _ _ (G := (fun tau_term => subst_term (up_term_term tau_term)))). 
  exact Eq.
  reflexivity.
  apply up_subst_subst_term_term_underlying.
  Show Proof.
Qed.

(*showcase 2 more_general_principle2 *)
Definition up_subst_ren_term_term' (sigma : forall _ : nat, term)
         (zeta_term : forall _ : nat, nat) (theta : forall _ : nat, term)
         (Eq : forall x, eq (funcomp (ren_term zeta_term) sigma x) (theta x)) :
         forall x,
         eq (funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x)
           (up_term_term theta x).
Proof.
  eapply (more_general_principle2 _ _ (G := (fun zeta_term => ren_term (upRen_term_term zeta_term)))).
  exact Eq.
  reflexivity.
  apply up_subst_ren_term_term_underlying.
  Show Proof.
Qed.
           

Definition up_subst_subst_term_term (sigma : forall _ : nat, term)
  (tau_term : forall _ : nat, term) (theta : forall _ : nat, term)
  (Eq : forall x, eq (funcomp (subst_term tau_term) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x)
    (up_term_term theta x) :=
  fun x => match x with
    | 0 => eq_refl
    | S x' =>
        eq_trans (up_subst_subst_term_term_underlying tau_term (sigma x'))
          (ap (ren_term ↑) (Eq x'))
    end.
