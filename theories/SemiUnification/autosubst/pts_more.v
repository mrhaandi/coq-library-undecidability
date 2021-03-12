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

Fixpoint rinst_inst_term' {xi P} : ren_term xi P = subst_term (funcomp var xi) P.
Proof. by apply: rinst_inst_term. Qed.

(* TODO rinstId_term uses funext, which is bad *)
(* alternative: ren_term_id *)
Definition term_norm := (compRen_term, renRen_term, @ren_term_id, renComp_term, compComp_term).

(* such that simpl evaluates funcomp f g x *)
Arguments funcomp {X Y Z} _ _ _ /.
(* such that simpl evaluates id x*)
Arguments unscoped.id _ _/.




(* AUTOSUBST EXPERIMENTS *)
(* NOT RELEVANT FOR DEVELOPMENT *)

Lemma some_funcomp_property {X Y: Type} {s: X} {f: nat -> Y} {g: Y -> X} {t: Y}: 
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

(* maybe this is even more general ? *)
(* does not depend on term *)
Definition more_general_principle4 {X Y Z : Type}
  {F : (nat -> X) -> Y -> Z}
  {f : nat -> X} {g : nat -> Y} {h : nat -> Z}
  {x : X} {y : Y} {z : Z}
  {uX : X -> X} {uY : Y -> Y} {uZ : Z -> Z}
  (Eq_h : forall n, (g >> F f) n = h n)
  (Eq_z : F (x .: f >> uX) y = z)
  (Eq1 : forall y', F (scons x (f >> uX)) (uY y') = F (f >> uX) y')
  (Eq2 : forall y', uZ (F f y') = F (f >> uX) y')
  :
  forall (n: nat),
  ((scons y (g >> uY)) >> F (scons x (f >> uX))) n = 
  (scons z (h >> uZ)) n.
Proof.
  intros [|n].
  - apply Eq_z.
  - apply (eq_trans (Eq1 _)).
    apply (eq_trans (eq_sym (Eq2 _))).
    apply (ap uZ).
    apply Eq_h.
  Show Proof.
Qed.

Definition up_ren_ren_term_term_p4 (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
  eapply (more_general_principle4 (F := id)).
  - apply Eq.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  Show Proof.
Qed.

Definition up_ren_subst_term_term_p4 (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
  eapply (more_general_principle4 (F := id)).
  - apply Eq.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  Show Proof.
Qed.


Definition up_subst_subst_term_term_p4 (sigma : forall _ : nat, term)
  (tau_term : forall _ : nat, term) (theta : forall _ : nat, term)
  (Eq : forall x, eq (funcomp (subst_term tau_term) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x)
    (up_term_term theta x).
Proof.
  eapply (more_general_principle4).
  exact Eq.
  reflexivity.
  apply compRenSubst_term.
  reflexivity.
  apply compSubstRen_term.
  reflexivity.
  Show Proof.
Qed.

Definition up_subst_ren_term_term_p4 (sigma : forall _ : nat, term)
         (zeta_term : forall _ : nat, nat) (theta : forall _ : nat, term)
         (Eq : forall x, eq (funcomp (ren_term zeta_term) sigma x) (theta x)) :
         forall x,
         eq (funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x)
           (up_term_term theta x).
Proof.
  eapply (more_general_principle4).
  exact Eq.
  reflexivity.
  apply compRenRen_term.
  reflexivity.
  apply compRenRen_term.
  reflexivity.
  Show Proof.
Qed.

(* not exactly rinstInst_up_term_term_p4, this is an instance of up_ren_subst_term_term_p4 
while up_term_term var == var; see upId_term_term *)
Definition rinstInst_up_term_term_p4 (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp var xi x = sigma x) :
  forall x, funcomp (up_term_term var) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
  eapply (more_general_principle4 (F := id)).
  - exact Eq.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
