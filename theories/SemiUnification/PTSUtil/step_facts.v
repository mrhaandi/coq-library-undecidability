(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(*
  Synopsis:
    Facts about the single-step beta reduction relation for pts-terms.
*)

Require Import Undecidability.SemiUnification.HOSemiU.
Require Import Undecidability.SemiUnification.autosubst.unscoped.
Require Import Undecidability.SemiUnification.autosubst.pts.
Require Import Undecidability.SemiUnification.autosubst.pts_more.
Require Import Undecidability.SemiUnification.autosubst.allfv_more.

Require Import ssreflect ssrbool ssrfun.

(* case analysis on the single-step beta relation *)
Lemma stepE {P Q} : step P Q -> 
  match P with
  | var _ => False
  | const _ => False
  | app P1 P2 => 
    (exists P11 P12, P1 = lam P11 P12 /\ Q = subst_term (scons P2 var) P12) \/
    (exists Q1, Q = app Q1 P2 /\ step P1 Q1) \/
    (exists Q2, Q = app P1 Q2 /\ step P2 Q2)
  | lam P1 P2 => 
      (exists Q1, Q = lam Q1 P2 /\ step P1 Q1) \/
      (exists Q2, Q = lam P1 Q2 /\ step P2 Q2)
  | Pi P1 P2 => 
      (exists Q1, Q = Pi Q1 P2 /\ step P1 Q1) \/
      (exists Q2, Q = Pi P1 Q2 /\ step P2 Q2)
  end.
Proof. case; by eauto. Qed.

(* TODO move to beta facts *)
Lemma step_betaI {P Q R R'} : R' = (subst_term (scons R var) Q) -> step (app (lam P Q) R) R'.
Proof. move=> ->. by apply: step_beta. Qed.

(* TODO move to beta facts *)
Lemma step_ren_termI xi {P Q} : step P Q -> step (ren_term xi P) (ren_term xi Q).
Proof.
  move=> H. elim: H xi; [|by eauto using step with nocore ..].
  move=> > /=. apply: step_betaI. rewrite ?term_norm.
  apply: ext_term. by case.
Qed.

(* TODO move to beta facts *)
Lemma step_subst_termI sigma {P Q} : step P Q -> step (subst_term sigma P) (subst_term sigma Q).
Proof.
  move=> H. elim: H sigma; [|by eauto using step with nocore ..].
  move=> > /=. apply: step_betaI. rewrite ?term_norm.
  apply: ext_term. case; first done.
  move=> ? /=. by rewrite term_norm subst_term_var. 
Qed.

Lemma step_allfv_term_impl {p P Q} : step P Q -> allfv_term p P -> allfv_term p Q.
Proof.
  move=> H. elim: H p; [| by firstorder done ..].
  move=> > /= [[_ +] ?]. rewrite allfv_subst_term.
  apply: allfv_term_impl. by case.
Qed.
