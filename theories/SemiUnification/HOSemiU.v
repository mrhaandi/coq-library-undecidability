(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Higher-order Semi-unification (HOSemiU)
*)

Require Import List Relation_Operators.

Require Import Undecidability.SemiUnification.autosubst.pts.
(* 
  terms (according to pure type systems) 
  P Q R ::= x | c | P Q | lambda (x : P). Q | Pi (x : P). Q 
  where x ranges over term variables and c ranges over term constants
*)

(* single step beta reduction relation *)
Inductive step : term -> term -> Prop :=
  | step_beta P Q R: step (app (lam P Q) R) (subst_term (scons R var) Q) 
  | step_appL P P' Q: step P P' -> step (app P Q) (app P' Q)
  | step_appR P Q Q': step Q Q' -> step (app P Q) (app P Q')
  | step_lamL P P' Q: step P P' -> step (lam P Q) (lam P' Q)
  | step_lamR P Q Q': step Q Q' -> step (lam P Q) (lam P Q')
  | step_PiL P P' Q: step P P' -> step (Pi P Q) (Pi P' Q)
  | step_PiR P Q Q': step Q Q' -> step (Pi P Q) (Pi P Q').

(* a term is (strongly) normalizing if it only allows for finite reduction chains *)
Definition normalizing (P : term) : Prop := 
  Acc (transp term step) P.

(* a term is normal if it is not reducible *)
Definition normal (P : term) : Prop :=
  forall Q, not (step P Q).

(* beta-equivalence is the reflexive, symmetric, transitive closure 
  of the single-step beta reduction *)
Definition eq_beta := clos_refl_sym_trans term step.

(* a valuation assigns terms with property p to term variables *)
Definition valuation (p : term -> Prop) : Type := nat -> { P : term | p P }.

(* substitution function "subst_term" is defined in pts.v *)

(* replace free variables by assigned terms with property p *)
(* for example, p can be "normal_form" or "simple" *)
Definition substitute {p : term -> Prop} (φ : valuation p) (P : term) : term :=
  subst_term (fun x => proj1_sig (φ x)) P.

(* Higher-order Semi-unification Definition *)

(* inequality: s ≤ t *)
Definition inequality : Type := (term * term).

(* φ solves s ≤ t, if there is ψ such that ψ (φ (s)) =β φ (s) *)
(* property p in the range of φ is the same as in the range of ψ *)
Definition solution {p : term -> Prop} (φ : valuation p) : inequality -> Prop := 
  fun '(P, Q) => exists (ψ : valuation p), 
    eq_beta (substitute ψ (substitute φ P)) (substitute φ Q).

(* Higher-order Semi-unification *)
(* is there a normalizing valuation φ that solves all inequalities? *)
Definition HOSemiU (cs: list inequality) := 
  exists (φ: valuation normalizing), forall (c: inequality), In c cs -> solution φ c.

(* Higher-order Semi-unification *)
(* is there a normal valuation φ that solves all inequalities? *)
Definition HOSemiU' (cs: list inequality) := 
  exists (φ: valuation normal), forall (c: inequality), In c cs -> solution φ c.
