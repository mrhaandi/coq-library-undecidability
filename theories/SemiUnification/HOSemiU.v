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

Require Import Undecidability.SemiUnification.autosubst.unscoped.
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

(* beta-equivalence is the reflexive, symmetric, transitive closure 
  of the single-step beta reduction *)
Definition eq_beta := clos_refl_sym_trans term step.

(* a valuation assigns terms to term variables *)
Definition valuation : Type := nat -> term.

(* inequality: P ≤ Q *)
Definition inequality : Type := (term * term).

(* terms which satisfy property p *)
(* for example, "p" can be "normalizing", "normal", or "simple" *)
Definition term' (p : term -> Prop) := { P : term | p P }.

(* inequality: P ≤ Q where P and Q satisfy property p *)
Definition inequality' (p : term -> Prop) : Type := (term' p * term' p).

(* a valuation assigns terms with property p to term variables *)
Definition valuation' (p : term -> Prop) : Type := nat -> term' p.

(* erase term annotation *)
Definition trim_term' {p : term -> Prop} : term' p -> term := fun P' => proj1_sig P'.

(* erase inequality annotation *)
Definition trim_inequality' {p : term -> Prop} : inequality' p -> inequality := 
  fun '(P', Q') => (trim_term' P', trim_term' Q').

(* erase valuation annotations *)
Definition trim_valuation' {p : term -> Prop} : valuation' p -> valuation := 
  fun φ' => fun x => trim_term' (φ' x).

(* substitution function "subst_term" is defined in pts.v *)

(* Higher-order Semi-unification Definition *)

(* φ solves P ≤ Q, if there is ψ such that ψ (φ (P)) =β φ (Q) *)
(* property p is trimmed before substitution *)
Definition solution {p : term -> Prop} (φ' : valuation' p) : inequality' p -> Prop := 
  fun '(P', Q') => 
    exists (ψ' : valuation' p), 
      let '(P, Q) := (trim_term' P', trim_term' Q') in
      let φ := trim_valuation' φ' in
      let ψ := trim_valuation' ψ' in
      eq_beta (subst_term ψ (subst_term φ P)) (subst_term φ Q).

(* Higher-order Semi-unification *)
(* is there a valuation φ that solves all inequalities? *)
(* for example, property "p" can be "normalizing", "normal", or "simple" *)
Definition HOSemiU (p : term -> Prop) : list (inequality' p) -> Prop := 
  fun cs => exists (φ : valuation' p), forall (c : inequality' p), In c cs -> solution φ c.

(* a term is (strongly) normalizing if it only allows for finite reduction chains *)
Definition normalizing (P : term) : Prop := 
  Acc (transp term step) P.

(* Higher-order Semi-unification for strongly normalizing terms *)
Definition HOSemiU_SN := HOSemiU normalizing.

(* a term is normal if it is not reducible *)
Definition normal (P : term) : Prop :=
  forall Q, not (step P Q).

(* Higher-order Semi-unification for terms in normal form *)
Definition HOSemiU_NF := HOSemiU normal.

(* notion of a simple type represented by a term
  P, Q ::= x | Pi (x : P). Q (where x is not free in Q) *)
Fixpoint simple (P: term) :=
  match P with
  | var _ => True
  | const _ => False 
  | app P Q => False
  | lam P Q => False
  | Pi P Q => (* Pi (x : P). Q is simple iff *)
      simple P /\ (* P is simple *)
      simple Q /\ (* Q is simple *)
      exists Q', Q = ren_term shift Q' (* x does not occur free in Q *) 
  end.

(* Higher-order Semi-unification for simple terms *)
Definition HOSemiU_SIM := HOSemiU simple.
