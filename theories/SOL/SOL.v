(* * Second-Order Logic *)

Require Import Vector Arith.
Notation vec := Vector.t.


(* ** Syntax *)

(* Parameterized over function and predicate signature as well as logical operators *)
Class funcs_signature := { syms : Type; ar_syms : syms -> nat }.
Class preds_signature := { preds : Type; ar_preds : preds -> nat }.
Class operators := { binop : Type ; quantop : Type }.

Coercion syms : funcs_signature >-> Sortclass.
Coercion preds : preds_signature >-> Sortclass.

Section Syntax.

  Context {Σ_funcs : funcs_signature}.

  Unset Elimination Schemes.

  Inductive function : nat -> Type :=
    | var_func : nat -> forall ar, function ar
    | sym : forall f : syms, function (ar_syms f).

  Inductive term : Type :=
    | var_indi : nat -> term
    | func {ar} (_ : function ar) (v : vec term ar) : term.

  Set Elimination Schemes.

  Context {Σ_preds : preds_signature}.

  Inductive predicate : nat -> Type :=
    | var_pred : nat -> forall ar, predicate ar
    | pred : forall P : preds, predicate (ar_preds P).

  Context {ops : operators}.

  Inductive form : Type :=
    | fal : form
    | atom : forall {ar}, predicate ar -> vec term ar -> form
    | bin : binop -> form -> form -> form
    | quant_indi : quantop -> form -> form
    | quant_func : quantop -> nat -> form -> form
    | quant_pred : quantop -> nat -> form -> form.

End Syntax.

Arguments var_func {_} _ {_}, {_} _ _.
Arguments var_pred {_} _ {_}, {_} _ _.



(* ** Instantiate logical operators to full SOL *)

Inductive full_logic_sym : Type :=
| Conj : full_logic_sym
| Disj : full_logic_sym
| Impl : full_logic_sym.

Inductive full_logic_quant : Type :=
| All : full_logic_quant
| Ex : full_logic_quant.

#[global]
Instance full_operators : operators :=
  {| binop := full_logic_sym ; quantop := full_logic_quant |}.



(* ** Tarski Semantics *)

Section Tarski.

  (* Environments *)
  Definition env_indi domain := nat -> domain.
  Definition env_func domain := nat -> forall ar, vec domain ar -> domain.
  Definition env_pred domain := nat -> forall ar, vec domain ar -> Prop.
  Record env domain := new_env { get_indi : env_indi domain ; get_func : env_func domain ; get_pred : env_pred domain }.
  Notation "⟨ a , b , c ⟩" := (new_env _ a b c).

  Arguments get_indi {_}.
  Arguments get_func {_}.
  Arguments get_pred {_}.

  (* Extension operation on environments:  We use a type class here to support the 
     same notation `x .: ρ` for individual, function, and predicate environments. *)
  Class Econs X Env := econs : X -> Env -> Env.
  Local Notation "x .: rho" := (econs x rho) (at level 70, right associativity).

  #[global] Instance econs_indi domain : Econs domain (nat -> domain) :=
    fun x env n => match n with  0 => x | S n => env n end.

  (* Extension for function and predicate environments needs to take arity into account. *)
  Definition econs_ar ar p : Econs (p ar) (nat -> forall ar, p ar) :=
    fun x env n => match n with
            | 0 => fun ar' => match Nat.eq_dec ar ar' with
                              | left e => match e in _ = ar' return p ar' with eq_refl => x end
                              | right _ => env n ar'
                              end
            | S n => fun ar' => if Nat.eq_dec ar ar' then env n ar' else env (S n) ar'
    end.
  #[global] Instance econs_func domain ar : Econs _ _ := econs_ar ar (fun ar => vec domain ar -> domain).
  #[global] Instance econs_pred domain ar : Econs _ _ := econs_ar ar (fun ar => vec domain ar -> Prop).

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Variable domain : Type.

  (* Interpretation of function and predicate symbols *)
  Class interp := B_I {
      i_f : forall f : syms, vec domain (ar_syms f) -> domain ;
      i_P : forall P : preds, vec domain (ar_preds P) -> Prop ;
  }.
  Context { I : interp }.

  Definition eval_function {ar} (rho : env domain) (f : function ar) : vec domain ar -> domain :=
    match f with
    | var_func f => get_func rho f _
    | sym f => i_f f
    end.

  Definition eval_predicate {ar} (rho : env domain) (P : predicate ar) : vec domain ar -> Prop :=
    match P with
    | var_pred P => get_pred rho P _
    | pred P => i_P P
    end.

  Fixpoint eval (rho : env domain) (t : term) : domain := 
    match t with
    | var_indi x => get_indi rho x
    | func f v => eval_function rho f (Vector.map (eval rho) v)
    end.

  Fixpoint sat (rho : env domain) (phi : form) : Prop :=
    match phi with
    | atom P v => eval_predicate rho P (Vector.map (eval rho) v)
    | fal => False
    | bin Impl phi psi => sat rho phi -> sat rho psi
    | bin Conj phi psi => sat rho phi /\ sat rho psi
    | bin Disj phi psi => sat rho phi \/ sat rho psi
    | quant_indi Ex phi => exists d : domain, sat ⟨d .: get_indi rho, get_func rho, get_pred rho⟩ phi
    | quant_indi All phi => forall d : domain, sat ⟨d .: get_indi rho, get_func rho, get_pred rho⟩ phi
    | quant_func Ex ar phi => exists (f : vec domain ar -> domain), sat ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ phi
    | quant_func All ar phi => forall (f : vec domain ar -> domain), sat ⟨get_indi rho, f .: get_func rho, get_pred rho⟩ phi
    | quant_pred Ex ar phi => exists (P : vec domain ar -> Prop), sat ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ phi
    | quant_pred All ar phi => forall (P : vec domain ar -> Prop), sat ⟨get_indi rho, get_func rho, P .: get_pred rho⟩ phi
    end.

End Tarski.


(* Boundle domain and interpretation into a model record *)
Record Model `{funcs_signature, preds_signature} := { 
  M_domain : Type ;
  M_interp : interp M_domain
}.

(* Allow to use a model M as a synonym for its domain and allow Coq 
   to find interpretations inside models automatically. This allows us
   to simply write `sat M rho phi`. *)
Coercion M_domain : Model >-> Sortclass.
#[global] Instance M_I `{funcs_signature, preds_signature} M : interp (M_domain M) := M_interp M.



(* ** Notations for SOL *)

Module SOLNotations.

  Notation "x .: rho" := (econs x rho) (at level 70, right associativity).

  Notation "$ x" := (var_indi x) (at level 5, format "$ '/' x").
  Notation "i$ x" := (var_indi x) (at level 5, format "i$ '/' x").
  Notation "f$ x" := (func (var_func x)) (at level 5, format "f$ '/' x").
  Notation "p$ x" := (atom (var_pred x)) (at level 5, format "p$ '/' x").

  Notation "⊥" := fal.
  Notation "A ∧ B" := (@bin _ _ full_operators Conj A B) (at level 41).
  Notation "A ∨ B" := (@bin _ _ full_operators Disj A B) (at level 42).
  Notation "A '~>' B" := (@bin _ _ full_operators Impl A B) (at level 43, right associativity).
  Notation "A '<~>' B" := ((A ~> B) ∧ (B ~> A)) (at level 43).
  Notation "¬ A" := (A ~> ⊥) (at level 40).

  Notation "∀i Phi" := (@quant_indi _ _ full_operators All Phi) (at level 50).
  Notation "∃i Phi" := (@quant_indi _ _ full_operators Ex Phi) (at level 50).
  Notation "∀f ( ar ) Phi" := (@quant_func _ _ full_operators All ar Phi) (at level 50).
  Notation "∃f ( ar ) Phi" := (@quant_func _ _ full_operators Ex ar Phi) (at level 50).
  Notation "∀p ( ar ) Phi" := (@quant_pred _ _ full_operators All ar Phi) (at level 50).
  Notation "∃p ( ar ) Phi" := (@quant_pred _ _ full_operators Ex ar Phi) (at level 50).

End SOLNotations.



(* ** Instantiate empty signature *)
#[global] Instance empty_funcs_sig : funcs_signature := {| syms := False; ar_syms := fun f => match f with end |}.
#[global] Instance empty_preds_sig : preds_signature := {| preds := False; ar_preds := fun P => match P with end |}.


(* ** List of decision problems *)

(* Validity of formulas *)
Definition SOL_valid (phi : form) := forall (M : Model) rho, sat M rho phi.

(* Satisfiability of formulas *)
Definition SOL_satis (phi : form) := exists (M : Model) rho, sat M rho phi.
