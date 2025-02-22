(* * Peano Arithmetic *)
(* ** Signature *)

Require Export Undecidability.FOL.Utils.FullSyntax.
From Undecidability.Synthetic Require Import EnumerabilityFacts ListEnumerabilityFacts.
Import Vector.VectorNotations.
From Stdlib Require Import List.

(* ** Signature for PA axiomatisation, containing function symbols for set operations *)

#[global]
Existing Instance falsity_on.

Inductive PA_funcs : Type :=
  Zero : PA_funcs
| Succ : PA_funcs
| Plus : PA_funcs
| Mult : PA_funcs.

Definition PA_funcs_ar (f : PA_funcs ) :=
match f with
 | Zero => 0
 | Succ => 1
 | Plus => 2
 | Mult => 2
 end.

Definition PA_funcs_eq (x y:PA_funcs) : {x=y} + {x<>y}.
Proof. decide equality. Defined.

Inductive PA_preds : Type :=
  Eq : PA_preds.

Definition PA_preds_eq (x y:PA_preds) : {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition PA_preds_ar (P : PA_preds) :=
match P with
 | Eq => 2
end.


#[global]
Instance PA_funcs_signature : funcs_signature :=
{| syms := PA_funcs ; ar_syms := PA_funcs_ar |}.

#[global]
Instance PA_preds_signature : preds_signature :=
{| preds := PA_preds ; ar_preds := PA_preds_ar |}.

Definition enum_PA_funcs : nat -> option PA_funcs := (fun k => match k with
    | 0 => Some Zero
    | 1 => Some Succ
    | 2 => Some Plus
    | _ => Some Mult
    end).
Lemma enumerator_PA_funcs : enumerator__T enum_PA_funcs PA_funcs.
Proof.
  intros [].
  + now exists 0.
  + now exists 1.
  + now exists 2.
  + now exists 3.
Qed.
Lemma enumerable_PA_funcs : enumerable__T PA_funcs.
Proof.
  cbn. exists enum_PA_funcs. apply enumerator_PA_funcs.
Qed.

Definition enum_PA_preds : nat -> option PA_preds := (fun k => Some Eq).
Lemma enumerator_PA_preds : enumerator__T enum_PA_preds PA_preds.
Proof.
  intros []. now exists 0.
Qed.
Lemma enumerable_PA_preds : enumerable__T PA_preds.
Proof.
  exists enum_PA_preds. apply enumerator_PA_preds.
Qed.


Declare Scope PA_Notation.
Open Scope PA_Notation.

Notation "'zero'" := (@func PA_funcs_signature Zero ([])) (at level 1) : PA_Notation.
Notation "'σ' x" := (@func PA_funcs_signature Succ ([x])) (at level 32) : PA_Notation.
Notation "x '⊕' y" := (@func PA_funcs_signature Plus ([x ; y]) ) (at level 39) : PA_Notation.
Notation "x '⊗' y" := (@func PA_funcs_signature Mult ([x ; y]) ) (at level 38) : PA_Notation.
Notation "x '==' y" := (@atom PA_funcs_signature PA_preds_signature _ _ Eq ([x ; y])) (at level 40) : PA_Notation.

Section comparisons.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.

  Definition PAlt x y := ∃ y`[↑] == (σ x`[↑] ⊕ $0).
  Definition PAle x y := ∃ y`[↑] == (x`[↑] ⊕ $0).
  Definition PAle' x y := ∃ y`[↑] == ($0 ⊕ x`[↑]).

  Lemma PAlt_subst x y ρ : (PAlt x y)[ρ] = PAlt (x`[ρ]) (y`[ρ]).
  Proof.
    unfold PAlt. cbn. now asimpl.
  Qed.
  
  Lemma PAle_subst x y ρ : (PAle x y)[ρ] = PAle (x`[ρ]) (y`[ρ]).
  Proof.
    unfold PAle. cbn. now asimpl.
  Qed.

  Lemma PAle'_subst x y ρ : (PAle' x y)[ρ] = PAle' (x`[ρ]) (y`[ρ]).
  Proof.
    unfold PAle'. cbn. now asimpl.
  Qed.
End comparisons.

Notation "x '⧀' y"  := (PAlt x y) (at level 40) : PA_Notation.
Notation "x '⧀=' y"  := (PAle x y) (at level 40) : PA_Notation.
Notation "x '⧀='' y"  := (PAle' x y) (at level 40) : PA_Notation.
