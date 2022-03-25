Require Import Undecidability.IntersectionTypes.CD.
Require Import Undecidability.CounterMachines.CM2X.

Require Import Undecidability.IntersectionTypes.Util.CD_facts.

Require Import List Relations.
Import ListNotations.
Import CD (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Section Argument.

Context (P : Cm2x).

(* Scott encoding of nat *)
Fixpoint enc_nat n :=
  match n with
  | 0 => lam (lam (var 1))
  | S n => lam (lam (app (var 0) (enc_nat n)))
  end.

Definition enc_tab i k :=
  Nat.iter (S k) lam (if (Nat.ltb i k) then var i else var k).

Notation tm_steps := (clos_refl_trans tm CD_facts.step).

Lemma enc_tab_spec2 i k Ms N : length Ms = k ->
  k <= i ->
  tm_steps (fold_right (fun M2 M1 => app M1 M2) (app (enc_tab i k) N) Ms) N.
Proof.
  ?

Lemma enc_tab_spec i k Ms N : length Ms = k ->
  tm_steps (fold_right (fun M2 M1 => app M1 M2) (app (enc_tab i k) N) Ms ) (nth i Ms N).
Proof.
  elim: Ms k i.
  { move=> [|?]; last done. rewrite /enc_tab. move=> [|i] _ /=.
    all: by apply: rt_step; apply: stepRed. }
  
  move=> M Ms IH [|k] i /=; first done.
  move=> [/IH] {}IH.
  move: i => [|i].
  - admit.
  - 



(* Scott encoding of option *)
Definition enc_option {X : Type} (e : X -> tm) (o : option X) :=
  match o with
  | None => lam (lam (var 1))
  | Some x => lam (lam (app (var 0) (e x)))
  end.

Definition enc_nat3 i a b :=
  lam (app (app (app (var 0) (enc_nat i)) (enc_nat a)) (enc_nat b)).

