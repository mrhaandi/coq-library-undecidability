(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(*
  Synopsis:
    Invertible injection "encode_term" from "term" to "nat".
*)

Require Import Undecidability.SemiUnification.HOSemiU.
Require Import Undecidability.SemiUnification.autosubst.pts.

Require Import Lia.
Require Import ssreflect ssrbool ssrfun.

Module EncodeNat.

(* bijection from nat * nat to nat *)
Definition encode_nat '(x, y) : nat := 
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(* bijection from nat to nat * nat *)
Definition decode_nat (n : nat) : nat * nat := 
  nat_rec _ (0, 0) (fun _ '(x, y) => if x is S x then (x, S y) else (S y, 0)) n.

Lemma encode_nat_non_decreasing (x y: nat) : x + y <= encode_nat (x, y).
Proof. elim: x=> [| x IH] /=; [| rewrite PeanoNat.Nat.add_succ_r /=]; by lia. Qed.

Lemma encode_decode_nat {xy: nat * nat} : decode_nat (encode_nat xy) = xy.
Proof.
  move Hn: (encode_nat xy) => n. elim: n xy Hn.
  { by move=> [[|?] [|?]]. }
  move=> n IH [x [|y [H]]] /=.
  { move: x => [|x [H]] /=; first done.
    by rewrite (IH (0, x)) /= -?H ?PeanoNat.Nat.add_0_r. }
  by rewrite (IH (S x, y)) /= -?H ?PeanoNat.Nat.add_succ_r.
Qed.

End EncodeNat.

Import EncodeNat.
Opaque encode_nat decode_nat.

(* injectively encode a term as a natural number *)
Fixpoint encode_term (P: term) : nat :=
  match P with
  | var x => encode_nat (0, x)
  | const c => encode_nat (1, c) 
  | app P Q => encode_nat (2, (encode_nat (encode_term P, encode_term Q))) 
  | lam P Q => encode_nat (3, (encode_nat (encode_term P, encode_term Q))) 
  | Pi P Q => encode_nat (4, (encode_nat (encode_term P, encode_term Q))) 
  end.

Fixpoint decode_term' (k n: nat) : term :=
  match k with
  | 0 => var 0
  | S k =>
    match decode_nat n with
    | (0, x) => var x
    | (1, c) => const c
    | (2, m) => let (m1, m2) := decode_nat m in
      app (decode_term' k m1) (decode_term' k m2)
    | (3, m) => let (m1, m2) := decode_nat m in
      lam (decode_term' k m1) (decode_term' k m2)
    | (4, m) => let (m1, m2) := decode_nat m in
      Pi (decode_term' k m1) (decode_term' k m2)
    | _ => var 0
    end
  end.

(* uniquely decode a term from a natural number *)
Definition decode_term (n: nat) := decode_term' (S n) n.

Lemma encode_decode_term (P: term) : decode_term (encode_term P) = P.
Proof.
  rewrite /decode_term. 
  suff : (forall k, encode_term P < k -> decode_term' k (encode_term P) = P) by apply.
  move=> k. elim: k P; first by lia.
  move=> k IH [] => /=.
  - move=> ?. by rewrite encode_decode_nat.
  - move=> ?. by rewrite encode_decode_nat.
  - move=> P Q ?.
    have ? := encode_nat_non_decreasing 2 (encode_nat (encode_term P, encode_term Q)).
    have ? := encode_nat_non_decreasing (encode_term P) (encode_term Q).
    rewrite ?encode_decode_nat. congr app; apply: IH; by lia.
  - move=> P Q ?.
    have ? := encode_nat_non_decreasing 3 (encode_nat (encode_term P, encode_term Q)).
    have ? := encode_nat_non_decreasing (encode_term P) (encode_term Q).
    rewrite ?encode_decode_nat. congr lam; apply: IH; by lia.
  - move=> P Q ?.
    have ? := encode_nat_non_decreasing 4 (encode_nat (encode_term P, encode_term Q)).
    have ? := encode_nat_non_decreasing (encode_term P) (encode_term Q).
    rewrite ?encode_decode_nat. congr Pi; apply: IH; by lia.
Qed.

Opaque encode_term decode_term.
