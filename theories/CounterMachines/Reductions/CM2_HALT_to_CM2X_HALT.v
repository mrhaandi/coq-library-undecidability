(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Reduction from:
    Two Counter Machine Halting (CM2_HALT)
  to:
    Two Counter Machine with Swap Halting (CM2X_HALT)
*)

Require Import List PeanoNat Lia.
Import ListNotations.

Require Undecidability.CounterMachines.CM2.
Require Undecidability.CounterMachines.CM2X.
Import CM2 (CM2_HALT). Import CM2X (CM2X_HALT).

From Undecidability.CounterMachines.Util Require Import 
  Nat_facts Facts.

From Undecidability.CounterMachines.Util Require CM2_facts.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Module CM2X_facts.

Import CM2X.

(* halting is monotone *)
Lemma halting_monotone {cm x} (n m: nat) : n <= m ->
  CM2X.steps cm n x = None -> CM2X.steps cm m x = None.
Proof.
  move=> ?. have -> : m = n + (m - n) by lia.
  rewrite /steps iter_plus=> ->. by rewrite oiter_None.
Qed.

End CM2X_facts.

Module Argument.
Import CM2 (Cm2).
Import CM2X (Cm2x).

Section CM2_CM2X.
  Variable (P: Cm2). (* CM2 program *)

  (* instruction index map *)
  Definition fs (i: nat) : nat := i*7.

  (* encode instruction at index i using index map fs for current cm2x index p *)
  Definition encode_instruction : CM2.Instruction * nat -> list CM2X.Instruction :=
    fun '(cm2i, i) => let p := fs i in
      match cm2i with
      | CM2.inc false => 
        [CM2X.inc; CM2X.inc; CM2X.inc; CM2X.dec (fs (1+i))] ++
        [CM2X.inc; CM2X.inc; CM2X.inc]
      | CM2.inc true => 
        [CM2X.inc; CM2X.inc; CM2X.dec (6 + fs i); CM2X.inc; CM2X.inc; CM2X.inc; CM2X.inc]
      | CM2.dec false j => 
        [CM2X.dec (4 + fs i)] ++
        [CM2X.inc; CM2X.dec (3 + fs i); CM2X.dec (fs (1+i))] ++
        [CM2X.inc; CM2X.dec (6 + fs i); CM2X.dec (fs j)]
      | CM2.dec true j => 
        [CM2X.inc; CM2X.dec (3 + fs i)] ++
        [CM2X.dec (6 + fs i)] ++
        [CM2X.dec (4 + fs i); CM2X.dec (fs j)] ++
        [CM2X.inc; CM2X.dec (fs (1+i))]
      end.

  Local Arguments encode_instruction : simpl never.
  
  (* two counter machine with swap encoding P *)
  Definition PX : list CM2X.Instruction :=
    flat_map encode_instruction (combine P (seq 0 (length P))).

  (* encode cm2 config as cm2x config *)
  Definition encode_config (x: CM2.Config) : CM2X.Config :=
    let '(i, (a, b)) := x in (fs i, (a * 2, b * 2)).

  Lemma length_encode_instruction {cm2i: CM2.Instruction} {i: nat} :
    length (encode_instruction (cm2i, i)) = 7.
  Proof. by move: cm2i => [] []. Qed.

  Lemma length_PX : length PX = (length P) * 7.
  Proof.
    rewrite /PX. elim: (P) (n in seq n _); first done.
    move=> ? ? IH n. 
    rewrite /= app_length (IH (S n)) length_encode_instruction. by lia. 
  Qed.

  Lemma seek_PX n {i} :
    nth_error PX (n + fs i) = 
    match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => 
      obind (fun cm2i => nth_error (encode_instruction (cm2i, i)) n) (nth_error P i)
    | _ => nth_error PX (n + fs i)
    end.
  Proof.
    rewrite /PX.
    suff : n < 7 -> forall k,
      nth_error (flat_map encode_instruction (combine P (seq k (length P)))) (n + fs i) =
    obind (fun cm2i : CM2.Instruction => nth_error (encode_instruction (cm2i, k + i)) n) (nth_error P i).
    { move: n => [|[|[|[|[|[|[|?]]]]]]]; last done.
      all: apply; by lia. }
    move=> Hn. elim: (P) i; first by move: n {Hn} => [|?] [|?] /=.
    move=> cm2i P' IH [|i] k /=.
    - by rewrite /fs ?Nat.add_0_r nth_error_app1 ?length_encode_instruction.
    - rewrite nth_error_app2 ?length_encode_instruction; first by (rewrite /fs; lia).
      have ->: n + fs (S i) - 7 = n + fs i by (rewrite /fs; lia).
      rewrite IH. move: (nth_error P' i) => [? /= |]; last done.
      by have ->: S (k + i) = k + S i by lia.
  Qed.

  Arguments nth_error : simpl never.
  
  Lemma fs_inj {i j: nat} : fs i = fs j -> i = j.
  Proof. rewrite /fs. by lia. Qed.

  (* PX simulates each step of P *)
  Lemma P_iff_PX {x: CM2.Config} : 
    Nat.iter 4 (obind (CM2X.step PX)) (Some (encode_config x)) = omap encode_config (CM2.step P x).
  Proof.
    move: x => [i [a b]] /=.
    move Hoi: (nth_error P i) => oi.
    rewrite /CM2.step.
    move: oi Hoi => [cm2i|] /=; first last.
    { move=> Hi. by rewrite (seek_PX 0) Hi /=. }
    move: cm2i => [] [] > Hi.
    (* case inc b *)
    - rewrite (seek_PX 0) Hi /=.
      rewrite (seek_PX 1) Hi /=.
      rewrite (seek_PX 2) Hi /=.
      by rewrite (seek_PX 6) Hi /=.
    (* case inc a *)
    - rewrite (seek_PX 0) Hi /=.
      rewrite (seek_PX 1) Hi /=.
      rewrite (seek_PX 2) Hi /=.
      by rewrite (seek_PX 3) Hi /=.
    (* case dec b *)
    - move: b => [|b].
      + rewrite (seek_PX 0) Hi /=.
        rewrite (seek_PX 1) Hi /=.
        rewrite (seek_PX 2) Hi /=.
        by rewrite (seek_PX 6) Hi /=.
      + rewrite (seek_PX 0) Hi /=.
        rewrite (seek_PX 1) Hi /=.
        rewrite (seek_PX 3) Hi /=.
        by rewrite (seek_PX 4) Hi /=.
    (* case dec a *)
    - move: a => [|a].
      + rewrite (seek_PX 0) Hi /=.
        rewrite (seek_PX 1) Hi /=.
        rewrite (seek_PX 2) Hi /=.
        by rewrite (seek_PX 3) Hi /=.
      + rewrite (seek_PX 0) Hi /=.
        rewrite (seek_PX 4) Hi /=.
        rewrite (seek_PX 5) Hi /=.
        by rewrite (seek_PX 6) Hi /=.
  Qed.
 
  (* P terminates iff PX terminates *)
  Lemma P_iff_PX_terminating (x: CM2.Config) {n}: 
    CM2.steps P n x = None <-> 
    CM2X.steps PX (n*4) (encode_config x) = None.
  Proof.
    elim: n x. { done. }
    move=> n. rewrite /CM2.steps /CM2X.steps.
    move=> IH x.
    have -> : S n = 1 + n by lia.
    have -> : (1 + n) * 4 = 4 + n * 4 by lia.
    rewrite iter_plus iter_plus P_iff_PX /=.
    case: (CM2.step P x).
    - done.
    - by rewrite /= ?oiter_None.
  Qed.

End CM2_CM2X.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* two counter machine halting many-one reduces to 
   two counter machine with swap halting *)
Theorem reduction : CM2_HALT ⪯ CM2X_HALT.
Proof.
  exists Argument.PX=> P. split.
  - move=> [n] /Argument.P_iff_PX_terminating ?.
    by exists (n * 4).
  - move=> [n]. have /CM2X_facts.halting_monotone : n <= n * 4 by lia.
    move=> /[apply] /(Argument.P_iff_PX_terminating _ (0, (0, 0))) ?.
    by exists n.
Qed.
