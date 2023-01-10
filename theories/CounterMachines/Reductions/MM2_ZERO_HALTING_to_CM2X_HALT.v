(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) TU Dortmund University, Dortmund, Germany
*)

(* 
  Reduction from:
    Two Counter Minsky Machine Halting (MM2_ZERO_HALTING)
  to:
    Two Counter Machine with Swap Halting (CM2X_HALT)
*)

Require Import List PeanoNat Lia Relations.
Import ListNotations.

Require Undecidability.MinskyMachines.MM2.
Require Import Undecidability.MinskyMachines.Util.MM2_facts.
Require Undecidability.CounterMachines.CM2X.
Import MM2 (MM2_ZERO_HALTING). Import CM2X (CM2X_HALT).

Require Import Undecidability.Shared.deterministic_simulation.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

Module Argument.
Import MM2 (mm2_instr).
#[local] Notation mm2_state := (nat*(nat*nat))%type.
Import CM2X (Cm2x).

Section CM2_CM2X.
  Variable (P: list mm2_instr). (* MM2 program *)

  (* instruction index map *)
  Definition fs (i: nat) : nat := if i is S j then j*7 else (length P)*7.

  (* encode instruction at index i using index map fs for current cm2x index p *)
  Definition encode_instruction : mm2_instr * nat -> list CM2X.Instruction :=
    fun '(cm2i, i) => let p := fs i in
      match cm2i with
      | MM2.mm2_inc_a =>
        [CM2X.inc; CM2X.inc; CM2X.inc; CM2X.dec (fs (1+i))] ++
        [CM2X.inc; CM2X.inc; CM2X.inc]
      | MM2.mm2_inc_b =>
        [CM2X.inc; CM2X.inc; CM2X.dec (6 + fs i); CM2X.inc; CM2X.inc; CM2X.inc; CM2X.inc]
      | MM2.mm2_dec_a j =>
        [CM2X.dec (4 + fs i)] ++
        [CM2X.inc; CM2X.dec (3 + fs i); CM2X.dec (fs (1+i))] ++
        [CM2X.inc; CM2X.dec (6 + fs i); CM2X.dec (fs j)]
      | MM2.mm2_dec_b j =>
        [CM2X.inc; CM2X.dec (3 + fs i)] ++
        [CM2X.dec (6 + fs i)] ++
        [CM2X.dec (4 + fs i); CM2X.dec (fs j)] ++
        [CM2X.inc; CM2X.dec (fs (1+i))]
      end.

  Local Arguments encode_instruction : simpl never.
  
  (* two counter machine with swap encoding P *)
  Definition PX : list CM2X.Instruction :=
    flat_map encode_instruction (combine P (seq 1 (length P))).

  (* encode cm2 config as cm2x config *)
  Definition encode_config (x: mm2_state) : CM2X.Config :=
    let '(i, (a, b)) := x in (fs i, (a * 2, b * 2)).

  Lemma length_encode_instruction {cm2i: mm2_instr} {i: nat} :
    length (encode_instruction (cm2i, i)) = 7.
  Proof. by case: cm2i. Qed.

  Lemma length_PX : length PX = (length P) * 7.
  Proof.
    rewrite /PX. elim: (P) (n in seq n _); first done.
    move=> ? ? IH n. 
    rewrite /= app_length (IH (S n)) length_encode_instruction. by lia.
  Qed.

  Lemma seek_PX n {i} :
    nth_error PX (n + fs (S i)) = 
    match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => 
      obind (fun cm2i => nth_error (encode_instruction (cm2i, S i)) n) (nth_error P i)
    | _ => nth_error PX (n + fs (S i))
    end.
  Proof.
    rewrite /PX.
    suff : n < 7 -> forall k,
      nth_error (flat_map encode_instruction (combine P (seq k (length P)))) (n + fs (S i)) =
    obind (fun cm2i : mm2_instr => nth_error (encode_instruction (cm2i, k + i)) n) (nth_error P i).
    { move: n => [|[|[|[|[|[|[|?]]]]]]]; last done.
      all: apply; by lia. }
    move=> Hn. elim: (P) i; first by move: n {Hn} => [|?] [|?] /=.
    move=> cm2i P' IH [|i] k /=.
    - by rewrite /fs ?Nat.add_0_r nth_error_app1 ?length_encode_instruction.
    - rewrite nth_error_app2 ?length_encode_instruction; first by (rewrite /fs; lia).
      have ->: n + S (S (S (S (S (S (S (i * 7))))))) - 7 = n + fs (S i) by (rewrite /fs; lia).
      rewrite IH. move: (nth_error P' i) => [? /= |]; last done.
      by have ->: S (k + i) = k + S i by lia.
  Qed.

  Arguments nth_error : simpl never.
  
  #[local] Notation sync := (fun x x' => encode_config x = x').
  #[local] Notation step2 := (fun x y => CM2X.step PX x = Some y).

  Lemma step2_det s' t1' t2' : step2 s' t1' -> step2 s' t2' -> t1' = t2'.
  Proof. by move=> /= -> []. Qed.

  Lemma init_sync : sync (1, (0, 0)) (0, (0, 0)).
  Proof. cbn. reflexivity. Qed.

  Lemma CM2X_HALT_spec : terminates step2 (0, (0, 0)) <-> CM2X_HALT PX.
  Proof.
    split.
    - move=> /(terminating_Acc step2_det). rewrite /CM2X_HALT.
      move: (0, (0, 0)) => ?. elim.
      move=> x' _ IH. case E: (CM2X.step PX x') => [y'|].
      + move: (E) => /IH [] k ?. exists (k+1).
        rewrite /CM2X.steps /Nat.iter nat_rect_plus.
        by rewrite -?/(Nat.iter _ _ _) /= E.
      + by exists 1.
    - move=> [k]. elim: k (0, (0, 0)).
      + done.
      + move=> k IH x.
        have -> : S k = k + 1 by lia.
        rewrite /CM2X.steps /Nat.iter nat_rect_plus -?/(Nat.iter _ _ _) /=.
        case E: (CM2X.step PX x) => [y|].
        * move=> /IH. apply: terminates_extend. by apply: rt_step.
        * move=> _. exists x. split; [apply: rt_refl|].
          move=> y. by rewrite E.
  Qed.

  Lemma P_to_PX (s t s' : mm2_state) :
    MM2.mm2_step P s t -> encode_config s = s' ->
    exists t' : mm2_state, clos_trans mm2_state step2 s' t' /\ encode_config t = t'.
  Proof.
    move=> [instr] [+ H] <-.
    case: H => i => [a b|a b|j a b|j a b|j b|j a] /=.
    all: move=> /[dup] /mm2_instr_at_pos -> /nth_error_Some_mm2_instr_at_iff Hi.
    all: eexists; split; [|reflexivity].
    - apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 0) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 1) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 2) Hi. }
      apply: t_step. by rewrite /= (seek_PX 3) Hi.
    - apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 0) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 1) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 2) Hi. }
      apply: t_step. by rewrite /= (seek_PX 6) Hi.
    - apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 0) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 4) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 5) Hi. }
      apply: t_step. by rewrite /= (seek_PX 6) Hi.
    - apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 0) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 1) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 3) Hi. }
      apply: t_step. by rewrite /= (seek_PX 4) Hi.
    - apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 0) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 1) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 2) Hi. }
      apply: t_step. by rewrite /= (seek_PX 3) Hi.
    - apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 0) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 1) Hi. }
      apply: t_trans; [apply: t_step|]. { by rewrite /= (seek_PX 2) Hi. }
      apply: t_step. by rewrite /= (seek_PX 6) Hi.
  Qed.

  Lemma transport : MM2_ZERO_HALTING P -> CM2X_HALT PX.
  Proof.
    move=> H. apply /CM2X_HALT_spec. apply: terminates_transport init_sync H.
    - by apply: P_to_PX.
    - move=> x x' /mm2_stop_index_iff Hx <-. move: x Hx => [i [a b]] /= [->|].
      + eexists. split; [apply: rt_refl|].
        move=> y' /=.
        suff: nth_error PX (length P * 7) = None by move ->.
        apply /nth_error_None. rewrite length_PX. lia.
      + move: i => [|i]; [lia|].
        eexists. split; [apply: rt_refl|].
        move=> y' /=.
        suff: nth_error PX (i * 7) = None by move ->.
        apply /nth_error_None. rewrite length_PX. lia.
  Qed.

  Lemma reflection : CM2X_HALT PX -> MM2_ZERO_HALTING P.
  Proof.
    move=> /CM2X_HALT_spec. apply: terminates_reflection init_sync.
    - apply: step2_det.
    - by apply: P_to_PX.
    - move=> ?. apply: mm2_exists_step_dec.
  Qed.

End CM2_CM2X.
End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* two counter machine halting many-one reduces to 
   two counter machine with swap halting *)
Theorem reduction : MM2_ZERO_HALTING ⪯ CM2X_HALT.
Proof.
  exists Argument.PX=> P. split.
  - apply Argument.transport.
  - apply Argument.reflection.
Qed.
