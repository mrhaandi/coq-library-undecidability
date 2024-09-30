From Undecidability Require Import TM.TM.
From Undecidability.MinskyMachines Require Import MMA MMA.mma_defs Util.MMA_computable.

From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Undecidability.Shared.simulation.

Require Import List PeanoNat Lia Relations.
Import ListNotations.

Require Import ssreflect.

Set Default Goal Selector "!".

#[local] Notation "P // s ~~> t" := (sss_output (@mma_sss _) P s t).
#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).

Lemma sss_compute_iff {n P s t} : P // s ->> t <-> clos_refl_trans _ (sss_step (@mma_sss n) P) s t.
Proof.
  split.
  - case=> k. elim: k s.
    { move=> ? /sss_steps_0_inv <-. by apply: rt_refl. }
    move=> ? IH ? H. inversion H.
    by apply: rt_trans; [apply: rt_step|apply: IH]; eassumption.
  - move=> /clos_rt_rt1n_iff. elim.
    { move=> ?. exists 0. by constructor. }
    move=> > ? _ ?. apply: sss_compute_trans; [|eassumption].
    exists 1. by econstructor; [eassumption|constructor].
Qed.

Lemma in_code_step {n s P} :
  subcode.in_code (fst s) P ->
  exists t, sss_step (@mma_sss n) P s t.
Proof.
  move: s P => [i v] [offset P] /= ?.
  case E: (nth_error P (i - offset)) => [instr|]; first last.
  { move=> /nth_error_None in E. cbn in *. lia. }
  have [t Ht] := mma_sss_total_ni instr (i, v).
  move: E => /(nth_error_split P) [?] [?] [->] Hi.
  eexists t, offset, _, instr, _, v.
  split; [done|split; [|eassumption]].
  congr pair. lia.
Qed.

Lemma out_code_iff {n s P} : subcode.out_code (fst s) P <-> simulation.stuck (sss_step (@mma_sss n) P) s.
Proof.
  split.
  - move=> /sss_steps_stall H t /in_sss_steps_S H'.
    by have /H' /H [] : sss_steps (mma_sss (n:=n)) P 0 t t by apply: in_sss_steps_0.
  - have [|] := subcode.in_out_code_dec (fst s) P; [|done].
    move=> /in_code_step [t] ? Hs. exfalso. by apply: (Hs t).
Qed.

Lemma sss_step_or_stuck {n} p i P :
  (exists q, sss_step (@mma_sss n) (i, P) p q) \/ simulation.stuck (sss_step (@mma_sss n) (i, P)) p.
Proof.
  have [|] := subcode.in_out_code_dec (fst p) (i, P).
  - move=> /in_code_step ?. by left.
  - move=> /out_code_iff ?. by right.
Qed.

Lemma sss_terminates_iff {n s P} : sss_terminates (@mma_sss n) P s <-> simulation.terminates (sss_step (@mma_sss n) P) s.
Proof.
  split.
  - move=> [t] [/sss_compute_iff ? /out_code_iff ?]. by exists t.
  - move=> [t] [/sss_compute_iff ? /out_code_iff ?]. by exists t.
Qed.
