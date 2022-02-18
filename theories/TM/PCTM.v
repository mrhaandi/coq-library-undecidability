(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import sss.

From Undecidability.TM
  Require Import SBTM.

Import SBTMNotations (tape).

Set Implicit Arguments.

(** * Halting problem for (micro-programmed) Turing machines with a PC counter *)

Inductive pctm_instr : Set :=
  | pctm_mv  : direction -> pctm_instr
  | pctm_wr  : bool -> pctm_instr
  | pctm_jz  : nat -> pctm_instr
  | pctm_jmp : nat -> pctm_instr.

Module PCTMNotations.

  Notation MV  := pctm_mv.
  Notation WR  := pctm_wr.
  Notation JZ  := pctm_jz.
  Notation JMP := pctm_jmp.

  Definition rd (t : tape) : bool := let '(_,b,_) := t in b.
  Definition wr (t : tape) b : tape := let '(l,_,r) := t in (l,b,r).

End PCTMNotations.

Import PCTMNotations SBTMNotations.

(* ** Semantics for PC based TM *)

Section PC_based_Single_Tape_Turing_Machine.

  Definition pctm_state := (nat*tape)%type.

  Inductive pctm_sss : pctm_instr -> pctm_state -> pctm_state -> Prop :=
    | pctm_sss_mv d i t :   MV d // (i,t) -1> (1+i,mv d t)       (* From the SBTM.v *)
    | pctm_sss_wr b i t :   WR b // (i,t) -1> (1+i,wr t b)
    | pctm_sss_jz i j t :   JZ j // (i,t) -1> (if rd t then 1+i else j,t)
    | pctm_sss_jmp i j t : JMP j // (i,t) -1> (j,t)
  where "i // s -1> t" := (pctm_sss i s t).

End PC_based_Single_Tape_Turing_Machine.

(* The Halting problem for PCTM *)
  
Definition PCTM_PROBLEM := (list pctm_instr * tape)%type.

#[local] Notation "P // s ↓" := (sss_terminates pctm_sss P s).

Definition PCTM_HALT (Q : PCTM_PROBLEM) := let (P,t) := Q in (1,P) // (1,t) ↓.
