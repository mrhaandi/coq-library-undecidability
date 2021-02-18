(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Two Counter Machine with Swap Halting (CM2X_HALT)
*)

(*
  Literature:
  [1, Problem 14.2-2] Minsky, Marvin Lee. Computation. Englewood Cliffs: Prentice-Hall, 1967.
*)

Require Import List.

(* a configuration consists of a program index and two counter values *)
Record Config : Set := mkConfig { index : nat; value1 : nat; value2 : nat }.

(* the instruction inc maps 
      a configuration (i, (a, b)) to (1+i, (b, 1+a))
    an instruction dec j maps
      a configuration (i, (0, b)) to (1+i, (b, 0)) 
      a configuration (i, (1+a, b)) to (j, (b, a))  *)
Inductive Instruction : Set := 
  | inc : Instruction
  | dec : nat -> Instruction.

(* a two counter machine with swap is a list of instructions *)
Definition Cm2x : Set := list Instruction.

(* two counter machine with swap step function *)
Definition step (M: Cm2x) (x: Config) : Config :=
  match nth_error M (index x) with
  | None => x (* halting configuration *)
  | Some inc => (* increase counter, swap, goto next state*)
    {| index := 1 + (index x); value1 := value2 x; value2 := 1 + (value1 x) |}
  | Some (dec j) => (* decrease counter, swap, if successful goto index j *)
    match value1 x with
    | 0 => {| index := 1 + (index x); value1 := value2 x; value2 := 0 |}
    | S n => {| index := j; value1 := value2 x; value2 := n |}
    end
  end.
(* unfold step if the configuration is decomposed *)
Arguments step _ !x /.

(* halting configuration property *)
Definition halting (M : Cm2x) (x: Config) : Prop := step M x = x.

(* Two Counter Machine Halting Problem *)
Definition CM2X_HALT : Cm2x -> Prop :=
  fun M => exists (n: nat), 
    halting M (Nat.iter n (step M) {| index := 0; value1 := 0; value2 := 0 |}).
