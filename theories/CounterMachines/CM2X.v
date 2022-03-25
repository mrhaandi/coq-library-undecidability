(* 
  Problem(s):
    Two Counter Machine with Swap Halting (CM2X_HALT)

  Literature:
    [1, Problem 14.2-2] Minsky, Marvin Lee. Computation. Englewood Cliffs: Prentice-Hall, 1967.
*)

Require Import List ssrfun.

(* a configuration consists of a program index and two counter values *)
Notation Config := (nat * (nat * nat))%type.

(* the instruction inc maps 
      a configuration (i, (a, b)) to (1+i, (b, 1+a))
    an instruction dec j maps
      a configuration (i, (0, b)) to (1+i, (b, 0)) 
      a configuration (i, (1+a, b)) to (j, (b, a))  *)
Inductive Instruction : Set := 
  | inc : Instruction
  | dec : nat -> Instruction.

(* a two counter machine with swap is a list of instructions *)
Notation Cm2x := (list Instruction).

(* two counter machine with swap step function *)
Definition step (M: Cm2x) (x: Config) : option Config :=
  let '(i, (a, b)) := x in
  match nth_error M i with
  | None => None (* halting configuration *)
  | Some inc => Some (1+i, (b, 1+a))
  | Some (dec j) => Some (
    match a with
    | 0 => (1+i, (b, 0))
    | S n => (j, (b, n))
    end)
  end.

(* unfold step if the configuration is decomposed *)
Arguments step _ !x /.

(* iterated partial two-counter machine step function *)
Definition steps (M: Cm2x) (k: nat) (x: Config) : option Config :=
  Nat.iter k (obind (step M)) (Some x).

(* configuration reachability *)
Definition reaches (M: Cm2x) (x y: Config) :=
  exists k, steps M k x = Some y.

(* does M eventually terminate starting from the configuration x? *)
Definition terminating (M: Cm2x) (x: Config) :=
  exists k, steps M k x = None.

(* Two-counter Machine with Swap Halting:
   Given a two-counter machine with swap M,
   does a run in M starting from configuration (0, (0, 0)) eventually halt? *)
Definition CM2X_HALT : Cm2x -> Prop :=
  fun M => terminating M (0, (0, 0)).
