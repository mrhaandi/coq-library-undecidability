Require Import Undecidability.MinskyMachines.MM.
Require Import Undecidability.Shared.Libs.DLW.Code.sss Undecidability.Shared.Libs.DLW.Vec.pos.
(* Undecidability.MinskyMachines.Util.MM_sss Undecidability.MinskyMachines.MM.mm_defs. *)

From Coq Require Import List Vector.
Import ListNotations Vector.VectorNotations.

Definition eval n : (nat * list (mm_instr (pos n))) -> (nat * Vector.t nat n) -> (nat * Vector.t nat n) -> Prop :=
  fun '(i, P) '(c, v) '(c', v') => sss_output (@mma_sss _) (i, P) (c, v) (c', v').

Definition MMA_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists P : list (mm_instr (Fin.t (1 + k + n))),
    forall v : Vector.t nat k,
      (forall m, R v m <->
         exists c v', eval (1 + k + n) (1, P) (1, (0 :: v) ++ Vector.const 0 n) (c, m :: v')).
