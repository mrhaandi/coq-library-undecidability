(* Coppo-Dezani-Venneri Intersection Type System *)
Require Import List.

(* strict types are of shape: a | (t1 /\ .. /\ tn -> t) *)
Inductive sty : Type :=
  | atom : nat -> sty
  | arr : list sty -> sty -> sty.

(* a type are (possibly empty) list of strict types *)
Notation ty := (list sty).

(* de Bruijn terms are of shape: x | (M N) | \lambda. M *)
Inductive tm : Type :=
  | var : nat -> tm
  | app : tm -> tm -> tm
  | lam : tm -> tm.

(* strict type assignment system *)
Inductive type_assignment (Gamma : list ty) : tm -> sty -> Prop :=
  | type_assignment_var x t :
      In t (nth x Gamma nil) ->
      type_assignment Gamma (var x) t
  | type_assignment_arr M phi t :
      type_assignment (phi :: Gamma) M t ->
      type_assignment Gamma (lam M) (arr phi t)
  | type_assignment_app M N phi t :
      type_assignment Gamma M (arr phi t) ->
      Forall (type_assignment Gamma N) phi ->
      type_assignment Gamma (app M N) t.

(* Intersection Type Checking *)
Definition CDV_TC : (list ty) * tm * sty -> Prop :=
  fun '(Gamma, M, t) => type_assignment Gamma M t.

(* Intersection Type Typability *)
Definition CDV_TYP : tm -> Prop :=
  fun M => exists Gamma t, type_assignment Gamma M t.

(* Intersection Type Inhabitation *)
Definition CDV_INH : (list ty) * sty -> Prop :=
  fun '(Gamma, t) => exists M, type_assignment Gamma M t.
