(* Coppo-Dezani Intersection Type System *)
Require Import List.

(* strict types are of shape: a | (s1 /\ s2 /\ .. /\ sn -> t) *)
Inductive sty : Type :=
  | atom : nat -> sty
  | arr : sty -> list sty -> sty -> sty.

(* a type are (non-empty) list of strict types *)
Notation ty := (sty * list sty)%type.

(* de Bruijn terms are of shape: x | (M N) | \lambda. M *)
Inductive tm : Type :=
  | var : nat -> tm
  | app : tm -> tm -> tm
  | lam : tm -> tm.

(* strict type assignment system *)
Inductive type_assignment (Gamma : list ty) : tm -> sty -> Prop :=
  | type_assignment_var x s phi t :
      nth_error Gamma x = Some (s, phi) ->
      In t (s::phi) ->
      type_assignment Gamma (var x) t
  | type_assignment_app M N s phi t :
    type_assignment Gamma M (arr s phi t) ->
    type_assignment Gamma N s ->
    Forall (type_assignment Gamma N) phi ->
    type_assignment Gamma (app M N) t
  | type_assignment_arr M s phi t :
      type_assignment ((s, phi) :: Gamma) M t ->
      type_assignment Gamma (lam M) (arr s phi t).


(* Intersection Type Type Checking *)
Definition CD_TC : (list ty) * tm * sty -> Prop :=
  fun '(Gamma, M, t) => type_assignment Gamma M t.

(* Intersection Type Typability *)
Definition CD_TYP : tm -> Prop :=
  fun M => exists Gamma t, type_assignment Gamma M t.

(* Intersection Type Inhabitation *)
Definition CD_INH : (list ty) * sty -> Prop :=
  fun '(Gamma, t) => exists M, type_assignment Gamma M t.
