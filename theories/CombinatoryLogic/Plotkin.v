(*
  [1] Plotkin, Gordon "Call-by-name, call-by-value and the λ-calculus." Theoretical computer science 1.2 (1975): 125-159.
*)

From Undecidability Require L.L.
Require Import List Lia.
Import L.
From Undecidability Require Import L.Util.L_facts.
From Undecidability Require L.Computability.Seval.
Require Import Relations.

From Undecidability Require Import CombinatoryLogic.Krivine.

Require Import ssreflect ssrbool ssrfun.
   
(* left-most outer-most call-by-name *)
Inductive step : term -> term -> Prop :=
  | stepLam s t    : step (app (lam s) t) (subst s 0 t)
  | stepApp s s' t : step s s' -> step (app s t) (app s' t).

  (* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

Fixpoint ren (xi : nat -> nat) (t : term) : term  :=
  match t with
  | var x => var (xi x)
  | app s t => app (ren xi s) (ren xi t)
  | lam t => lam (ren (scons 0 (funcomp S xi)) t)
  end.

Fixpoint cbv_cbn (t : term) : term :=
  match t with
  | var n => lam (app (var 0) (var (S n)))
  | app s t => lam (app (ren S (cbv_cbn s)) (lam (app (ren S (ren S (cbv_cbn t))) (lam (app (app (var 1) (var 0)) (var 2))))))
  | lam s => lam (app (var 0) (ren S (lam (cbv_cbn s))))
  end.

Definition Psi (t : term) :=
  match t with
  | var n => var n
  | app s t => app s t
  | lam s => ren S (lam (cbv_cbn s))
  end.

Lemma subst_ren s k t : subst (ren S s) (S k) t = ren S (subst s k t).
Proof. Admitted. (* needs closedness *)

Lemma lemma_6_1 M N k : 
  subst (cbv_cbn M) k (Psi (lam N)) = cbv_cbn (subst M k (lam N)).
Proof.
  elim: M k N.
  - move=> /= n k N. case: (Nat.eqb n k).
    + done.
    + done.
  - move=> s IH1 t IH2 k N /=.
    rewrite !subst_ren.
    by rewrite IH1 IH2.
  - move=> s IH k N /=.
    rewrite -IH.
    congr lam. congr app. congr lam.
    cbn.
Admitted.

Definition on_app {X : Type} (s : term) (x : X) (g : term -> term -> X) : X :=
  match s with
  | app s t => g s t
  | _ => x
  end.

(* plotkins M : K *)
Fixpoint colon (M : term) (u : term) : term :=
  on_app M (
    app u (Psi M)
  ) (
    fun s t =>
      on_app s (
        on_app t (
          app (app (Psi s) (Psi t)) u
        ) (
          fun t1 t2 => app (Psi t) (lam (app (app (app (var 0) (Psi s)) (var 0)) u))
        )
      ) (
        fun s1 s2 => colon s (lam (app (cbv_cbn t) (lam (app (app (var 1) (var 0)) u))))
      )
  ).


Lemma lemma_6_2 s u : closed (lam u) -> halt_cbn [] [] (colon s u) -> halt_cbn [] [] (app (cbv_cbn s) u).
Proof.
  move=> Hu. elim: s.
  - move=> n /=.
    move=> /halt_cbnE H'.
    do ? constructor.
    apply: (halt_cbn_flatten_iff H').


Lemma main s t : s ≻ t -> 
  halt_cbn [] [] (app (cbv_cbn s) (lam (var 0))) -> 
  halt_cbn [] [] (app (cbv_cbn t) (lam (var 0))).
Proof.
  elim; clear s t.
  - move=> s t /=.
    do 17 (move=> /halt_cbnE).
    move=> H'.

  move=> /eval_iff.
  elim. elim.
  { admit. }

  move=> > []. 

Lemma test :=
