(* plotkin call by value call by name and lambda calculus *)

From Undecidability Require L.L.
Require Import List Lia.
Import L.
From Undecidability Require Import L.Util.L_facts.
From Undecidability Require L.Computability.Seval.
Require Import Relations.
Require Import ssreflect ssrbool ssrfun.

Inductive eterm := closure : list eterm -> term -> eterm.

(* actual krivine machine
https://en.wikipedia.org/wiki/Krivine_machine *)
Inductive halt_cbn : list eterm -> list eterm -> term -> Prop :=
  | halt_var_0 ts ctx t ctx' :
      halt_cbn ts ctx t ->
      halt_cbn ts ((closure ctx t)::ctx') (var 0)
  | halt_var_S ts ctx n t :
      halt_cbn ts ctx (var n) ->
      halt_cbn ts (t::ctx) (var (S n))
  | halt_app ts ctx s t :
      halt_cbn ((closure ctx t)::ts) ctx s ->
      halt_cbn ts ctx (app s t)
  | halt_lam_ts t ts ctx s :
      halt_cbn ts (t::ctx) s ->
      halt_cbn (t::ts) ctx (lam s)
  | halt_lam ctx s :
      halt_cbn [] ctx (lam s).

Lemma halt_cbnE ts ctx u : halt_cbn ts ctx u ->
  match u with
  | var 0 =>
      match ctx with
      | [] => False
      | (closure ctx' t')::_ => halt_cbn ts ctx' t'
      end
  | var (S n) => 
      match ctx with
      | [] => False
      | _::ctx' => halt_cbn ts ctx' (var n)
      end
  | app s t => halt_cbn ((closure ctx t) :: ts) ctx s
  | lam s =>
      match ts with
      | [] => True
      | t'::ts' => halt_cbn ts' (t'::ctx) s
      end
  end.
Proof. by case. Qed.
    
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
  | app s t => lam (app (ren S (cbv_cbn  s)) (lam (app (ren S (ren S (cbv_cbn t))) (lam (app (app (var 1) (var 0)) (var 2))))))
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

Lemma subst_main M N k : 
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

    done.
    + done.
    + done. cbn. done. 

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
