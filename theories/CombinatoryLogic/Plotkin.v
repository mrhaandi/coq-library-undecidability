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
  | lam s => lam (cbv_cbn s)
  end.

(*
Lemma subst_ren s k t : subst (ren S s) (S k) t = ren S (subst s k t).
Proof. Admitted. (* needs closedness *)
*)

Lemma lemma_6_1 s k t : closed (lam t) ->
  cbv_cbn (L.subst s k (lam t)) = L.subst (cbv_cbn s) k (Psi (lam t)).
Proof.
  move=> Ht. elim: s k.
  - move=> n k /=. case: (Nat.eqb n k); last done.
    move=> /=. congr lam. congr app. congr lam. admit. (* use closedness *)
  - move=> s1 IH1 s2 IH2 k /=. rewrite IH1 IH2 /=.
    congr lam. congr app.
    + admit.
    + congr lam. congr app. admit.
  - move=> s IH k /=. rewrite IH /=.
    congr lam. congr app. congr lam.
    admit.
Admitted.

(*
Lemma lemma_6_1 M N :
  subst (scons (Psi (lam N)) var) (cbv_cbn M) = cbv_cbn (subst (scons (lam N) var) M).
Proof.
  (* maybe point subst is better ?  *)
Admitted.
*)
(*
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
*)

Definition on_app {X : Type} (s : term) (x : X) (g : term -> term -> X) : X :=
  match s with
  | app s t => g s t
  | _ => x
  end.

Definition is_app (s: term) : bool :=
  if s is app _ _ then true else false.

Fixpoint colon (M : term) (u : term) : term :=
  match M with
  | var _ => app u (Psi M)
  | lam _ => app u (Psi M)
  | app s t =>
      if is_app s then
        colon s (lam (app (ren S (cbv_cbn t)) (lam (app (app (var 1) (var 0)) (ren S (ren S u))))))
      else
        if is_app t then
          colon t (lam (app (app (ren S (Psi s)) (var 0)) (ren S u)))
        else
          app (app (Psi s) (Psi t)) u
  end.

(* plotkins M : K *)
(*
Fixpoint colon (M : term) (u : term) : term :=
  on_app M (
    app u (Psi M)
  ) (
    fun s t =>
      on_app s (
        on_app t (
          app (app (Psi s) (Psi t)) u
        ) (
          fun t1 t2 => colon t (lam (app (app (ren S (Psi s)) (var 0)) (ren S u)))
        )
      ) (
        fun s1 s2 => colon s (lam (app (ren S (cbv_cbn t)) (lam (app (app (var 1) (var 0)) (ren S (ren S u))))))
      )
  ).

Arguments colon : simpl never.
*)

Lemma colon_var_app n t1 t2 u : colon (app (var n) (app t1 t2)) u = colon (app t1 t2) (lam (app (app (ren S (Psi (var n))) (var 0)) (ren S u))).
Proof. done. Qed.
  (*
Lemma ren_const_ren m xi t : ren (fun=> m) (ren xi t) = ren (fun=> m) t.
Proof. by rewrite ren_ren_term. Qed.
*)

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Arguments cbv_cbn: simpl never.


(* drop closedness? 
Lemma lemma_6_2 s u : halt_cbn [] [] (colon s u) -> halt_cbn [] [] (app (cbv_cbn s) u).
Proof.
  elim: s u.
  - move=> n u /=.
    move=> /halt_cbnE H'.
    do ? constructor.
    apply: (halt_cbn_flatten_iff H'); by constructor.
  - move=> [n1|s1 s2|s1] IH1 [n2|t1 t2|t1] IH2 u.
    + move=> /= /halt_cbnE /halt_cbnE H'.
      do ? constructor.
      apply: (halt_cbn_flatten_iff H'); last done.
      constructor; [|constructor;[|done]] => /=.
      all: by rewrite ren_ren_term.
    + move Et: (app t1 t2) IH2 => t IH2 /= H'.
      rewrite /cbv_cbn -/cbv_cbn /= /funcomp /=.
      do 8 constructor.
      do 2 apply: halt_cbn_ren_S.
      have := IH2 (lam (app (app (Psi (var (S n1))) (var 0)) (ren S u))).
      apply: unnest.
      { move: H'. by rewrite -Et. }
      move=> /halt_cbnE {}H'.
      apply: (halt_cbn_flatten_iff H'); last done.
      constructor; last done.
      move=> /=. rewrite /funcomp /many_subst /=.
      congr lam. rewrite !simpl_term. congr app.
      apply: ext_subst_term. by case.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
  - move=> s IH u /=.
    rewrite /colon -/colon /cbv_cbn -/cbv_cbn /=.
    move=> /halt_cbnE H'.
    do ? constructor.
    apply: (halt_cbn_flatten_iff H'); last done.
    constructor; last done.
    move=> /=. rewrite !simpl_term.
    congr lam. apply: ext_subst_term. by case.
Admitted.
*)

Lemma bound_cbv_cbn k t : bound k t -> bound k (cbv_cbn t).
Proof.
  elim: t.
  - move=> n H. rewrite /cbv_cbn.
Admitted.

Lemma closed_cbv_cbn t : closed t -> closed (cbv_cbn t).
Proof. Admitted.

Lemma closed_lam_cbv_cbn t : closed (lam t) -> closed (lam (cbv_cbn t)).
Proof. Admitted.

Lemma lemma_6_3 {s t u} : closed s -> s ≻ t -> 
  halt_cbn [] [] (colon t u) ->
  halt_cbn [] [] (colon s u).
Proof.
  move=> Hs Hst.
  elim: Hst u Hs; clear s t.
  - move=> s t u /= /closed_app [Hs Ht].
    move=> H'. rewrite /colon /=.
    do 3 constructor.
    suff : halt_cbn [closure [] u] [] (L.subst (cbv_cbn s) 0 (lam (cbv_cbn t))).
    { move=> {}H'. apply: (halt_cbn_flatten_iff H'); first by constructor.
      move: Ht => /closed_lam_cbv_cbn. move: (cbv_cbn s) (lam (cbv_cbn t)) => s' t'.
      admit. (* doable *) }
    rewrite -lemma_6_1; first done.
    admit.
    (* by move: H' => /lemma_6_2 /halt_cbnE. *)
  - move=> s t t' ? IH u /closed_app [Hs Ht].
    move=> H'. rewrite /colon -/colon /=.
Admitted.

Arguments clos_trans {A} R.

(* induction on size of s *)
Lemma lemma_6_3' {s t u} : closed s -> s ≻ t ->
  clos_trans step (colon s u) (colon t u).
Proof.
  elim /(measure_rect term_size) : s t u.
  move=> s + t ++ Hst. case: Hst; clear s t.
  - move=> s1 s2 IH u /closed_app [Hs1 Hs2].
    rewrite L_subst_subst; first done.

    admit. (* substitution case *)
    (*
    move=> H'. rewrite /colon /=.
    do 3 constructor.
    suff : halt_cbn [closure [] u] [] (L.subst (cbv_cbn s) 0 (lam (cbv_cbn t))).
    { move=> {}H'. apply: (halt_cbn_flatten_iff H'); first by constructor.
      move: Ht => /closed_lam_cbv_cbn. move: (cbv_cbn s) (lam (cbv_cbn t)) => s' t'.
      admit. (* doable *) }
    rewrite -lemma_6_1; first done.
    by move: H' => /lemma_6_2 /halt_cbnE.*)
  - move=> s t t' ? IH u /closed_app [Hs Ht].
    rewrite /colon -/colon /=.


Admitted.

(* forward simulation *)
Lemma main_forward s t : closed s -> L.eval s t -> 
  halt_cbn [] [] (colon s (lam (var 0))).
Proof.
  move=> Hs /eval_iff [] Hst Ht.
  have H't := closed_star Hst Hs.
  elim: Hst Ht Hs.
  { move=> ? [? ->] ?. by do ? constructor. }
  move=> s1 s2 s3 Hs1s2 Hs2s3 IH Hs3 Hs1.
  apply: lemma_6_3; [done|eassumption|].
  apply: IH; [done|].
  by apply: closed_step; eassumption.
Qed.

Lemma not_halt_cbn_colon_var n : not (halt_cbn [] [] (colon (var n) (lam (var 0)))).
Proof.
  move=> /halt_cbnE /halt_cbnE /halt_cbnE /halt_cbnE /=.
  by case: n.
Qed.

Lemma main_backward s :
  closed s -> clos_refl_trans step (colon s u) (colon (lam t) u) -> 
  
  halt_cbn [] [] (colon s (lam (var 0))) -> exists t, L.eval s t.
Proof.

Lemma main_backward s :
  closed s -> halt_cbn [] [] (colon s (lam (var 0))) -> exists t, L.eval s t.
Proof.
  have := Seval.stepf_spec s.
  case: (Seval.stepf s) => [|s' ?].
  - admit.
  - move=> /(_ s') /iffLR /(_ (or_introl erefl)).
    move=> /lemma_6_3 /[apply]. /[apply].
    have /[apply] := lemma_6_3 Hs Hss'.
  Print or.

Check Seval.stepf.
