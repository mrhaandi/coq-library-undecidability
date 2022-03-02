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
  | app s t => lam (app (var 0) (cbv_cbn (app s t)))
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


Lemma cbv_cbn_ren xi s : cbv_cbn (ren xi s) = ren xi (cbv_cbn s).
Proof.
  elim: s xi.
  - done.
  - move=> ? IH1 ? IH2 xi /=. by rewrite IH1 IH2 !simpl_term.
  - move=> ? IH xi /=. rewrite IH !simpl_term.
    congr lam. congr app. congr lam.
    apply: ext_ren_term. by case.
Qed.

(* TODO proof could be simplified ? *)
Lemma cbv_cbn_subst sigma s : 
  (forall n, match sigma n with | app _ _ => False | _ => True end) ->
  cbv_cbn (subst sigma s) = subst (funcomp Psi sigma) (cbv_cbn s).
Proof.
  elim: s sigma.
  - move=> n sigma Hsigma /=.
    have := Hsigma n. by case: (sigma n).
  - move=> s IH1 t IH2 sigma Hsigma /=.
    rewrite (IH1 _ Hsigma) (IH2 _ Hsigma) /=.
    rewrite !simpl_term /=.
    congr lam. congr app. congr lam. congr app.
    apply: ext_subst_term => ? /=. by rewrite !simpl_term.
  - move=> s IH sigma Hsigma /=.
    rewrite IH.
    { move=> [|n] /=; first done.
      have := Hsigma n. by case: (sigma n). }
    rewrite !simpl_term.
    congr lam. congr app. congr lam.
    apply: ext_subst_term => - [|n] /=; first done.
    have := Hsigma n. case: (sigma n); [done|done|].
    move=> s' /= _. rewrite !cbv_cbn_ren.
    congr lam. rewrite !simpl_term. apply: ext_ren_term.
    by case.
Qed.

Fixpoint colon' s t :=
  match s with
  | var _ => app t (Psi s)
  | lam _ => app t (Psi s)
  | app s1 s2 =>
      colon' s1 (lam (app (ren S (cbv_cbn s2)) (lam (app (app (var 1) (var 0)) (ren S (ren S t))))))
  end.

Import Relation_Operators (t1n_trans).

Lemma stepsf_to_colon' s u : exists n, stepsf (S n) (app (cbv_cbn s) u) = Some (colon' s u).
Proof.
  elim: s u.
  - move=> n u /=. by exists 0.
  - move=> s IH1 t IH2 u /=.
    have [n Hn] := IH1 (lam (app (ren S (cbv_cbn t)) (lam (app (app (var 1) (var 0)) (ren S (ren S u)))))).
    exists (S n). rewrite -Hn.
    rewrite (stepsf_plus 1 (S n)) /=.
    by rewrite !simpl_term /= !ren_as_subst_term.
  - move=> ???. exists 0. move=> /=.
    rewrite /stepsf /= !simpl_term /=. congr Some. congr app. congr lam.
    rewrite -[RHS]subst_var_term. apply: ext_subst_term. by case.
Qed.


Lemma colon'_top_level_redex s t u :
  exists n, stepsf (S n) (colon' (app (lam s) (lam t)) u) = 
    Some (colon' (subst (scons (lam t) var) s) u).
Proof.
  have [n <-] := stepsf_to_colon' ((subst (scons (lam t) var) s)) u.
  exists (4+n). rewrite (stepsf_plus 4 (S n)).
  rewrite cbv_cbn_subst. { by case. }
  rewrite /stepsf /=.
  congr obind. congr Nat.iter. congr Some.
  rewrite !simpl_term /=. congr app.
  apply: ext_subst_term.
  case; last done.
  congr lam.
  rewrite -[RHS]subst_var_term.
  apply: ext_subst_term. by case.
Qed.


Lemma redex_colon' s t u : 
  exists n, stepsf (S n) (app (app (lam (cbv_cbn s)) (lam (cbv_cbn t))) u) =
    Some (colon' (subst (scons (lam t) var) s) u).
Proof.
  have [n Hn] := stepsf_to_colon' (subst (scons (lam t) var) s) u.
  exists (S n).
  rewrite (stepsf_plus 1 (S n)) -Hn /=.
  rewrite cbv_cbn_subst /=. { by case. }
  congr stepsf. congr app.
  apply: ext_subst_term. by case.
Qed.

Lemma closed_eval {s t} : L.eval s t -> closed s -> closed t.
Proof. by move=> /eval_iff [/closed_star]. Qed.

Arguments colon' : simpl never.

Lemma bound_ren {k k' xi t} : bound k t -> (forall n, n < k -> xi n < k') -> bound k' (ren xi t).
Proof.
  elim: t k k' xi.
  - move=> > /boundE ? H /=. apply: dclvar. by apply: H.
  - move=> ? IH1 ? IH2 > /boundE + ? /=.
    move=> [/IH1 {}IH1 /IH2 {}IH2]. apply: dclApp; [by apply: IH1|by apply: IH2].
  - move=> ? IH > /boundE /IH {}IH H /=.
    apply: dcllam. apply: IH.
    move=> [|n] /=; [|have := H n]; lia.
Qed.

Lemma bound_subst {k k' sigma t} : bound k t -> (forall n, n < k -> bound k' (sigma n)) -> bound k' (subst sigma t).
Proof.
  elim: t k k' sigma.
  - move=> > /boundE ? H /=. by apply: H.
  - move=> ? IH1 ? IH2 > /boundE + ? /=.
    move=> [/IH1 {}IH1 /IH2 {}IH2]. apply: dclApp; [by apply: IH1|by apply: IH2].
  - move=> ? IH > /boundE /IH {}IH H /=.
    apply: dcllam. apply: IH.
    move=> [|n] /=.
    + move=> _. apply: dclvar. lia.
    + move=> ?. apply: bound_ren.
      * apply: H. lia.
      * lia.
Qed.

Lemma bound_cbv_cbn k t : bound k t -> bound k (cbv_cbn t).
Proof.
  elim: t k.
  - move=> n k /boundE H. rewrite /cbv_cbn. apply: dcllam.
    apply: dclApp; apply: dclvar; lia.
  - move=> ? IH1 ? IH2 k /boundE [/IH1 {}IH1 /IH2 {}IH2] /=.
    apply: dcllam. apply: dclApp.
    + apply: (bound_ren IH1). lia.
    + apply: dcllam. apply: dclApp.
      * rewrite !simpl_term /=. apply: (bound_ren IH2). lia.
      * apply: dcllam. apply: dclApp; [apply: dclApp|]; apply: dclvar; lia.
  - move=> ? IH k /boundE /IH {}IH /=.
    apply: dcllam. apply: dclApp; [apply: dclvar; lia|].
    apply: dcllam. apply: (bound_ren IH).
    move=> [|n] /=; lia.
Qed.

(* cbv simulation lemma for closed terms *)
Lemma main_forward s t : L.eval s t -> closed s ->
  forall x, exists n, stepsf n (colon' s x) = Some (colon' t x).
Proof.
  elim. { move=> ???. by exists 0. }
  move=> {}s u {}t t' v Hsu IH1 Htt' IH2 Hv IH3 /closed_app [Hs Ht].
  move=> /(_ Hs) in IH1. move=> /(_ Ht) in IH2.
  have Ht' : closed t' by (apply: closed_eval; eassumption).
  have Hu : bound 1 u.
  { by have /closed_dcl /boundE := closed_eval Hsu Hs. } 
  have /IH3 {}IH3 : closed (L.subst u 0 t').
  { apply /closed_dcl. apply: closed_subst; [done|by apply /closed_dcl]. }
  move=> x.
  move: IH3.
  have -> : L.subst u 0 t' = subst (scons t' var) u.
  { rewrite L_subst_subst; first done.
    apply: (bound_ext_subst_term Hu).
    move=> [|n]; [done|lia]. }
  move: Htt' {Hv} IH2 Ht' => /eval_iff [_] [] t'' -> IH2 Ht'' IH3.
  pose x1 := lam (app (ren S (cbv_cbn t)) (lam (app (app (var 1) (var 0)) (ren S (ren S x))))).
  pose x2 := lam (app (app (lam (cbv_cbn u)) (var 0)) (ren S x)).
  have -> : colon' (app s t) x = colon' s x1 by done.
  have [n1 Hn1] := IH1 x1.
  have H'n1 : stepsf 1 (colon' (lam u) x1) = Some (app (cbv_cbn t) x2).
  { rewrite /stepsf /= /x2. congr Some. rewrite !simpl_term !ren_as_subst_term /=.
    congr app. congr lam. congr app. congr app. congr lam.
    move: Hu => /bound_cbv_cbn /bound_ext_subst_term.
    rewrite -[RHS]subst_var_term. apply.
    move=> [|?] /=; [done|lia]. }
  have [n2 Hn2] := stepsf_to_colon' t x2.
  have [n3 Hn3] := IH2 x2.
  have H'n3 : stepsf 1 (colon' (lam t'') x2) = Some (app (app (lam (cbv_cbn u)) (lam (cbv_cbn t''))) x).
  { rewrite /stepsf /= /x2. congr Some. rewrite !simpl_term /=.
    congr app. congr app. congr lam.
    move: Hu => /bound_cbv_cbn /bound_ext_subst_term.
    rewrite -[RHS]subst_var_term. apply.
    move=> [|?] /=; [done|lia]. }
  have [n4 Hn4] := redex_colon' u t'' x.
  have [n5 Hn5] := IH3 x.
  exists (n1 + (1 + (S n2 + (n3 + (1 + (S n4 + n5)))))).
  rewrite stepsf_plus Hn1 /=.
  rewrite (stepsf_plus 1 (S n2 + (n3 + (1 + (S n4 + n5))))) H'n1 /=.
  rewrite (stepsf_plus (S n2) (n3 + (1 + (S n4 + n5)))) Hn2 /=.
  rewrite (stepsf_plus n3 (1 + (S n4 + n5))) Hn3 /=.
  rewrite (stepsf_plus 1 (S n4 + n5)) H'n3 /=.
  by rewrite (stepsf_plus (S n4) n5) Hn4 /=.
Qed.

Print Assumptions main_forward.

(* BACKWARD DIRECTION using leftmost outermost L step *)

Definition is_app (t : term) :=
  if t is app _ _ then true else false.

(* left-most outer-most cbv step *)
Fixpoint cbv_stepf (s : term) : option term :=
  match s with
  | app s t =>
      match cbv_stepf s with
      | Some s' => Some (app s' t)
      | None =>
          if is_app s then None else
            match cbv_stepf t with
            | Some t' => Some (app s t')
            | None =>
                match s, t with
                | lam s', lam t' => Some (subst (scons (lam t') var) s')
                | _, _ => None
                end
            end
      end
  | _ => None
  end.

Definition cbv_stepsf k s := Nat.iter k (obind cbv_stepf) (Some s).

Arguments cbv_stepsf : simpl never.
Arguments cbv_stepf : simpl never.

Lemma cbv_stepsf_plus n m s : cbv_stepsf (n + m) s = (obind (cbv_stepsf m)) (cbv_stepsf n s).
Proof.
  rewrite /cbv_stepsf iter_plus. case: (Nat.iter n _ _); [done|by rewrite oiter_None].
Qed.

Lemma cbv_stepsf_appL {k s s' t} :
  cbv_stepsf k s = Some s' ->
  cbv_stepsf k (app s t) = Some (app s' t).
Proof.
  elim: k s s' t. { by move=> > [<-]. }
  move=> k IH s s' t.
  rewrite !(cbv_stepsf_plus 1 k).
  rewrite /(cbv_stepsf 1) /=.
  case E: (cbv_stepf s) => [s''|]; last done.
  move=> /= /IH {}IH.
  rewrite /cbv_stepf -/cbv_stepf E. by apply: IH.
Qed.

Lemma cbv_stepsf_appR {k s t t'} :
  cbv_stepsf k t = Some t' ->
  cbv_stepsf k (app (lam s) t) = Some (app (lam s) t').
Proof.
  elim: k s t t'. { by move=> > [<-]. }
  move=> k IH s t t'.
  rewrite !(cbv_stepsf_plus 1 k).
  rewrite /(cbv_stepsf 1) /=.
  case E: (cbv_stepf t) => [t''|]; last done.
  move=> /= /IH {}IH.
  rewrite /cbv_stepf -/cbv_stepf E. by apply: IH.
Qed.

(* this can be used to simplify forward direction proof *)
Lemma eval_cbv_stepsf s t : L.eval s t -> closed s -> exists k, cbv_stepsf k s = Some t.
Proof.
  elim; clear s t. { move=> *. by exists 0. }
  move=> s u t t' v Hsu IH1 Htt' IH2 Hv IH3 /closed_app [Hs Ht].
  move: (Hs) => /IH1 => - [k1 {}IH1].
  move: (Ht) => /IH2 => - [k2 {}IH2].
  have Ht' : closed t' by (apply: closed_eval; eassumption).
  have Hu : bound 1 u.
  { by have /closed_dcl /boundE := closed_eval Hsu Hs. } 
  have /IH3 [k3 {}IH3] : closed (L.subst u 0 t').
  { apply /closed_dcl. apply: closed_subst; [done|by apply /closed_dcl]. }
  move: IH3.
  have -> : L.subst u 0 t' = subst (scons t' var) u.
  { rewrite L_subst_subst; first done.
    apply: (bound_ext_subst_term Hu).
    move=> [|n]; [done|lia]. }
  move=> <-. exists (k1 + (k2 + S k3)).
  rewrite cbv_stepsf_plus (cbv_stepsf_appL IH1) /=.
  rewrite cbv_stepsf_plus (cbv_stepsf_appR IH2) /=.
  rewrite (cbv_stepsf_plus 1 k3) /=.
  by move: Htt' => /eval_iff [_] [? ->].
Qed.

Lemma cbv_stepf_closed {s s'} : cbv_stepf s = Some s' -> closed s -> closed s'.
Proof.
  elim: s s'; [done| |done].
  move=> s IH1 t IH2 s'. rewrite /cbv_stepf -/cbv_stepf.
  case Es: (cbv_stepf s) => [s''|].
  { move=> [<-] /closed_app [? ?].
    apply: app_closed; last done.
    by apply: IH1. }
  case: (is_app s); first done.
  case Et: (cbv_stepf t) => [t''|].
  { move=> [<-] /closed_app [? ?].
    apply: app_closed; first done.
    by apply: IH2. }
  case: (s); [done|done|] => ?.
  case: (t); [done|done|] => ?.
  move=> [<-] /closed_app [/closed_dcl /boundE ?] /closed_dcl ?.
  apply /closed_dcl. apply: bound_subst; first by eassumption.
  move=> [|n]; [done|lia].
Qed.

Lemma cbv_stepf_step s s' : cbv_stepf s = Some s' -> closed s -> L_facts.step s s'.
Proof.
  elim: s s'; [done| |done].
  move=> s IH1 t IH2 s'. rewrite /cbv_stepf -/cbv_stepf.
  case Es: (cbv_stepf s) => [s''|].
  { move=> [<-] /closed_app [? ?].
    apply: stepAppL. by apply: IH1. }
  case: (is_app s); first done.
  case Et: (cbv_stepf t) => [t''|].
  { move=> [<-] /closed_app [? ?].
    apply: stepAppR. by apply: IH2. }
  case: (s); [done|done|] => s'''.
  case: (t); [done|done|] => t'''.
  move=> [<-] /closed_app [/closed_dcl /boundE ?] /closed_dcl ?.
  have := L_facts.stepApp s''' t'''. congr L_facts.step.
  rewrite L_subst_subst. { by apply /closed_dcl. }
  apply: bound_ext_subst_term; first by eassumption.
  move=> [|n]; [done|lia].
Qed.

Lemma cbv_stepsf_eval k s t : cbv_stepsf k s = Some (lam t) -> closed s -> L.eval s (lam t).
Proof.
  move=> Hk Hs. apply /eval_iff. split; last done.
  elim: k s t Hk Hs.
  { move=> > [->] ?. by apply: starR. }
  move=> k IH s t.
  rewrite (cbv_stepsf_plus 1 k) /(cbv_stepsf 1) /=.
  case E: (cbv_stepf s) => [s'|]; last done.
  move=> + Hs. move: (Hs) => /(cbv_stepf_closed E) /IH /[apply] ?.
  apply: starC; last by eassumption.
  by apply: cbv_stepf_step.
Qed.

Lemma simulate_cbv_stepf s t : cbv_stepf s = Some t ->
  forall x, exists k, stepsf (S k) (colon' s x) = Some (colon' t x).
Proof.
  elim: s t; [done| |done].
  move=> s1 IH1 s2 IH2 t. rewrite /cbv_stepf -/cbv_stepf.
  case Es1: (cbv_stepf s1) => [s1'|].
  { move=> [<-] x.
    move: Es1 => /IH1 {}IH1.
    by apply: IH1. }
  case Hs1: (is_app s1); first done.
  case Es2: (cbv_stepf s2) => [s2'|].
  { move=> [<-] x.
    have H's1 : forall t, colon' (app s1 t) x = app (lam (app (ren S (cbv_cbn t)) (lam (app (app (var 1) (var 0)) (ren S (ren S x)))))) (Psi s1).
    { by case: (s1) Hs1. }
    rewrite !H's1. move: Es2 => /IH2 {}IH2.
    (* does not work immediately, needs more complicated colon as by plotkin?
    or just different stepf? *)
    
    
    }

  admit. (* doesnt work because of nested left apps that have no redex *) }
  case: (s1); [done|done|] => s1''.
  case: (s2); [done|done|] => s2''.
  move=> [<-] x. have [k Hk] := colon'_top_level_redex s1'' s2'' x.
  exists k. apply: Hk.
Admitted.

(**
(* OBSOLETE  *)

Lemma colon'_top_level_redex s t u : clos_trans step (colon' (app (lam s) (lam t)) u) (colon' (subst (scons (lam t) var) s) u).
Proof.
  move=> /=.
  apply /clos_trans_t1n_iff. apply: t1n_trans. { by apply: stepLam. }
  rewrite /=. apply: t1n_trans. { by apply: stepLam. }
  rewrite /=. apply: t1n_trans. { by apply: stepLam. }
  rewrite /=. apply: t1n_trans. { apply: stepApp. by apply: stepLam. }
  apply /clos_trans_t1n_iff.
  have := asd0 ((subst (scons (lam t) var) s)) u.
  congr clos_trans. rewrite cbv_cbn_subst. { by case. }
  rewrite !simpl_term. congr app; [|by rewrite -[LHS]subst_var_term].
  apply: ext_subst_term.
  case; last done.
  congr lam.
  rewrite -[LHS]subst_var_term.
  apply: ext_subst_term. by case.
Qed.

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
*)
