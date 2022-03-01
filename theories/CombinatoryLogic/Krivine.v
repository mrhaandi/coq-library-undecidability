(*
  Krivine Machine
  https://en.wikipedia.org/wiki/Krivine_machine

  Closure-based left-most-outer-most lambda-term evaluation

  Further details in L_CBN_Interpreter
*)

From Undecidability Require L.L.
Require Import List Lia.
Import L.
From Undecidability Require Import L.Util.L_facts.
From Undecidability Require L.Computability.Seval.
Require Import Relations.
Require Import ssreflect ssrbool ssrfun.

Unset Implicit Arguments.

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

Fixpoint term_size (t : term) : nat :=
  match t with
  | var n => n
  | app s t => 1 + term_size s + term_size t
  | lam s => 1 + term_size s
  end.

Fixpoint eterm_size (u : eterm) : nat :=
  let '(closure ctx t) := u in 1 + list_sum (map eterm_size ctx) + (term_size t).

Definition context_size (ctx : list eterm) : nat :=
  eterm_size (closure ctx (var 0)).

Fixpoint eclosed (u : eterm) : Prop :=
  let '(closure ctx t) := u in bound (length ctx) t /\ Forall id (map eclosed ctx).

(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
(forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

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

Fixpoint subst (sigma: nat -> term)  (s: term) : term :=
  match s with
  | var n => sigma n
  | app s t => app (subst sigma s) (subst sigma t)
  | lam s => lam (subst (scons (var 0) (funcomp (ren S) sigma)) s)
  end.

Definition many_subst (ts : list term) (s : term) : term :=
  subst (fun n => nth n ts (var (n - length ts))) s.

Arguments many_subst ts !s /.

(* recursively substitute each local context, rename all free varaibles to 0 *)
Fixpoint flatten (u : eterm) : term :=
  let '(closure ctx t) := u in ren (fun=> 0) (many_subst (map flatten ctx) t).

Lemma ext_ren_term xi1 xi2 t : (forall n, xi1 n = xi2 n) -> ren xi1 t = ren xi2 t.
Proof.
  elim: t xi1 xi2.
  - move=> > /= ?. by congr var.
  - move=> ? IH1 ? IH2 ?? Hxi /=. congr app; [by apply: IH1 | by apply: IH2].
  - move=> ? IH > Hxi /=. congr lam. apply: IH.
    case; first done. move=> ?. by congr S.
Qed.

Lemma ext_subst_term sigma1 sigma2 t : (forall n, sigma1 n = sigma2 n) ->
  subst sigma1 t = subst sigma2 t.
Proof.
  elim: t sigma1 sigma2.
  - by move=> > /= ?.
  - move=> ? IH1 ? IH2 ?? Hsigma /=. congr app; [by apply: IH1 | by apply: IH2].
  - move=> ? IH > Hsigma /=. congr lam. apply: IH.
    case; first done. move=> ?. by rewrite /= /funcomp Hsigma.
Qed.

Lemma ren_ren_term xi1 xi2 t : ren xi2 (ren xi1 t) = ren (funcomp xi2 xi1) t.
Proof.
  elim: t xi1 xi2 => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_ren_term. by case.
Qed.

Lemma ren_as_subst_term xi t : ren xi t = subst (funcomp var xi) t.
Proof.
  elim: t xi => /=.
  - done.
  - move=> ? IH1 ? IH2 ?. by rewrite IH1 IH2.
  - move=> ? IH ?. rewrite IH.
    congr lam. apply: ext_subst_term. by case.
Qed.

Lemma ren_subst_term xi sigma t : ren xi (subst sigma t) = subst (funcomp (ren xi) sigma) t.
Proof.
  elim: t xi sigma => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_term.
    case; first done. move=> ?. by rewrite /funcomp /= !ren_ren_term.
Qed.

Lemma subst_ren_term xi sigma t : subst sigma (ren xi t) = subst (funcomp sigma xi) t.
Proof.
  elim: t xi sigma => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_term. by case.
Qed.

Lemma subst_subst_term sigma1 sigma2 t : subst sigma2 (subst sigma1 t) = subst (funcomp (subst sigma2) sigma1) t.
Proof.
  elim: t sigma1 sigma2 => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_term.
    case; first done. move=> ?. rewrite /funcomp /=.
    by rewrite !ren_subst_term !subst_ren_term.
Qed.

Definition simpl_term := (ren_ren_term, ren_subst_term, subst_ren_term, subst_subst_term).

Lemma flatten_var_0 t ctx :
  flatten (closure (t :: ctx) (var 0)) = flatten t.
Proof. move: t => [? ?]. by rewrite /= /many_subst /= ren_ren_term. Qed.

Lemma flatten_var_S t ctx n :
  flatten (closure (t :: ctx) (var (S n))) = flatten (closure ctx (var n)).
Proof. done. Qed.

Lemma Forall2_consE {X : Type} {P : X -> X -> Prop} {x1 l1 x2 l2} : 
  Forall2 P (x1::l1) (x2::l2) -> P x1 x2 /\ Forall2 P l1 l2.
Proof. move=> H. by inversion H. Qed.

Lemma many_subst_cons u ts s : ren (fun=> 0) (many_subst (u :: ts) s) = 
  subst (funcomp (ren (fun=> 0)) (scons u var))
    (if ren (fun=> 0) (many_subst ts (lam s)) is lam t then t else var 0).
Proof.
  rewrite /many_subst /= !ren_subst_term !subst_subst_term.
  apply: ext_subst_term.
  move=> [|n] /=; first done.
  rewrite /funcomp /=. move: (nth _ _ _) => ?.
  rewrite !subst_ren_term ren_as_subst_term.
  apply: ext_subst_term. by case.
Qed.

(* halt_cbn is invariant closure flattening *)
Lemma halt_cbn_flatten_iff {ts1 ts2 ctx1 ctx2 s1 s2} :
  halt_cbn ts1 ctx1 s1 ->
  map flatten ts1 = map flatten ts2 ->
  flatten (closure ctx1 s1) = flatten (closure ctx2 s2) ->
  halt_cbn ts2 ctx2 s2.
Proof.
  move=> H. elim: H ts2 ctx2 s2; clear ts1 ctx1 s1.
  - move=> ts ctx t ctx' ? IH ts2 ctx2 s2.
    rewrite flatten_var_0.
    by move=> /IH /[apply].
  - move=> ts1 ctx1 n t ? IH ts2 ctx2 s2.
    rewrite flatten_var_S.
    by move=> /IH /[apply].
  - move=> ts1 ctx1 s t ? IH ts2 ctx2 s2.
    elim /(measure_rect context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * rewrite flatten_var_0.
        move=> /= ??. apply: halt_var_0. apply: IH' => //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ??. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + move=> ??? /= [] /IH {}IH ?.
      apply: halt_app. apply: IH => //=.
      by congr cons.
    + done.
  - move=> t1 ts1 ctx1 s1 ? IH [|t2 ts2] ctx2 s2; first done.
    move=> [Ht1t2 ?].
    elim /(measure_rect context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * rewrite flatten_var_0.
        move=> /= ?. apply: halt_var_0. apply: IH' => //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ?. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + done.
    + move=> s2 /= [Hs1s2]. apply: halt_lam_ts. apply: IH => //=.
      by rewrite Ht1t2 !many_subst_cons /= Hs1s2.
  - move=> ctx1 s1 [|t2 ts2] ctx2 s2; last done.
    move=> _.
    elim /(measure_rect context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * rewrite flatten_var_0.
        move=> /= ?. apply: halt_var_0. apply: IH' => //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ?. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + done.
    + move=> *. by apply: halt_lam.
Qed.

Lemma halt_cbn_ren_S {ts ctx u s} :
  halt_cbn ts ctx s ->
  halt_cbn ts (u::ctx) (ren S s).
Proof.
  move=> /halt_cbn_flatten_iff. apply; first done.
  - by rewrite /= /many_subst !simpl_term.
Qed.

Print Assumptions halt_cbn_flatten_iff.

(* left-most outer-most call-by-name *)
Inductive step : term -> term -> Prop :=
  | stepLam s t    : step (app (lam s) t) (subst (scons t var) s)
  | stepApp s s' t : step s s' -> step (app s t) (app s' t).

Lemma stepE s t :
  step s t ->
  match s with
  | app (lam s1) s2 => t = subst (scons s2 var) s1
  | app (app s1 s2) s3 => exists s', t = app s' s3 /\ step (app s1 s2) s'
  | _ => False
  end.
Proof.
  elim; first done.
  case; [done| |done].
  move=> []; [done| |].
  - move=> > ? [?] [-> ?].
    eexists. split; [done|by apply: stepApp].
  - move=> > ? ->. eexists. split; [done|by apply: stepLam].
Qed.

Lemma step_fun s t1 t2 : step s t1 -> step s t2 -> t1 = t2.
Proof.
  move=> H. elim: H t2.
  - by move=> > /stepE ->.
  - case.
    + by move=> > /stepE.
    + by move=> > ? IH t2 /stepE [?] [->] /IH ->.
    + by move=> > /stepE.
Qed.

Arguments clos_refl_trans {A}.
Arguments clos_trans {A}.
(*
Inductive crt_length : nat -> term -> term -> Prop :=
  | crt_length_refl t : crt_length 0 t t
  | 
*)

Print clos_refl_trans_1n_ind.

Lemma step_aux (P : term -> Prop) :
  (forall s, (forall u, clos_trans step s u -> P u) -> P s) -> 
  forall s t,
    clos_refl_trans step s t -> P t -> (forall u, not (clos_refl_trans step t u)) -> P s.
Proof.
  move=> IH ?? /(@clos_rt_rt1n term). elim; first done.
  move=> s s' t Hss' Hs't IH' Ht H't. apply: (IH).
  move=> u /(@clos_trans_t1n_iff term) Hsu.
  case: Hsu Hss'.
  + move=> ? /step_fun /[apply] ->. by apply: IH'.
  + move=> > + ?. move=> /step_fun /[apply] ?. subst.
    apply: (IH).
      case: Hs't IH H't Ht; clear t.
      * done.
      * move=> s'' t Hs's'' Hs''t IH1 IH2 Ht. apply: IH1; [done| |done].
        apply.
        admit.

  elim´´´´

Lemma step_aux s t (P : term -> Prop) : (forall u, not (clos_refl_trans step t u)) ->
  ((forall u, clos_trans step s u -> P u) -> P s) -> P t -> clos_refl_trans step s t -> P s.
Proof.
  move=> H1 H2 H3 /(@clos_rt_rt1n term) Hst.
  elim: Hst H1 H2 H3; clear s t.
  - done.
  - move=> s s' t Hss' Hs't IH H't IH' Ht. apply: IH'.
    move=> u /(@clos_trans_t1n_iff term) Hsu.
    case: Hsu Hss'.
    + move=> ? /step_fun /[apply] ->.
      case: Hs't IH H't Ht; clear t.
      * done.
      * move=> s'' t Hs's'' Hs''t IH1 IH2 Ht. apply: IH1; [done| |done].
        apply.
        admit.
    + move=> > + ?. move=> /step_fun /[apply] ?. subst.

        done. 
    apply: (IH).
    done. apply.  admit.  done.
    admit. admit.
  - done.
  -  
Admitted.

Lemma test s t : clos_refl_trans step s t -> False.
Proof.
  apply: step_aux.
  - admit.
  -  
  


Lemma ren_closed {xi t} : closed t -> ren xi t = t.
Proof. Admitted.
  
Lemma subst_closed {sigma t} : closed t -> subst sigma t = t.
Proof. Admitted.

Lemma many_subst_closed {ts t} : closed t -> many_subst ts t = t.
Proof. move=> /subst_closed. by apply. Qed.

Lemma L_subst_subst s k t :
  closed t -> L.subst s k t = subst (fun n => if Nat.eqb n k then t else var n) s.
Proof.
  move=> Ht. elim: s k.
  - done. 
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH k /=. rewrite IH.
    congr lam. apply: ext_subst_term.
    rewrite /funcomp /=.
    move=> [|n] /=; first done.
    case: (Nat.eqb n k); last done.
    by rewrite (ren_closed Ht).
Qed.

Lemma step_halt_cbn s t ts ctx : closed s -> step s t ->
  halt_cbn ts ctx s -> halt_cbn ts ctx t.
Proof.
  move=> Hs Hst. elim: Hst Hs ts ctx; clear s t.
  - move=> s t /closed_app [Hs Ht] ts ctx /halt_cbnE /halt_cbnE.
    move=> /halt_cbn_flatten_iff. apply; first done.
    rewrite /= /many_subst /= !simpl_term. apply: ext_subst_term.
    rewrite /funcomp /=. move=> [|n] /=; last done.
    rewrite !simpl_term. apply: ext_subst_term.
    move=> n. by rewrite /funcomp /= !simpl_term.
  - move=> s s' t ? IH /closed_app [Hs Ht] ts ctx /halt_cbnE /IH {}IH.
    apply: halt_app. by apply: IH.
Qed.

Lemma step_halt_cbn' s t ts ctx : closed s -> step s t ->
  halt_cbn ts ctx t -> halt_cbn ts ctx s.
Proof.
  move=> Hs Hst. elim: Hst Hs ts ctx; clear s t.
  - move=> s t /closed_app [Hs Ht] ts ctx H'.
    apply: halt_app. apply: halt_lam_ts.
    apply: (halt_cbn_flatten_iff H'); first done.
    rewrite /= /many_subst /= !simpl_term. apply: ext_subst_term.
    rewrite /funcomp /=. move=> [|n] /=; last done.
    rewrite !simpl_term. apply: ext_subst_term.
    move=> n. by rewrite /funcomp /= !simpl_term.
  - move=> s s' t ? IH /closed_app [Hs Ht] ts ctx /halt_cbnE /IH {}IH.
    apply: halt_app. by apply: IH.
Qed.

(* maybe this is needed? *)
Lemma halt_cbn_spec ts ctx s : halt_cbn ts ctx s ->
  exists t, clos_refl_trans term step (flatten (closure ctx s)) (lam t).
Proof.
  elim.
  - move=> > ? [t IH]. exists t.
    move: IH. by rewrite /= !simpl_term.
Admitted.
