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
Lemma halt_cbn_flatten_iff ts1 ts2 ctx1 ctx2 s1 s2:
  halt_cbn ts1 ctx1 s1 ->
  Forall2 (fun t1 t2 => flatten t1 = flatten t2) ts1 ts2 ->
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
      by constructor.
    + done.
  - move=> t1 ts1 ctx1 s1 ? IH [|t2 ts2] ctx2 s2.
    { move=> H. by inversion H. }
    move=> /Forall2_consE [Ht1t2 ?].
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
  - move=> ctx1 s1 [|t2 ts2] ctx2 s2; first last.
    { move=> H. by inversion H. }
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

Print Assumptions halt_cbn_flatten_iff.
