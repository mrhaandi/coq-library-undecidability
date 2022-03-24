(* OBSOLETE; REMOVE *)

Require Import Undecidability.IntersectionTypes.CDV.

Require Import List Relations Lia.
Import CDV (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Fixpoint tm_size (M : tm) :=
  match M with
  | var _ => 1
  | app M' N' => 1 + tm_size M' + tm_size N'
  | lam M' => 1 + tm_size M'
  end.

Lemma type_assignmentE Gamma M t : type_assignment Gamma M t ->
  match M with
  | var x => In t (nth x Gamma nil)
  | lam M' => 
    match t with
    | atom _ => False
    | arr phi' t' => type_assignment (phi' :: Gamma) M' t'
    end
  | app M' N' => exists phi',
      type_assignment Gamma M' (arr phi' t) /\ Forall (type_assignment Gamma N') phi'
  end.
Proof. by case=> *; do ? eexists; eassumption. Qed.

(*head form : x M1 .. Mn where x is free of bound*)
Inductive normal_form : tm -> Prop :=
  | normal_head : forall M, head_form M -> normal_form M
  | normal_abs : forall M, normal_form M -> normal_form (lam M)
with head_form : tm -> Prop :=
  | head_var : forall x, head_form (var x)
  | head_app : forall M N, head_form M -> normal_form N -> head_form (app M N).


(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

Arguments funcomp {X Y Z} (g f) /.

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

(* parallel term renaming *)
Fixpoint ren (xi : nat -> nat) (t : tm) : tm  :=
  match t with
  | var x => var (xi x)
  | app s t => app (ren xi s) (ren xi t)
  | lam t => lam (ren (scons 0 (funcomp S xi)) t)
  end.

(* parallel term substitution *)
Fixpoint subst (sigma: nat -> tm) (s: tm) : tm :=
  match s with
  | var n => sigma n
  | app s t => app (subst sigma s) (subst sigma t)
  | lam s => lam (subst (scons (var 0) (funcomp (ren S) sigma)) s)
  end.

Lemma ext_ren_tm xi1 xi2 t : (forall n, xi1 n = xi2 n) -> ren xi1 t = ren xi2 t.
Proof.
  elim: t xi1 xi2.
  - move=> > /= ?. by congr var.
  - move=> ? IH1 ? IH2 ?? Hxi /=. congr app; [by apply: IH1 | by apply: IH2].
  - move=> ? IH > Hxi /=. congr lam. apply: IH.
    case; first done. move=> ?. by congr S.
Qed.

Lemma ext_subst_tm sigma1 sigma2 t : (forall n, sigma1 n = sigma2 n) ->
  subst sigma1 t = subst sigma2 t.
Proof.
  elim: t sigma1 sigma2.
  - by move=> > /= ?.
  - move=> ? IH1 ? IH2 ?? Hsigma /=. congr app; [by apply: IH1 | by apply: IH2].
  - move=> ? IH > Hsigma /=. congr lam. apply: IH.
    case; first done. move=> ?. by rewrite /= Hsigma.
Qed.

Lemma ren_ren_tm xi1 xi2 t : ren xi2 (ren xi1 t) = ren (funcomp xi2 xi1) t.
Proof.
  elim: t xi1 xi2 => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_ren_tm. by case.
Qed.

Lemma ren_as_subst_tm xi t : ren xi t = subst (funcomp var xi) t.
Proof.
  elim: t xi => /=.
  - done.
  - move=> ? IH1 ? IH2 ?. by rewrite IH1 IH2.
  - move=> ? IH ?. rewrite IH.
    congr lam. apply: ext_subst_tm. by case.
Qed.

Lemma ren_subst_tm xi sigma t : ren xi (subst sigma t) = subst (funcomp (ren xi) sigma) t.
Proof.
  elim: t xi sigma => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_tm.
    case; first done. move=> ?. by rewrite /= !ren_ren_tm.
Qed.

Lemma subst_ren_tm xi sigma t : subst sigma (ren xi t) = subst (funcomp sigma xi) t.
Proof.
  elim: t xi sigma => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_tm. by case.
Qed.

Lemma subst_subst_tm sigma1 sigma2 t : subst sigma2 (subst sigma1 t) = subst (funcomp (subst sigma2) sigma1) t.
Proof.
  elim: t sigma1 sigma2 => /=.
  - done.
  - move=> ? IH1 ? IH2 ??. by rewrite IH1 IH2.
  - move=> ? IH ??. rewrite IH.
    congr lam. apply: ext_subst_tm.
    case; first done. move=> ?.
    by rewrite /= !ren_subst_tm !subst_ren_tm.
Qed.

Lemma subst_var_tm s : subst var s = s.
Proof.
  elim: s.
  - done.
  - move=> ? IH1 ? IH2 /=. by rewrite IH1 IH2.
  - move=> ? IH /=. congr lam. rewrite -[RHS]IH.
    apply: ext_subst_tm. by case.
Qed.

Definition simpl_tm := (ren_ren_tm, ren_subst_tm, subst_ren_tm, subst_subst_tm, subst_var_tm).

Inductive step : tm -> tm -> Prop :=
  | stepRed s t    : step (app (lam s) t) (subst (scons t var) s)
  | stepLam s s'   : step s s' -> step (lam s) (lam s')
  | stepAppL s s' t : step s s' -> step (app s t) (app s' t)
  | stepAppR s t t' : step t t' -> step (app s t) (app s t').

(* strong normalization property *)
Inductive sn x : Prop :=
  | SNI : (forall y, step x y -> sn y) -> sn x.

Lemma sn_clos_refl_trans M N : clos_refl_trans tm step M N -> sn M -> sn N.
Proof.
  move=> /clos_rt_rt1n_iff. elim. { done. }
  move=> > ??? []. by eauto with nocore.
Qed.

(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
(forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Lemma normal_form_spec M : normal_form M \/ exists N, step M N.
Proof.
  elim: M.
  - move=> ?. left. by auto using normal_form, head_form with nocore.
  - move=> M []; first last.
    { move=> [M' ?] ? ?. right. eexists (app M' _). by apply: stepAppL. }
    case; first last.
    { move=> *. right. eexists. by apply: stepRed. }
    move=> {}M HM N []; first last.
    { move=> [?] ?. right. eexists (app M _). apply: stepAppR. eassumption. }
    move=> ?. left. by do 2 constructor.
  - move=> M [].
    { move=> ?. left. by constructor. }
    move=> [? ?]. right. eexists. apply: stepLam. eassumption.
Qed.

Lemma sn_nf M : sn M -> exists N, normal_form N /\ clos_refl_trans tm step M N.
Proof.
  elim.
  move=> {}M IH1 IH2.
  case: (normal_form_spec M).
  - move=> ?. exists M. split; first done. by apply: rt_refl.
  - move=> [?] /[dup] ? /IH2 [N] [? ?]. exists N. split; first done.
    apply: rt_trans; [|eassumption].
    by apply: rt_step.
Qed.

Fixpoint sty_size (t : sty) :=
  match t with
  | atom a => 1
  | arr phi t => 1 + list_sum (map sty_size phi) + sty_size t
  end.
