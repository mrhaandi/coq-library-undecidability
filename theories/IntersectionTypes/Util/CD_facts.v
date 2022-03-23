Require Import Undecidability.IntersectionTypes.CD.

Require Import List Relations Lia.
Import CD (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Fixpoint tm_size (M : tm) :=
  match M with
  | var _ => 1
  | app M' N' => 1 + tm_size M' + tm_size N'
  | lam M' => 1 + tm_size M'
  end.

Inductive type_assignment_var_spec (Gamma : list ty) x t : Prop :=
  | type_assignment_var_spec_intro s phi : 
      nth_error Gamma x = Some (s, phi) -> s = t \/ In t phi -> type_assignment_var_spec Gamma x t.

Inductive type_assignment_app_spec (Gamma : list ty) M N t : Prop :=
  | type_assignment_app_spec_intro s phi : 
      type_assignment Gamma M (arr s phi t) -> type_assignment Gamma N s -> Forall (type_assignment Gamma N) phi -> type_assignment_app_spec Gamma M N t.

Lemma type_assignmentE Gamma M t : type_assignment Gamma M t ->
  match M with
  | var x => type_assignment_var_spec Gamma x t
  | lam M' => 
    match t with
    | atom _ => False
    | arr s' phi' t' => type_assignment ((s', phi') :: Gamma) M' t'
    end
  | app M' N' => type_assignment_app_spec Gamma M' N' t
  end.
Proof. by case=> * //; econstructor; eassumption. Qed.

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

(* weak normalization property *)
Inductive wn M : Prop :=
  | wn_intro N : clos_refl_trans tm step M N -> normal_form N -> wn M.

Arguments wn_intro {M}.

(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
(forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Lemma not_step_var x N : step (var x) N -> False.
Proof. move E: (var x) => M HMN. by case: HMN E. Qed.

Lemma step_lamE M N : step (lam M) N ->
  exists M', N = lam M' /\ step M M'.
Proof.
  move E: (lam M) => M0 H. case: H E => //.
  move=> > ? [->]. by eexists.
Qed.

Lemma subst_as_ren M x : subst (scons (var x) var) M = ren (scons x id) M.
Proof.
  rewrite ren_as_subst_tm /=. apply: ext_subst_tm. by case.
Qed.

Lemma step_ren xi M N : step M N -> step (ren xi M) (ren xi N).
Proof.
  move=> H. elim: H xi.
  { move=> > /=.
    evar (M1 : tm). evar (M2 : tm).
    have := stepRed M1 M2. congr step.
    rewrite /M1 /M2 !simpl_tm. apply: ext_subst_tm.
    by case. }
  all: by eauto using step with nocore.
Qed.

(* mutual induction on head_form, normal_form *)
Scheme normal_form_ind' := Induction for normal_form Sort Prop
  with head_form_ind' := Induction for head_form Sort Prop.

Fact normal_form_ren xi M : 
  normal_form M -> normal_form (ren xi M).
Proof.
  move=> H. move: H xi.
  apply: (normal_form_ind' 
    (fun M _ => forall xi, normal_form (ren xi M)) 
    (fun M _ => forall xi, head_form (ren xi M)));
      by eauto using normal_form, head_form.
Qed.

Fact normal_form_ren' xi M : 
  normal_form (ren xi M) -> normal_form M.
Proof.
  move E: (ren xi M) => M' H. move: H xi M E.
  apply: (normal_form_ind' 
    (fun M' _ => forall xi M, ren xi M = M' -> normal_form M)
    (fun M' _ => forall xi M, ren xi M = M' -> head_form M)).
  - by eauto using normal_form, head_form.
  - move=> > ? IH ? [] //= ? [?]. subst.
    by eauto using normal_form, head_form.
  - move=> ?? [] //= ? [?]. subst.
    by eauto using normal_form, head_form.
  - move=> > ????? [] //= ?? [??]. subst.
    by eauto using normal_form, head_form.
Qed.


Lemma step_renE xi M N : step (ren xi M) N -> exists N', N = ren xi N' /\ step M N'.
Proof.
  move E: (ren xi M) => M' H. elim: H xi M E.
  - move=> ??? [] //.
    move=> [] // ?? /= [<- <-]. eexists.
    split; first last. { by apply: stepRed. }
    rewrite !simpl_tm. apply: ext_subst_tm.
    by case.
  - move=> > ? IH ? [] //= ? [?]. subst.
    have [? [? ?]] := IH _ _ erefl. subst.
    eexists.
    split; first last. { apply: stepLam. eassumption. }
    done.
  - move=> > ? IH ? [] //= ?? [??]. subst.
    have [? [? ?]] := IH _ _ erefl. subst.
    eexists.
    split; first last. { apply: stepAppL. eassumption. }
    done.
  - move=> > ? IH ? [] //= ?? [??]. subst.
    have [? [? ?]] := IH _ _ erefl. subst.
    eexists.
    split; first last. { apply: stepAppR. eassumption. }
    done.
Qed.

Lemma steps_renE xi M N : clos_refl_trans tm step (ren xi M) N -> exists N', N = ren xi N' /\ clos_refl_trans tm step M N'.
Proof.
  move E: (ren xi M) => M' /clos_rt_rt1n_iff H.
  elim: H xi M E.
  { move=> > <-. eexists. split;[done|]. by apply: rt_refl. }
  move=> > +++ > ?. subst. move=> /step_renE [?] [->] ? _.
  move=> /(_ _ _ erefl) [?] [->] ?.
  eexists. split; [done|].
  apply: rt_trans; [apply: rt_step|]; eassumption.
Qed.

Fixpoint sty_size (t : sty) :=
  match t with
  | atom a => 1
  | arr s phi t => 1 + sty_size s + list_sum (map sty_size phi) + sty_size t
  end.

Lemma In_sty_size_le s phi :
  In s phi -> sty_size s <= list_sum (map sty_size phi).
Proof.
  elim: phi; first done.
  move=> ?? IH /= [] => [<-|/IH]; lia.
Qed.

Lemma sty_ind' (P : sty -> Prop) :
  (forall x, P (atom x)) ->
  (forall s phi t, P s -> Forall P phi -> P t -> P (arr s phi t)) ->
  forall s, P s.
Proof.
  move=> IH1 IH2. elim /(measure_rect sty_size). case.
  - move=> *. apply: IH1.
  - move=> s phi t IH'. apply: IH2.
    + apply: IH'=> /=. lia.
    + elim: phi IH'; first done.
      move=> s' phi' IH1' IH2'. constructor.
      * apply: IH2'=> /=. lia.
      * apply: IH1'=> /= *. apply: IH2'=> /=. lia.
    + apply: IH'=> /=. lia.
Qed.

#[local] Notation all P l := (fold_right and True (map P l)).

Lemma Forall_all {X : Type} {P : X -> Prop} l : Forall P l <-> all P l.
Proof.
  elim: l. { done. }
  move=> ?? IH. split.
  - by move=> /Forall_cons_iff [? /IH].
  - move=> [? ?]. constructor; first done. by apply /IH.
Qed.

(*

(* strong normalization property *)
Inductive sn x : Prop :=
  | SNI : (forall y, step x y -> sn y) -> sn x.

Lemma sn_clos_refl_trans M N : clos_refl_trans tm step M N -> sn M -> sn N.
Proof.
  move=> /clos_rt_rt1n_iff. elim. { done. }
  move=> > ??? []. by eauto with nocore.
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
*)
