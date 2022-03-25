Require Import Undecidability.IntersectionTypes.CD.

Require Import List Relations Lia.
Import CD (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Lemma nth_error_seq start len n : n < len -> nth_error (seq start len) n = Some (start+n).
Proof.
  elim: len start n. { lia. }
  move=> len IH start [|n] ?. { congr Some. lia. }
  rewrite /= IH; [|congr Some]; lia.
Qed.

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

Lemma ren_id_tm s : ren id s = s.
Proof. by rewrite ren_as_subst_tm subst_var_tm. Qed.

Definition simpl_tm := (ren_ren_tm, ren_subst_tm, subst_ren_tm, subst_subst_tm, ren_id_tm, subst_var_tm).

Fixpoint forall_fv (P : nat -> Prop) t := 
  match t with
  | var x => P x
  | app s t => forall_fv P s /\ forall_fv P t
  | lam t => forall_fv (scons True P) t
  end.

Lemma forall_fv_impl (P Q : nat -> Prop) t : 
  (forall x, P x -> Q x) -> forall_fv P t -> forall_fv Q t.
Proof.
  elim: t P Q => /=.
  - move=> >. by apply.
  - move=> ? IH1 ? IH2 > /[dup] /IH1 {}IH1 /IH2 {}IH2. tauto.
  - move=> > IH > H /=. apply: IH.
    by case.
Qed.

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

Lemma type_assignment_ren_fv Gamma Delta xi t M :
  type_assignment Gamma M t ->
  forall_fv (fun x => forall s phi, nth_error Gamma x = Some (s, phi) -> nth_error Delta (xi x) = Some (s, phi)) M ->
  type_assignment Delta (ren xi M) t.
Proof.
  elim: M Gamma Delta xi t.
  - move=> > /type_assignmentE [>] /= ++ IH.
    move=> /IH ??. by econstructor; eassumption.
  - move=> > IH1 > IH2 > /type_assignmentE [>].
    move=> /IH1 {}IH1 ? Hphi /= [] /IH1 ? /IH2 {}IH2 /=.
    econstructor.
    + eassumption.
    + by apply: IH2.
    + by apply: Forall_impl Hphi => ? /IH2.
  - move=> > IH ??? [] > /type_assignmentE; first done.
    move=> /IH {}IH /= H'. constructor. apply: IH.
    apply: forall_fv_impl H'.
    by case.
Qed.

Lemma type_assignment_ren Gamma Delta xi t M :
  type_assignment Gamma M t ->
  (forall x s phi, nth_error Gamma x = Some (s, phi) -> nth_error Delta (xi x) = Some (s, phi)) ->
  type_assignment Delta (ren xi M) t.
Proof.
  elim: M Gamma Delta xi t.
  - move=> > /type_assignmentE [>] /= ++ IH.
    move=> /IH ??. by econstructor; eassumption.
  - move=> > IH1 > IH2 > /type_assignmentE [>].
    move=> /IH1 {}IH1 ? Hphi /[dup] /IH1 ? /IH2 {}IH2 /=.
    econstructor.
    + eassumption.
    + by apply: IH2.
    + by apply: Forall_impl Hphi => ? /IH2.
  - move=> > IH ??? [] > /type_assignmentE; first done.
    move=> /IH {}IH H' /=. constructor. apply: IH.
    by case.
Qed.

Lemma type_assignment_subst Gamma Delta sigma t M :
  type_assignment Gamma M t ->
  (forall x s phi, nth_error Gamma x = Some (s, phi) -> Forall (type_assignment Delta (sigma x)) (s::phi)) ->
  type_assignment Delta (subst sigma M) t.
Proof.
  elim: M Gamma Delta sigma t.
  - move=> > /type_assignmentE [>] /= ++ IH.
    move=> /IH /Forall_cons_iff [IH1 /Forall_forall IH2].
    by move=> [<-|/IH2].
  - move=> > IH1 > IH2 > /type_assignmentE [>].
    move=> /IH1 {}IH1 ? Hphi /[dup] /IH1 ? /IH2 {}IH2 /=.
    econstructor.
    + eassumption.
    + by apply: IH2.
    + by apply: Forall_impl Hphi => ? /IH2.
  - move=> > IH ??? [] > /type_assignmentE; first done.
    move=> /IH {}IH H' /=. constructor. apply: IH.
    move=> [|x] > /=.
    + move=> [<- <-]. apply /Forall_forall=> ??. by econstructor.
    + move=> /H'. apply: Forall_impl=> ? /type_assignment_ren. by apply.
Qed. 

Lemma type_preservation_step {Gamma t M N} : step M N -> type_assignment Gamma M t -> type_assignment Gamma N t.
Proof.
  move=> H. elim: H Gamma t.
  - move=> > /type_assignmentE [>] /type_assignmentE *.
    apply: type_assignment_subst; [eassumption|].
    move=> [|x].
    + move=> ?? [<- <-]. by constructor.
    + move=> ?? /= Hx. apply /Forall_forall=> ? Ht.
      by econstructor; eassumption.
  - move=> > ? IH ? [] > /type_assignmentE; by eauto using type_assignment with nocore.
  - move=> > ? IH > /type_assignmentE []. by eauto using type_assignment with nocore.
  - move=> > ? IH > /type_assignmentE []. eauto using type_assignment, Forall_impl with nocore.
Qed.

Lemma type_preservation {Gamma t M N} : clos_refl_trans tm step M N -> type_assignment Gamma M t -> type_assignment Gamma N t.
Proof.
  elim; by eauto using type_preservation_step with nocore.
Qed.
