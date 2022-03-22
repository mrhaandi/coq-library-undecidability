Require Import Undecidability.IntersectionTypes.CD Undecidability.IntersectionTypes.Util.CD_facts.
Require Import Relations List Lia.

Import CD (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".

#[local] Notation all P l := (fold_right and True (map P l)).

Definition Arr (P Q : tm -> Prop) (M : tm) := forall N, P N -> Q (app M N).

(*  forall N, (all (interp N) phi) -> interp (app M N) t *)

Fixpoint interp (M : tm) (s : sty) : Prop :=
  match s with
  | atom a => wn M
  | arr s phi t => Arr (fun N => (interp N s /\ all (interp N) phi)) (fun N => interp N t) M
  end.

Definition satis (Gamma : list ty) M t :=
  forall sigma, (forall i s phi, nth_error Gamma i = Some (s, phi) -> interp (sigma i) s /\ (Forall (interp (sigma i)) phi)) ->
  interp (subst sigma M) t.

Lemma Forall_all {X : Type} {P : X -> Prop} l : Forall P l <-> all P l.
Proof.
  elim: l. { done. }
  move=> ?? IH. split.
  - by move=> /Forall_cons_iff [? /IH].
  - move=> [? ?]. constructor; first done. by apply /IH.
Qed.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Inductive head_wn : tm -> Prop :=
  | head_wn_var x : head_wn (var x)
  | head_wn_app M N : head_wn M -> wn N -> head_wn (app M N).

Lemma head_wnE M : head_wn M ->
  match M with
  | var _ => True
  | lam _ => False
  | app M1 M2 => head_wn M1 /\ wn M2
  end.
Proof. by case. Qed.

Record Saturated (P : tm -> Prop) :=
  { Saturated_wn : forall M, P M -> wn M;
    Saturated_head_wn : forall M, head_wn M -> P M }.

Lemma not_step_var x N : step (var x) N -> False.
Proof. move E: (var x) => M HMN. by case: HMN E. Qed.

Lemma head_wn_wn M : head_wn M -> wn M.
Proof.
  suff: head_wn M -> exists N, clos_refl_trans tm step M N /\ head_form N.
  { move=> /[apply] - [?] [??]. by econstructor; [eassumption|constructor]. }
  elim. { move=> x. exists (var x). by split; [apply: rt_refl|constructor]. }
  move=> {}M N H1M [M'] [HMM' HM'] [N'] HNN' HN'.
  exists (app M' N'). split; [|by constructor].
  (* many steps app L *)
  apply: (rt_trans _ _ _ (app M' N)).
  - elim: HMM'.
    + move=> > ?. apply: rt_step. by apply: stepAppL.
    + move=> ?. by apply: rt_refl.
    + move=> *. by apply: rt_trans; eassumption.
  - elim: HNN'.
    + move=> > ?. apply: rt_step. by apply: stepAppR.
    + move=> ?. by apply: rt_refl.
    + move=> *. by apply: rt_trans; eassumption.
Qed.

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

Lemma wn_ren xi M : wn (ren xi M) -> wn M.
Proof.
  case=> N /steps_renE [?] [->] ? /normal_form_ren' /wn_intro. by apply.
Qed.

Lemma wn_lam M : wn M -> wn (lam M).
Proof.
  case=> N HMN ?. apply: (wn_intro (lam N)); [|by constructor].
  elim: HMN; by eauto using clos_refl_trans, step with nocore.
Qed.

Lemma step_wn M N : step M N -> wn N -> wn M.
Proof.
  move=> ? [???]. econstructor; [|eassumption].
  by apply: rt_trans; [apply: rt_step|]; eassumption.
Qed.

Lemma wn_app_var x M : wn (app M (var x)) -> wn M.
Proof.
  case=> N /clos_rt_rt1n_iff.
  move E: (app M (var x)) => M' H. elim: H M E.
  { move=> ?? E H. case: H E; last done.
    move=> ? []; first done.
    move=> ???? [-> _]. by econstructor; [apply: rt_refl|constructor]. }
  move=> > [].
  - move=> > IH ?? [??]. subst.
    move: IH. rewrite subst_as_ren.
    by move=> /clos_rt_rt1n_iff /wn_intro /[apply] /wn_ren /wn_lam.
  - done.
  - move=> > ?? IH ? [??]. subst.
    move: (IH _ erefl) => /[apply].
    by apply: step_wn.
  - move=> > H ? IH ? [??]. subst.
    by move=> /not_step_var in H.
Qed.


Lemma In_sty_size_le s phi :
  In s phi -> sty_size s <= list_sum (map sty_size phi).
Proof.
  elim: phi; first done.
  move=> ?? IH /= [] => [<-|/IH]; lia.
Qed.

Lemma Saturated_interp t : Saturated (fun M => interp M t).
Proof.
  elim /(measure_rect sty_size): t. case.
  { move=> x IH. constructor=> ?.
    - done.
    - by apply: head_wn_wn. }
  move=> s phi t IH. constructor=> M HM /=.
  - have := HM (var 0).
    apply: unnest.
    { split.
      { have /= := IH s. apply: unnest. { lia. }
        move=> /Saturated_head_wn. apply. by constructor. }
      apply /Forall_all /Forall_forall => s' /In_sty_size_le ?.
      have /= := IH s'. apply: unnest. { lia. }
      move=> /Saturated_head_wn. apply. by constructor. }
    have /= := IH t. apply: unnest. { lia. }
    move=> /Saturated_wn /[apply]. by apply: wn_app_var.
  - move=> N [+ _].
    have /= := IH s. apply: unnest. { lia. }
    move=> /Saturated_wn /[apply] ?.
    have /= := IH t. apply: unnest. { lia. }
    move=> /Saturated_head_wn. apply. by constructor.
Qed.

Print Assumptions Saturated_interp.

(* this will follow from saturation *)
Lemma interp_var x t : interp (var x) t.
Proof.
  have /Saturated_head_wn := Saturated_interp t.
  apply. by constructor.
Qed.

(* this needs interp_var *)
Lemma interp_wn M t : interp M t -> wn M.
Proof.
  have /Saturated_wn := Saturated_interp t. by apply.
Qed.

Inductive head_red : tm -> tm -> Prop :=
  | head_red_lam M N : wn N -> head_red (subst (scons N var) M) (app (lam M) N)
  | head_red_app M M' N : head_red M M' -> wn N -> head_red (app M N) (app M' N).

Lemma head_redE M N : head_red M N ->
  match N with
  | app (lam M1) M2 => M = subst (scons M2 var) M1 /\ wn M2
  | app M1 M2 => exists M', M = app M' M2 /\ head_red M' M1 /\ wn M2
  | _ => False
  end.
Proof.
  elim. { done. }
  by move=> ? [] *; [|eexists|].
Qed.

Lemma head_red_step M N : head_red M N -> step N M.
Proof.
  elim. { move=> *. by apply: stepRed. }
  move=> *. by apply: stepAppL.
Qed.

Lemma head_red_wn M N : head_red M N -> wn M -> wn N.
Proof.
  by move=> /head_red_step /step_wn.
Qed.

Lemma interp_head_red M N t : head_red M N -> interp M t -> interp N t.
Proof.
  elim: t M N.
  { move=> > ?. by apply: head_red_wn. }
  move=> s IHs phi t IH M N /= []. rewrite /Arr.
  - move=> {}M {}N HN IH' ? [Hs ?].
    apply: IH.
    { constructor; [by apply: head_red_lam|].
      have /Saturated_wn := Saturated_interp s. by apply. }
    by apply: IH'.
  - move=> > ?? /= IH' ? [??]. apply: IH.
    { constructor; [constructor|].
      - eassumption.
      - done.
      - have /Saturated_wn := Saturated_interp s. by apply. }
    by apply: IH'.
Qed.

(* this will follow from saturation? *)
Lemma interp_red M N t : wn N -> interp (subst (scons N var) M) t -> interp (app (lam M) N) t.
Proof.
  move=> HN. apply: interp_head_red. by apply: head_red_lam.
Qed.

(* needs stronger positivity assumption for whole derivation ! *)
Lemma satisI Gamma M t : type_assignment Gamma M t -> satis Gamma M t.
Proof.
  elim: M Gamma t.
  - move=> a > /type_assignmentE [] s phi Ha H.
    move=> sigma /(_ a _ _ Ha) [] /=.
    case: H. { by move=> <-. }
    by move=> + _ /Forall_forall {}H => /H.
  - move=> ? IH1 ? IH2 ?? /type_assignmentE [] s phi /IH1 {}IH1 /IH2 {}IH3 Hphi.
    move=> sigma Hsigma /=. apply: (IH1 sigma Hsigma). split.
    { by apply: IH3. }
    apply /Forall_all. rewrite -/interp.
    apply: Forall_impl Hphi => ? /IH2. by apply.
  - move=> ? IH1 ? [?|s phi t] /type_assignmentE; first done.
    move=> /IH1 {}IH1 sigma HGamma /=.
    move=> N [Hs Hphi]. apply: interp_red.
    { apply: interp_wn. eassumption.  }
    rewrite simpl_tm. apply: IH1=> - [|i].
    + move=> /= ?? [<- <-]. by split; [|apply /Forall_all].
    + move=> ?? /HGamma => - [Hs' Hphi'] /=. by rewrite !simpl_tm.
Qed.

Lemma weak_normalization Gamma M t : 
  type_assignment Gamma M t -> wn M.
Proof.
  move=> /satisI /(_ var). rewrite simpl_tm.
  apply: unnest. 
  { move=> i *. split. { by apply: interp_var. }
    apply /Forall_forall => *. by apply: interp_var. }
  by apply: interp_wn.
Qed.

Print Assumptions weak_normalization.
