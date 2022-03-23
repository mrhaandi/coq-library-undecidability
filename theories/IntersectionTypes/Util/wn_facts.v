Require Import Undecidability.IntersectionTypes.CD Undecidability.IntersectionTypes.Util.CD_facts.
Require Import Relations List Lia.

Import CD (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".

Definition Arr (P Q : tm -> Prop) (M : tm) := forall N, P N -> Q (app M N).

#[local] Notation all P l := (fold_right and True (map P l)).

Fixpoint interp (P : tm -> Prop) (M : tm) (s : sty) : Prop :=
  match s with
  | atom a => P M
  | arr s phi t => Arr (fun N => (interp P N s /\ all (interp P N) phi)) (fun N => interp P N t) M
  end.

(* P-neutral term *)
Inductive neutral (P : tm -> Prop) : tm -> Prop :=
  | neutral_var x : neutral P (var x)
  | neutral_app M N : neutral P M -> P N -> neutral P (app M N).

(* P-compatible head expansion *)
Inductive head_exp (P : tm -> Prop) : tm -> tm -> Prop :=
  | head_exp_lam M N : P N -> head_exp P (subst (scons N var) M) (app (lam M) N)
  | head_exp_app M M' N : head_exp P M M' -> P N -> head_exp P (app M N) (app M' N).

Record Saturated (Q P : tm -> Prop) :=
  { Saturated_incl : forall M, P M -> Q M;
    Saturated_neutral : forall M, neutral Q M -> P M }.

Arguments Saturated_incl {Q P}.
Arguments Saturated_neutral {Q P}.

Record Admissible (P : tm -> Prop) :=
  { Admissible_head_exp M N : head_exp P M N -> P M -> P N;
    Admissible_neutral M : neutral P M -> P M;
    Admissible_app_var M x : P (app M (var x)) -> P M }.

Lemma Admissible_Saturated_interp {P} : Admissible P -> forall t, Saturated P (fun M => interp P M t).
Proof.
  move=> HP. elim /sty_ind'.
  { move=> x. constructor=> ?.
    - done.
    - by apply: (Admissible_neutral P HP). }
  move=> s phi t IHs IHphi IHt. constructor=> M /= HM.
  - have /HM : interp P (var 0) s /\ all (interp P (var 0)) phi.
    { split. 
      - apply: (Saturated_neutral IHs). by constructor.
      - apply /Forall_all. apply: Forall_impl IHphi=> ?.
        move=> /Saturated_neutral. apply. by constructor. }
    move=> /(Saturated_incl IHt). by apply: (Admissible_app_var P HP).
  - move=> N [+ _] => /(Saturated_incl IHs) ?.
    apply: (Saturated_neutral IHt). by constructor.
Qed.

Lemma interp_head_exp {P : tm -> Prop} {M N t} : Admissible P ->
  head_exp P M N -> interp P M t -> interp P N t.
Proof.
  move=> HP. have HQ := Admissible_Saturated_interp HP. elim: t M N.
  { move=> *. apply: (Admissible_head_exp _ HP); eassumption. }
  move=> s ? phi t IH M N /= ? IH' N' [Hs Hphi].
  apply: IH. { constructor; [|apply: (Saturated_incl (HQ _))]; eassumption. }
  by apply: IH'.
Qed.

Definition satis (P : tm -> Prop) (Gamma : list ty) M t :=
  forall sigma, (forall i s phi, nth_error Gamma i = Some (s, phi) -> interp P (sigma i) s /\ (Forall (interp P (sigma i)) phi)) ->
  interp P (subst sigma M) t.

Arguments satis P Gamma M !t /.

Lemma satisI P Gamma M t : Admissible P -> type_assignment Gamma M t -> satis P Gamma M t.
Proof.
  move=> HP. have HQ := Admissible_Saturated_interp HP.
  elim: M Gamma t.
  - move=> a > /type_assignmentE [] s phi Ha H.
    move=> sigma /(_ a _ _ Ha) [] /=.
    case: H. { by move=> <-. }
    by move=> + _ /Forall_forall {}H => /H.
  - move=> ? IH1 ? IH2 ?? /type_assignmentE [] s phi /IH1 /= {}IH1 /IH2 {}IH3 Hphi.
    move=> sigma Hsigma /=. apply: (IH1 sigma Hsigma). split.
    { by apply: IH3. }
    apply /Forall_all. apply: Forall_impl Hphi => ? /IH2. by apply.
  - move=> ? IH1 ? [?|s phi t] /type_assignmentE; first done.
    move=> /IH1 {}IH1 sigma HGamma /=.
    move=> N [Hs Hphi]. apply: (interp_head_exp HP).
    { apply: head_exp_lam. by apply: (Saturated_incl (HQ s)). }
    rewrite simpl_tm. apply: IH1=> - [|i].
    + move=> /= ?? [<- <-]. by split; [|apply /Forall_all].
    + move=> ?? /HGamma => - [Hs' Hphi'] /=. by rewrite !simpl_tm.
Qed.

(* fundamental theorem for admissible predicates *)
Theorem fundamental (P : tm -> Prop) Gamma M t : Admissible P ->
  type_assignment Gamma M t -> P M.
Proof.
  move=> /[dup] HP /satisI /[apply] /(_ var). rewrite simpl_tm.
  have HQ := Admissible_Saturated_interp HP.
  move=> H. apply: (Saturated_incl (HQ _)).
  apply: H=> i *. have : neutral P (var i) by constructor.
  by split; [|apply /Forall_forall]=> *; apply: (Saturated_neutral (HQ _)).
Qed.

Module Admissible_wn.

Lemma neutal_wn_wn M : neutral wn M -> wn M.
Proof.
  suff: neutral wn M -> exists N, clos_refl_trans tm step M N /\ head_form N.
  { move=> /[apply] - [?] [??]. by econstructor; [eassumption|constructor]. }
  elim. { move=> x. exists (var x). by split; [apply: rt_refl|constructor]. }
  move=> {}M N H1M [M'] [HMM' HM'] [N'] HNN' HN'.
  exists (app M' N'). split; [|by constructor].
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

Lemma head_exp_step M N : head_exp wn M N -> step N M.
Proof.
  elim. { move=> *. by apply: stepRed. }
  move=> *. by apply: stepAppL.
Qed.

Lemma step_wn M N : step M N -> wn N -> wn M.
Proof.
  move=> ? [???]. econstructor; [|eassumption].
  by apply: rt_trans; [apply: rt_step|]; eassumption.
Qed.

Lemma head_exp_wn M N : head_exp wn M N -> wn M -> wn N.
Proof.
  by move=> /head_exp_step /step_wn.
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

Lemma wn_app_var M x : wn (app M (var x)) -> wn M.
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

Lemma Admissible_wn : Admissible wn.
Proof.
  constructor.
  - by apply: head_exp_wn.
  - by apply: neutal_wn_wn.
  - by apply: wn_app_var.
Qed.

End Admissible_wn.

(* consequence of fundamental theorem *)
Lemma weak_normalization Gamma M t : type_assignment Gamma M t -> wn M.
Proof.
  apply: fundamental. by apply: Admissible_wn.Admissible_wn.
Qed.
