Require Import Undecidability.IntersectionTypes.CDV Undecidability.IntersectionTypes.Util.type_assignment_facts.
Require Import Setoid Morphisms.
Require Import List Lia.

Import CDV (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".

#[local] Notation all P l := (fold_right and True (map P l)).

Definition Arr (P Q : tm -> Prop) (M : tm) := forall N, P N -> Q (app M N).

(*  forall N, (all (interp N) phi) -> interp (app M N) t *)

Fixpoint interp (M : tm) (s : sty) : Prop :=
  match s with
  | atom a => sn M
  | arr phi t => Arr (fun N => (all (interp N) phi)) (fun N => interp N t) M
  end.

Definition satis Gamma M t :=
  (forall sigma, (forall i, Forall (interp (sigma i)) (nth i Gamma nil)) ->
  interp (subst sigma M) t).

Lemma Forall_all {X : Type} {P : X -> Prop} l : Forall P l <-> all P l.
Proof.
  elim: l. { done. }
  move=> ?? IH. split.
  - by move=> /Forall_cons_iff [? /IH].
  - move=> [? ?]. constructor; first done. by apply /IH.
Qed.

(*
Lemma head_redexE {M M'} : head_redex M M' ->
  match M' with
  | app (lam M1') M2' => M = subst (scons M2' var) M1'
  | app M1' M2' => exists M1, M = app M1 M2' /\ head_redex M1 M1'
  | _ => False
  end.
Proof.
  elim. { done. }
  move=> ? []; [done| |done].
  move=> *. by eexists.
Qed.

Lemma head_redex_spec M N N' : step N N' -> head_redex M N -> M = N'.
Proof.
  elim /(measure_rect tm_size): M N N'.
  move=> M IH N N' [].
  - by move=> > /head_redexE.
  - by move=> > ? /head_redexE.
  - move=> > ? /head_redexE [?] [?] ?. subst.
    congr app. apply: IH.
    + move=> /=. lia.
    + eassumption.
    + eassumption.
Qed.

Lemma head_redex_interp M M' t : head_redex M M' -> interp M t -> interp M' t.
Proof.
  elim: t M M'.
  { move=> ? M M' /= H HM. constructor=> N.
    by move: H => /head_redex_spec /[apply] <-. }
  move=> phi t IH M M' /= ? IH' N Hphi.
  apply: IH. { apply: head_redex_app. eassumption. }
  by apply: IH'.
Qed.
*)

(* no empty intersections *)
Fixpoint positive (t : sty) :=
  match t with
  | atom _ => True
  | arr phi t =>  phi <> nil /\ all positive phi /\ positive t
  end.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Inductive head_sn : tm -> Prop :=
  | head_sn_var x : head_sn (var x)
  | head_sn_app M N : head_sn M -> sn N -> head_sn (app M N).

Lemma head_snE M : head_sn M ->
  match M with
  | var _ => True
  | lam _ => False
  | app M1 M2 => head_sn M1 /\ sn M2
  end.
Proof. by case. Qed.

Record Saturated (P : tm -> Prop) :=
  { Saturated_sn : forall M, P M -> sn M;
    Saturated_head_sn : forall M, head_sn M -> P M }.

Lemma not_step_var x N : step (var x) N -> False.
Proof. move E: (var x) => M HMN. by case: HMN E. Qed.

Lemma head_sn_step M N : head_sn M -> step M N -> head_sn N.
Proof.
  move=> H.
  elim: H N; clear M. { by move=> ?? /not_step_var. }
  move=> M1 M2. move E: (app M1 M2) => M HM1 IH HM2 N HMN.
  case: HMN E.
  - move=> > [??]. subst. by move=> /head_snE in HM1.
  - done.
  - move=> > ? [??]. subst. by constructor; [apply: IH|].
  - move=> > ? [??]. subst. constructor; [done|].
    case: HM2. by apply.
Qed.

Lemma head_sn_sn M : head_sn M -> sn M.
Proof.
  elim; clear M.
  - move=> ?. constructor. by move=> ? /not_step_var.
  - move=> M N H1M H2M HN.
    elim: HN; clear N => N IH1N.
    elim: H2M H1M; clear M => M IH1M IH2M H1M IH2N.
    constructor=> M2. move E1: (app M N) => M1 HM1M2.
    case: HM1M2 E1.
    + move=> > [? ?]. subst. by move=> /head_snE in H1M.
    + done.
    + move=> > ? [??]. subst.
      apply: IH2M; [done|apply: head_sn_step; eassumption|].
      move=> ? /IH2N []. apply. by apply: stepAppL.
    + move=> > ? [??]. subst. by apply: IH2N.
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

Lemma sn_ren xi M : sn (ren xi M) -> sn M.
Proof.
  move E: (ren xi M) => M' HM'.
  elim: HM' xi M E => ? _ IH xi M ?. subst.
  constructor=> ? /(step_ren xi) /IH. by apply.
Qed.

Lemma sn_lam M : sn M -> sn (lam M).
Proof.
  elim=> {}M _ IH. by constructor=> ? /step_lamE [?] [->] /IH.
Qed.

Lemma sn_app_var x M : sn (app M (var x)) -> sn M.
Proof.
  move E': (app M (var x)) => M' HM'.
  elim: HM' M x E'.
  move=> {}M' IH1 IH2 M x ?. subst. constructor.
  move=> N HMN.
  case: HMN IH1 IH2.
  - move=> > IH1 IH2. apply: IH2.
    + apply: stepAppL. by apply: stepRed.
    + done.
  - move=> > ? IH1 IH2.
    have := IH1 _ (stepRed _ _).
    rewrite subst_as_ren.
    move=> /sn_ren [] H. apply: sn_lam. by apply: H.
  - move=> > ? IH1 IH2. apply: IH2.
    + apply: stepAppL. apply: stepAppL. eassumption.
    + done.
  - move=> > ? IH1 IH2. apply: IH2.
    + apply: stepAppL. apply: stepAppR. eassumption.
    + done.
Qed.

(* looks doable *)
Lemma Saturated_interp t : positive t -> Saturated (fun M => interp M t).
Proof.
  elim /(measure_rect sty_size): t. case.
  { move=> x IH _. constructor.
    - done.
    - move=> M /=. by apply: head_sn_sn. }
  move=> phi t IH /= [H1phi [H2phi Ht]]. constructor=> /=.
  - move=> M. rewrite /Arr => HM.
    have := HM (var 0).
    apply: unnest. 
    { elim: phi IH {H1phi} H2phi {HM}. { done. }
      move=> s phi IH IH' /= [Hs Hphi]. split.
      - have := IH' s _ Hs.
        apply: unnest. { move=> /=. lia. }
        move=> /Saturated_head_sn. apply. by constructor.
      - apply: IH; [|done].
        move=> s' /= ? /IH'. apply=> /=. lia. }
    have := IH t _ Ht.
    apply: unnest. { rewrite /=. lia. }
    move=> /Saturated_sn /[apply]. by apply: sn_app_var.
  - move=> M HM N.
    move: phi IH H1phi H2phi => [|s phi]; first done.
    move=> IH _ /= [Hs Hphi] [].
    have := IH s _ Hs.
    apply: unnest. { rewrite /=. lia. }
    move=> /Saturated_sn /[apply] ? H'phi.
    have := IH t _ Ht.
    apply: unnest. { rewrite /=. lia. }
    move=> /Saturated_head_sn. apply.
    by constructor.
Qed.

Print Assumptions Saturated_interp.

(* this will follow from saturation *)
Lemma interp_var x t : positive t -> interp (var x) t.
Proof.
  move=> /Saturated_interp /Saturated_head_sn. apply.
  by constructor.
Qed.

(* this needs interp_var *)
Lemma interp_sn M t : positive t -> interp M t -> sn M.
Proof.
  move=> /Saturated_interp /Saturated_sn. by apply.
Qed.

Inductive head_red : tm -> tm -> Prop :=
  | head_red_lam M N : sn N -> head_red (subst (scons N var) M) (app (lam M) N)
  | head_red_app M M' N : head_red M M' -> sn N -> head_red (app M N) (app M' N).

Lemma head_redE M N : head_red M N ->
  match N with
  | app (lam M1) M2 => M = subst (scons M2 var) M1 /\ sn M2
  | app M1 M2 => exists M', M = app M' M2 /\ head_red M' M1 /\ sn M2
  | _ => False
  end.
Proof.
  elim. { done. }
  by move=> ? [] *; [|eexists|].
Qed.



(* is this wrong? M = I , N = (lam I) O
   NO, O is diallowed by head_red *)
Lemma head_red_sn M N : sn M -> head_red M N -> sn N.
Proof.
  elim=> {}M _ IH HMN. constructor=> N' HNN'.
  case: HNN' HMN IH.
  - admit.
  - by move=> > ? /head_redE.
  - move=> > [].
    + move=> > /head_redE [?] [->] [/head_redE] [-> ??].

    + by move=> > /not_step_var.
    + move=> > ? /head_redE [?] [->] [? ?].

Admitted.

Lemma interp_head_red M N t : positive t -> head_red M N -> interp M t -> interp N t.
Proof.
  elim: t M N.
  { move=> > ? /=.  admit. (* doable *) }
  move=> phi s IH M N /= [H1phi] [H2phi] Hs HMN. rewrite /Arr.
  move=> IH' N' Hphi. apply: (IH _ _ Hs).
  - apply: head_red_app; [eassumption|].
    move: (phi) H1phi H2phi Hphi => [|? ?]; first done.
    move=> /= _ [/Saturated_interp] /Saturated_sn + _ [].
    by move=> /[apply].
  - by apply: IH'.
Admitted.

(* this will follow from saturation? *)
Lemma interp_red M N t : sn N -> interp (subst (scons N var) M) t -> interp (app (lam M) N) t.
Proof.
  move=> HN. apply: interp_head_red. by apply: head_red_lam.
Qed.

(* needs stronger positivity assumption for whole derivation ! *)
Lemma satisI Gamma M t : Forall (Forall positive) Gamma -> positive t -> type_assignment Gamma M t -> satis Gamma M t.
Proof.
  elim: M Gamma t.
  - move=> a > ?? /type_assignmentE H.
    by move=> sigma /(_ a) /Forall_forall /(_ _ H).
  - move=> ? IH1 ? IH2 ???? /type_assignmentE [phi] [/IH1] {}IH1 Hphi.
    move=> sigma Hsigma /=. apply: (IH1 _ _ sigma Hsigma).
    { done. }
    { cbn. }
    apply /Forall_all. rewrite -/interp.
    apply: Forall_impl Hphi => ? /IH2. by apply.
  - move=> ? IH1 ? [?|phi t] /type_assignmentE; first done.
    move=> /IH1 {}IH1 sigma HGamma /=.
    move=> N Hphi. apply: interp_red. rewrite simpl_tm. apply: IH1 => - [|i].
    + by apply /Forall_all.
    + apply: Forall_impl (HGamma i) => ? /=.
      by rewrite !simpl_tm.
Qed.

Lemma In_nth_In t x (Gamma : list ty) :
  In t (nth x Gamma nil) ->
  In (nth x Gamma nil) Gamma.
Proof.
  elim: Gamma x. { by case. }
  by move=> > IH [|x] => [|/IH] ?; [left|right].
Qed.

Lemma normalization Gamma M t : 
  Forall (Forall positive) Gamma -> positive t -> type_assignment Gamma M t -> sn M.
Proof.
  move=> HGamma Ht /satisI /(_ var). rewrite simpl_tm.
  apply: unnest. 
  { move=> i. apply /Forall_forall => ? /[dup] /In_nth_In.
    move: HGamma => /Forall_forall /[apply].
    move=> /Forall_forall /[apply].
    by apply: interp_var. }
  by apply: interp_sn.
Qed.

Print Assumptions normalization.

(* OOOOOOOLD  *)

Lemma Saturated_interp t : positive t -> Saturated (fun M => interp M t).
Proof.
  elim /(measure_rect sty_size): t. case.
  { move=> x IH. constructor.
    - done.
    - move=> M /=. admit. (* easy *) }
  move=> phi t IH /= H'. constructor=> /=.
  - move=> M. rewrite /Arr => HM.
    have := HM (var 0).
    apply: unnest. { admit. (* doabl? by IH *) }


Lemma head_sn_interp M t : head_sn M -> interp M t.
Proof.
  elim /(measure_rect sty_size): t M. case.
  - move=> /= ? _. admit. (* easy *)
  - move=> phi t IH /= M HM N Hphi. move=> ?. apply: (IH).
    + move=> /=. lia.
    +   rewrite /Arr.  

Lemma head_sn_Arr (P Q : tm -> Prop) : (forall M, head_sn M -> P M) -> (forall M, head_sn M -> Q M) ->
  forall M, head_sn M -> Arr P Q M.
Proof.
  move=> HP HQ ????. apply: HQ. constructor. elim.
  - move=> x ? ?. apply: HQ.
(* NO! need stratification 
Lemma head_sn_interp M t : head_sn M -> interp M t.
Proof.
  elim /(measure_rect sty_size): t M. case.
  - move=> /= ? _. admit. (* easy *)
  - move=> phi t IH /= M HM N Hphi. apply: (IH).
    + move=> /=. lia.
    +   rewrite /Arr.  
*)

Lemma Saturated_interp t : Saturated (fun M => interp M t).
Proof.
  elim: t.
  { constructor.
    - move=> x /=. admit. (* easy *)
    - move=> /=. admit. (* difficult *)
    - move=> M N /=. (* WRONG *) admit. }
  move=> phi t [???]. constructor.
  - move=> x /=. rewrite /Arr.
  constructor.

(* OLD *)





(* saturated set of lambda-terms 
Definition sat (P : tm -> Prop) :=
  (forall M, head_sn M -> P M) /\ (forall M M', head_redex M M' -> P M -> P M').
*)

(* saturated set of lambda-terms *)
Definition sat (P : tm -> Prop) :=
  (forall M, head_args sn M -> P M).

Lemma sat_sn : sat sn.
Proof.
  move=> M H. have : head_form M.
  split.
Admitted.



Lemma sat_Arr P Q : sat P -> sat Q -> sat (Arr P Q).
Proof.
  split.
  - 
  (*
Lemma interp_sn M t : positive t -> interp M t -> sn M.
Proof.
  elim /(measure_rect sty_size) : t M.
*)
Lemma interp_hf M t : positive t -> head_sn M -> interp M t.
Proof.
  elim /(measure_rect sty_size) : t M.
  case. { move=> a IH M /=. admit. (*doable  *) }
  move=> [|s phi] t IH M /= []; first done.
  move=> _ [[? ?] ?] HM N [H'N Hphi]. apply: (IH).
  - move=> /=. lia.
  - done.
  - apply: head_sn_app; first done.









Print Assumptions satisI.






(*
(*head form : x M1 .. Mn where x is free of bound*)
Inductive normal_form : tm -> Prop :=
  | normal_head : forall M, head_form M -> normal_form M
  | normal_abs : forall M, normal_form M -> normal_form (lam M)
  with head_form : tm -> Prop :=
  | head_var : forall x, head_form (var x)
  | head_app : forall M N, head_form M -> normal_form N -> head_form (app M N).

Inductive sat (P : tm -> Prop) :=
  (forall M, head_form M -> P M) /\ 
*)

Lemma asd M N t : step M N -> interp N t -> interp M t.
Proof.
  elim.
  -  
  - case: t.
    + move=> /=.


Definition pw_iff {X} p q := (forall x : X, p x <-> q x).
Notation "p == q" := (pw_iff p q) (at level 70).

#[local] Instance Equiv_pw_iff {X} : Equivalence (@pw_iff X).
Proof. firstorder done. Qed.

Lemma pw {X : Type} P Q :
  (forall x : X, P x <-> Q x) ->
  (forall x, P x) <-> (forall x, Q x).
Proof. firstorder done. Qed.

Ltac pw := repeat (apply pw; intros).

(* * Strong Normalisation  *)

(* ** Logical Relation  *)

Definition active P :=
  match P with
  | lam _ => true
  | _ => false
  end.

Definition tpred := tm -> Prop.

Definition M (p : tpred) : tpred :=
  fun P => forall xi, p (ren xi P).

Inductive R (p : tpred) P : Prop :=
| RI : (active P = true -> M p P) ->
       (forall Q, step P Q -> R p Q) ->
       R p P.

#[local] Instance R_ext :
  Proper (pw_iff ==> eq ==> iff) R.
Proof.
  intros p1 p2 Heq P ? ->. split; induction 1 as [P H H1 H2].
  - econstructor. intros H3 xi. eapply Heq. now eapply H. eauto.
  - econstructor. intros H3 xi. eapply Heq. now eapply H. eauto.
Qed.

Record model := mk_model
  {
    Var : tpred -> tpred ;
    Arr : list tpred -> tpred -> tpred ;
    Var_ext : Proper (pw_iff ==> pw_iff) Var ;
    Arr_ext : Proper ((List.Forall2 pw_iff) ==> pw_iff ==> pw_iff) Arr ;
  }.
#[local] Existing Instances Var_ext Arr_ext.

Section Evaluation.
  Variable (M : model).

  Fixpoint eval (ρ : nat -> tpred) (s : sty) : tpred :=
    match s with
    | atom a => Var M (ρ a)
    | arr phi t => Arr M (map (eval ρ) phi) (eval ρ t)
    end.

  #[local] Instance eval_ext :
    Proper (pointwise_relation _ pw_iff ==> eq ==> pw_iff) eval.
  Proof.
    intros ρ1 ρ2 Heq s ? <-. induction s in ρ1, ρ2, Heq |- *; cbn.
    - now rewrite (Heq n).
    - have ? : List.Forall2 pw_iff (map (eval ρ1) l) (map (eval ρ2) l).
      admit. apply: Arr_ext. done. by apply: IHs.
  Admitted.

  (*
  Lemma eval_ren ξ s ρ :
    eval ρ (ren_poly_type ξ s) == eval (ξ >> ρ) s.
  Proof.
    induction s in ξ, ρ |- *; cbn.
    - reflexivity.
    - now rewrite IHs1, IHs2.
    - eapply All_ext. intros d. rewrite IHs.
      eapply eval_ext. now intros []. reflexivity.
  Qed.

  Lemma eval_weaken s ρ d :
    eval (d .: ρ) (ren_poly_type shift s) == eval ρ s.
  Proof. now rewrite eval_ren. Qed.
*)

  Definition lift : model.
  Proof using M.
    refine (mk_model id (Arr M) _ _).
    abstract firstorder.
  Defined.

End Evaluation.

(*
Lemma eval_subst (M : model) σ s ρ :
  eval M ρ (subst_poly_type σ s) == eval (lift M) (σ >> eval M ρ) s.
Proof.
  induction s in σ, ρ |- *; cbn.
  - reflexivity.
  - now rewrite IHs1, IHs2.
  - eapply All_ext. intros d. rewrite IHs. asimpl.
    eapply eval_ext; try reflexivity. intros []. reflexivity. eapply eval_weaken.
Qed.


Lemma eval_beta (M : model) s t ρ :
  eval M ρ (subst_poly_type (t .: poly_var) s) == eval (lift M) (eval M ρ t .: ρ >> Var M) s.
Proof.
  rewrite eval_subst.
  eapply eval_ext. now intros []. reflexivity.
Qed.
*)

Definition D : model.
Proof.
  refine {| Var :=  id ;
            Arr := fun ps q P => match P with lam P => forall Q, R p Q -> R q (subst_term poly_var (Q .: var) P) | _ => False end |}.
  - abstract firstorder.
  - abstract (intros p1 p2 Heq1 p1' p2' Heq2 []; cbn; try tauto; pw; now rewrite Heq1, Heq2).
  - abstract (intros F1 F2 Heq []; cbn; try tauto; pw; now rewrite (Heq x)).
Defined.

(* Instance equiv_D : equiv D. *)

Notation V s ρ := (eval D ρ s).
Notation K s ρ := (M (V s ρ)).
Notation E s ρ := (R (V s ρ)).

(* ** Reducibility Candidates  *)

Lemma R_sn p P :
  R p P -> sn P.
Proof.
  induction 1. eauto using sn.
Qed.

Lemma R_step p P Q :
  step P Q -> R p P -> R p Q.
Proof.
  intros ? []. eauto.
Qed.

Lemma R_var p n :
  R p (var n).
Proof.
  econstructor. intros [=].
  intros Q H. inversion H.
Qed.

Lemma R_ren ξ1 ξ2 p P :
  R p P -> R p (ren_term ξ1 ξ2 P).
Proof.
  induction 1 as [P H H0 H1]. econstructor.
  - intros HnP ξ'1 ξ'2. asimpl. eapply H. now destruct P.
  - intros Q.  erewrite rinst_inst_term; try reflexivity.
    intros (P' & H2 & <-) % step_subst_inv.
    erewrite <- rinst_inst_term; try reflexivity. eauto.
Qed.

(* ** Logical Relation  *)

Lemma K_var n ρ P :
  K (poly_var n) ρ P = forall ξ1 ξ2, ρ n (ren_term ξ1 ξ2 P).
Proof.
  reflexivity.
Qed.

Lemma K_arr s t ρ u P :
  K (poly_arr s t) ρ (abs u P) <->
  forall ξ1 ξ2 Q, E s ρ Q -> E t ρ (subst_term (ξ1 >> poly_var) (Q .: ξ2 >> var) P).
Proof.
  unfold M. cbn. pw. asimpl. eapply R_ext. reflexivity.
  now_asimpl.
Qed.

Lemma K_all s ρ P :
  K (poly_abs s) ρ (ty_abs P) <->
  forall ξ p t, E s (p .: ρ) (subst_term (t .: ξ >> poly_var) var P).
Proof.
  unfold M. split.
  - intros H ξ p t. specialize (H ξ id p t). fold ren_term in H.
    eapply R_ext. 3:eapply H. reflexivity. now_asimpl.
  - intros H ξ1 ξ2 p t. specialize (H ξ1 p t).
    pose proof (Hren := R_ren id ξ2 _ _ H). asimpl in Hren.
    eapply R_ext. 3:eapply Hren. reflexivity. now_asimpl.
Qed.

Lemma V_weaken s ρ p :
  V (ren_poly_type shift s) (p .: ρ) == V s ρ.
Proof.
  now rewrite eval_weaken.
Qed.

Lemma K_weaken s ρ p :
  K (ren_poly_type shift s) (p .: ρ) == K s ρ.
Proof.
  intros P. pw. eapply V_weaken.
Qed.

Lemma E_weaken s ρ p :
  E (ren_poly_type shift s) (p .: ρ) == E s ρ.
Proof.
  intros P. eapply R_ext. eapply V_weaken. reflexivity.
Qed.

Lemma V_beta s t ρ :
  V (subst_poly_type (t .: poly_var) s) ρ == V s (V t ρ .: ρ).
Proof.
  now rewrite eval_beta. 
Qed.

Lemma E_beta  s t ρ :
  E (subst_poly_type (t .: poly_var) s) ρ == E s (V t ρ .: ρ).
Proof.
  intros P. now rewrite eval_beta. 
Qed.

(* ** Logical relation on contexts  *)

Definition C (Γ : nat -> poly_type) (ρ : nat -> tpred) : (nat -> term) -> Prop :=
  fun σ => forall n, E (Γ n) ρ (σ n).

Lemma C_ext :
  Proper (pointwise_relation _ eq ==> eq ==> eq ==> iff) C.
Proof.
  split; repeat intros ?; subst. now rewrite <- H. now rewrite H.
Qed.

Lemma C_scons s Γ ρ σ P :
  E s ρ P -> C Γ ρ σ -> C (s .: Γ) ρ (P .: σ).
Proof.
  intros HE HC. hnf. intros []. eassumption. eapply HC.
Qed.

Lemma C_rename Γ ρ σ ξ1 ξ2 :
  C Γ ρ σ -> C Γ ρ (σ >> ren_term ξ1 ξ2).
Proof.
  intros H ?. eapply R_ren, H.
Qed.

Lemma C_up s Γ ρ σ :
  C Γ ρ σ -> C (s .: Γ) ρ (up_term_term σ).
Proof.
  intros H. eapply C_scons. eapply R_var. now eapply C_rename.
Qed.

(* ** Fundamental theorem & Strong Normalisation  *)
Lemma E2_ind s t ρ1 ρ2 p :
  (forall P Q, E s ρ1 P -> E t ρ2 Q -> (forall P', step P P' -> p P' Q) -> (forall Q', step Q Q' -> p P Q') -> p P Q) ->
  forall P Q, E s ρ1 P -> E t ρ2 Q -> p P Q.
Proof.
  intros H P Q. 
  induction 1 in Q |- *. induction 1. 
  eapply H; eauto using R.
Qed.

Lemma E_app s t P Q ρ :
  E (poly_arr s t) ρ P -> E s ρ Q -> E t ρ (app P Q).
Proof.
  revert P Q. eapply E2_ind.
  intros P Q nP nQ IHP IHQ. econstructor.
  inversion 1. intros R Hst. inv Hst; eauto.
  destruct nP. rewrite K_arr in H; eauto.
Qed.

Lemma E_lam s t s' ρ P :
  sn P ->
  (forall ξ1 ξ2 Q, E s ρ Q -> E t ρ (subst_term (ξ1 >> poly_var) (Q .: ξ2 >> var) P)) ->
  E (poly_arr s t) ρ (abs s' P).
Proof.
    induction 1 as [P _ IH]. intros H.
    econstructor.
    - intros _. rewrite K_arr. eauto.
    - intros Q Hst. inv Hst. eapply IH; eauto.
      intros. eapply R_step; eauto using step_subst.
Qed.

Lemma E_tapp s t ρ P r :
  E (poly_abs s) ρ P -> E (subst_poly_type (t .: poly_var) s) ρ (ty_app P r).
Proof.
  induction 1 as [P H IH H2]. eapply E_beta.
  econstructor. inversion 1. intros Q Hst. inv Hst.
  - specialize (H eq_refl). rewrite K_all in H. eauto.
  - eapply H2 in H4. now eapply E_beta in H4.
Qed.

Lemma E_tlam s ρ P :
  sn P ->
  (forall ξ p t, E s (p .: ρ) (subst_term (t .: ξ >> poly_var) var P)) ->
  E (poly_abs s) ρ (ty_abs P).
Proof.
  induction 1 as [P _ IH]. intros H. econstructor.
  - rewrite K_all. intros _. eapply H.
  - intros Q Hst. inv Hst. eapply IH. eauto.
    intros ξ p t.
    eapply R_step; eauto using step_subst.
Qed.

Lemma fundamental {Γ s P} :
  typing Γ P s ->
  forall σ τ ρ, 
  C (fun n => match List.nth_error Γ n with Some x => x | _ => poly_abs (poly_var 0) end) ρ τ -> 
  E s ρ (subst_term σ τ P).
Proof.
  induction 1 as [Γ n s H | | Γ | | ]; intros σ τ ρ HC.
  - specialize (HC n). cbn in HC. rewrite H in HC. eapply HC.
  - cbn. eapply E_app; eauto.
  -  eapply E_lam; fold subst_term.
     + eapply R_sn. eapply IHtyping.
       eapply C_ext. 4:{ eapply C_up, HC. }
       all: try reflexivity.
       now intros []. 
     + intros ξ1 ξ2 Q HQ.
       match goal with [ |- E _ _ ?R] => 
                       replace R with (subst_term (σ >> ren_poly_type ξ1) (Q .: τ >> ren_term ξ1 ξ2) P)
       end.
       * eapply IHtyping. eapply C_ext.
         4:{ eapply C_scons. eauto. eapply C_rename, HC. }
         all: try reflexivity.
         intros []; cbn; try reflexivity.
       * asimpl. eapply ext_term. intros. asimpl.
         -- erewrite rinst_inst_poly_type; reflexivity.
         -- intros []. reflexivity. asimpl.
            erewrite rinst_inst_term; try reflexivity. now asimpl.
  - cbn. eapply E_tapp; eauto.
  - cbn. eapply E_tlam.
    + specialize (IHtyping (up_poly_type_poly_type σ) (τ >> ren_term shift id) ((fun _ => False) .: ρ)).
      eapply R_sn. refine (IHtyping _).
      intros n.
      rewrite List.nth_error_map.
      destruct List.nth_error eqn:Eq.
      * cbn. asimpl. eapply E_weaken.
        specialize (HC n). cbn in HC. rewrite Eq in HC.
        eapply R_ren, HC.
      * unfold ssrfun.Option.map, ssrfun.Option.bind, ssrfun.Option.apply.
        eapply R_ren. specialize (HC n). cbn in HC.
        rewrite Eq in HC. eapply HC.
    + intros ξ p t. asimpl. eapply IHtyping.
      intros n. asimpl. eapply R_ext. 2:reflexivity.
      2:{ eapply E_weaken.
          erewrite <- rinst_inst_term; try reflexivity.
          eapply R_ren. eapply HC. }
      * f_equal. rewrite List.nth_error_map.
        now destruct List.nth_error eqn:Eq.
Qed.

Lemma SN {Gamma P t} : typing Gamma P t -> sn P.
Proof.
  intros Htp. pose proof (fundamental Htp poly_var var (fun _ _ => False)).
  asimpl in H.
  eapply R_sn, H.
  intros n. eapply R_var.
Qed.

Lemma typing_normal_form {Gamma P t} : typing Gamma P t -> exists Q, normal_form Q /\ typing Gamma Q t.
Proof.
  intros H.
  destruct (sn_normal _ _ _ H (SN H)) as (Q & H1 & H2).
  exists Q. split. eassumption. eapply preservation_star; eauto.
Qed.
