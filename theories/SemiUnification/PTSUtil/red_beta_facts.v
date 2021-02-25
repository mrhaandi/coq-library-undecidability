(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(*
  Synopsis:
    Facts about the multi-step beta reduction relation for pts-terms.
*)

Require Import Undecidability.SemiUnification.HOSemiU.
Require Import Undecidability.SemiUnification.autosubst.pts.
Require Import Undecidability.SemiUnification.autosubst.pts_more.
Require Import Undecidability.SemiUnification.autosubst.allfv_more.

Require Import Undecidability.SemiUnification.PTSUtil.step_facts.

Require Import Relations.Relation_Operators Relations.Operators_Properties.
Require Import ssreflect ssrbool ssrfun.

(* multi-step beta reduction is the reflexive, transitive closure 
  of of the single-step beta reduction *)
Definition red_beta := clos_refl_trans term step.

(* Fallstudie für Adrian *)
Lemma red_beta_diamond {P Q1 Q2} : red_beta P Q1 -> red_beta P Q2 -> 
  { Q | red_beta Q1 Q /\ red_beta Q2 Q }.
Proof.
Admitted.

Definition rt_rt1n := clos_rt_rt1n_iff.
Arguments rt_step {A R x y}.

Lemma red_beta_XI X P P' Q Q' : (X = app \/ X = lam \/ X = Pi) -> 
  red_beta P P' -> red_beta Q Q' -> red_beta (X P Q) (X P' Q').
Proof.
  move=> HX /rt_rt1n H. elim: H Q Q'.
  - move=> >. elim => *.
    + apply: rt_step.
      move: HX => [|[|]] ->; by eauto using step with nocore.
    + by apply: rt_refl.
    + apply: rt_trans; by eassumption.
  - move=> > ? ? IH > /IH ?.
    apply: rt_trans; last by eassumption.
    apply: rt_step. 
    move: HX => [|[|]] ->; by eauto using step with nocore.
Qed.

(* TODO move to red_beta facts *)
Corollary red_beta_appI P P' Q Q' : red_beta P P' -> red_beta Q Q' -> red_beta (app P Q) (app P' Q').
Proof. apply: red_beta_XI; by tauto. Qed.

(* TODO move to red_beta facts *)
Lemma red_beta_lamI P P' Q Q' : red_beta P P' -> red_beta Q Q' -> red_beta (lam P Q) (lam P' Q').
Proof. apply: red_beta_XI; by tauto. Qed.

(* TODO move to red_beta facts *)
Lemma red_beta_PiI P P' Q Q' : red_beta P P' -> red_beta Q Q' -> red_beta (Pi P Q) (Pi P' Q').
Proof. apply: red_beta_XI; by tauto. Qed.

(* transport f-image of step to eq_beta *)
Lemma red_beta_fI f : 
  (forall P Q, step P Q -> step (f P) (f Q)) -> 
  forall P Q, red_beta P Q -> red_beta (f P) (f Q).
Proof.
  move=> H ? ? /rt_rt1n. elim; first by (move=> *; apply: rt_refl).
  move=> > ? _ ?. apply: rt_trans; last by eassumption.
  apply: rt_step. by apply: H.
Qed.

Corollary red_beta_ren_termI xi {P Q} : red_beta P Q -> 
  red_beta (ren_term xi P) (ren_term xi Q).
Proof. apply: red_beta_fI => *. by apply: step_ren_termI. Qed.

Corollary red_beta_subst_termI {sigma P Q} : red_beta P Q  -> 
  red_beta (subst_term sigma P) (subst_term sigma Q).
Proof. apply: red_beta_fI => *. by apply: step_subst_termI. Qed.

Lemma red_beta_allfv_term_impl {p P Q} : red_beta P Q -> allfv_term p P -> allfv_term p Q.
Proof.
  elim.
  - move=> >. by apply: step_allfv_term_impl.
  - done.
  - by move=> > _ IH1 _ IH2 /IH1.
Qed.

(* TODO move to red_beta facts *)
(* todo rename such properties to transport? what i the name? not ext_? *)
Lemma ext_red_beta_subst_term {sigma tau P} : (forall x, red_beta (sigma x) (tau x)) -> 
  red_beta (subst_term sigma P) (subst_term tau P).
Proof.
  elim: P sigma tau.
  - move=> >. by apply.
  - move=> *. by apply: rt_refl.
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: red_beta_appI; [by apply: IHP | by apply: IHQ].
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: red_beta_lamI; first by apply IHP.
    apply: IHQ. case; first by apply: rt_refl.
    move=> x /=. by apply: red_beta_ren_termI.
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: red_beta_PiI; first by apply IHP.
    apply: IHQ. case; first by apply: rt_refl.
    move=> x /=. by apply: red_beta_ren_termI.
Qed.

(* multi-step beta case analysis *)
Lemma red_betaE {P Q} : red_beta P Q ->
  match P with
  | var _ => Q = P
  | const _ => Q = P
  | app P1 P2 => 
      (exists Q1 Q2, Q = app Q1 Q2 /\ red_beta P1 Q1 /\ red_beta P2 Q2) \/
      (exists P11 P12, red_beta P1 (lam P11 P12) /\ red_beta (subst_term (scons P2 var) P12) Q)
  | lam P1 P2 => exists Q1 Q2, Q = lam Q1 Q2 /\ red_beta P1 Q1 /\ red_beta P2 Q2
  | Pi P1 P2 => exists Q1 Q2, Q = Pi Q1 Q2 /\ red_beta P1 Q1 /\ red_beta P2 Q2
  end.
Proof.
  move=> /rt_rt1n. elim.
  - case.
    + done.
    + done.
    + move=> ? ?. left. 
      do 2 eexists. constructor; first by reflexivity.
      constructor; by apply: rt_refl.
    + move=> ? ?. 
      do 2 eexists. constructor; first by reflexivity.
      constructor; by apply: rt_refl.
    + move=> ? ?. 
      do 2 eexists. constructor; first by reflexivity.
      constructor; by apply: rt_refl.
  - move=> > [].
    + move=> > ? _. right. 
      do 2 eexists. constructor; first by apply: rt_refl.
      by apply /rt_rt1n.
    + move=> > ? _ [].
      * move=> [?] [?] [->] [? ?]. left.
        do 2 eexists. constructor; first by reflexivity.
        constructor; last done.
        apply: rt_trans; last by eassumption.
        by apply: rt_step.
      * move=> [?] [?] [?] ?. subst. right.
        do 2 eexists. constructor; last by eassumption.
        by apply: rt_trans; [apply: rt_step | by eassumption].
    + move=> > ? _ [].
      * move=> [?] [?] [->] [? ?]. left.
        do 2 eexists. constructor; first by reflexivity.
        constructor; first done.
        apply: rt_trans; last by eassumption.
        by apply: rt_step.
      * move=> [?] [?] [?] ?. subst. right.
        do 2 eexists. constructor; first by eassumption.
        apply: rt_trans; last by eassumption.
        apply: ext_red_beta_subst_term. case; first by apply: rt_step.
        move=> *. by apply: rt_refl.
    + move=> > /rt_step ? _ [?] [?] [->] [? ?].
      do 2 eexists. constructor; first by reflexivity.
      by constructor; first by (apply: rt_trans; eassumption).
    + move=> > /rt_step ? _ [?] [?] [->] [? ?].
      do 2 eexists. constructor; first by reflexivity.
      by constructor; last by (apply: rt_trans; eassumption).
    + move=> > /rt_step ? _ [?] [?] [->] [? ?].
      do 2 eexists. constructor; first by reflexivity.
      by constructor; first by (apply: rt_trans; eassumption).
    + move=> > /rt_step ? _ [?] [?] [->] [? ?].
      do 2 eexists. constructor; first by reflexivity.
      by constructor; last by (apply: rt_trans; eassumption).
Qed.

Lemma red_beta_normal {P Q} : red_beta P Q -> normal P -> P = Q.
Proof.
  case /rt_rt1n; first done.
  by move=> > + _ H => /H.
Qed.
