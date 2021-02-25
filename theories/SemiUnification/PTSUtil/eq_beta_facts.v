(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(*
  Synopsis:
    Facts about the beta-equivalence relation for pts-terms.
*)

Require Import Undecidability.SemiUnification.HOSemiU.
Require Import Undecidability.SemiUnification.autosubst.pts.
Require Import Undecidability.SemiUnification.autosubst.pts_more.
Require Import Undecidability.SemiUnification.autosubst.allfv_more.

Require Import Undecidability.SemiUnification.PTSUtil.step_facts.
Require Import Undecidability.SemiUnification.PTSUtil.red_beta_facts.

Require Import Relations.Relation_Operators Relations.Operators_Properties.
Require Import ssreflect ssrbool ssrfun.

Local Notation "P =β Q" := (eq_beta P Q) (at level 50).

Definition rst_rst1n := clos_rst_rst1n_iff.

(* transport f-image of step to eq_beta *)
Lemma eq_beta_fI f : 
  (forall P Q, step P Q -> step (f P) (f Q)) -> 
  forall P Q, eq_beta P Q -> eq_beta (f P) (f Q).
Proof.
  move=> H ? ? /rst_rst1n. elim; first by (move=> *; apply: rst_refl).
  move=> > [] ? _ ?; (apply: rst_trans; last by eassumption).
  - apply: rst_step. by apply: H.
  - apply: rst_sym. apply: rst_step. by apply: H.
Qed.

Corollary eq_beta_ren_termI xi {P Q} : eq_beta P Q -> 
  eq_beta (ren_term xi P) (ren_term xi Q).
Proof. apply: eq_beta_fI => *. by apply: step_ren_termI. Qed.

Corollary eq_beta_subst_termI {sigma P Q} : eq_beta P Q  -> 
  eq_beta (subst_term sigma P) (subst_term sigma Q).
Proof. apply: eq_beta_fI => *. by apply: step_subst_termI. Qed.

Lemma eq_beta_XI X P P' Q Q' : (X = app \/ X = lam \/ X = Pi) ->
  eq_beta P P' -> eq_beta Q Q' -> eq_beta (X P Q) (X P' Q').
Proof.
  move=> HX /rst_rst1n. elim.
  - move=> ? /rst_rst1n. elim; first by (move=> *; apply: rst_refl).
    move=> > [] /rt_step H1 _ IH; 
      (apply: rst_trans; last by eassumption).
    + apply: clos_rt_clos_rst. 
      by apply: red_beta_XI; [| apply: rt_refl |].
    + apply: rst_sym. apply: clos_rt_clos_rst. 
      by apply: red_beta_XI; [| apply: rt_refl |].
  - move=> > [] /rt_step H1 _ IH /IH H2; 
      (apply: rst_trans; last by eassumption).
    + apply: clos_rt_clos_rst.
      by apply: red_beta_XI; [| | apply: rt_refl].
    + apply: rst_sym. apply: clos_rt_clos_rst. 
      by apply: red_beta_XI; [| | apply: rt_refl].
Qed.

Corollary eq_beta_appI P P' Q Q' : eq_beta P P' -> eq_beta Q Q' -> eq_beta (app P Q) (app P' Q').
Proof. apply: eq_beta_XI. by tauto. Qed.

Corollary eq_beta_lamI P P' Q Q' : eq_beta P P' -> eq_beta Q Q' -> eq_beta (lam P Q) (lam P' Q').
Proof. apply: eq_beta_XI. by tauto. Qed.

Corollary eq_beta_PiI P P' Q Q' : eq_beta P P' -> eq_beta Q Q' -> eq_beta (Pi P Q) (Pi P' Q').
Proof. apply: eq_beta_XI. by tauto. Qed.

Lemma ext_eq_beta_subst_term {sigma tau P} : (forall x, eq_beta (sigma x) (tau x)) -> 
  eq_beta (subst_term sigma P) (subst_term tau P).
Proof.
  elim: P sigma tau.
  - move=> >. by apply.
  - move=> *. by apply: rst_refl.
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: eq_beta_appI; [by apply: IHP | by apply: IHQ].
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: eq_beta_lamI; first by apply IHP.
    apply: IHQ. case; first by apply: rst_refl.
    move=> x /=. by apply: eq_beta_ren_termI.
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: eq_beta_PiI; first by apply IHP.
    apply: IHQ. case; first by apply: rst_refl.
    move=> x /=. by apply: eq_beta_ren_termI.
Qed.

Lemma eq_beta_normal {P Q} : normal Q -> eq_beta P Q -> red_beta P Q.
Proof.
  move=> HQ /rst_rst1n HPQ. 
  elim: HPQ HQ; first by (move=> *; apply: rt_refl).
  move=> {}P R {}Q [|].
  - move=> /rt_step ? _ IH ?. 
    apply: rt_trans; [by eassumption | by apply: IH].
  - move=> /rt_step HRP _ IH HQ.
    have [Q' [HPQ' /red_beta_normal HQQ']] := red_beta_diamond HRP (IH HQ).
    by rewrite (HQQ' HQ).
Qed.
