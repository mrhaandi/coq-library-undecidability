(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(*
  Synopsis:
    Facts about the pts-terms in beta-normal form.
*)

Require Import Undecidability.SemiUnification.HOSemiU.
Require Import Undecidability.SemiUnification.autosubst.unscoped.
Require Import Undecidability.SemiUnification.autosubst.pts.
Require Import Undecidability.SemiUnification.autosubst.pts_more.
Require Import Undecidability.SemiUnification.autosubst.allfv_more.

Require Import Undecidability.SemiUnification.PTSUtil.step_facts.
Require Import Undecidability.SemiUnification.PTSUtil.red_beta_facts.

Require Import Relations.Relation_Operators Relations.Operators_Properties.
Require Import ssreflect ssrbool ssrfun.

Lemma normalE {P} : normal P ->
  match P with
  | var _ => True
  | const _ => True 
  | app (lam _ _) _ => False
  | app P Q => normal P /\ normal Q
  | lam P Q => normal P /\ normal Q
  | Pi P Q => normal P /\ normal Q
  end.
Proof.
Admitted.

Lemma normal_varI {x} : normal (var x).
Proof. by move=> ? /stepE. Qed. 

Lemma normal_constI {x} : normal (const x).
Proof. by move=> ? /stepE. Qed. 

Lemma normal_lamI {P Q} : normal P -> normal Q -> normal (lam P Q).
Proof. move=> HP HQ R /stepE. by case => - [?] [_] => [/HP | /HQ]. Qed.

Lemma normal_PiI {P Q} : normal P -> normal Q -> normal (Pi P Q).
Proof. move=> HP HQ R /stepE. by case => - [?] [_] => [/HP | /HQ]. Qed.

Lemma normal_ren_termE xi {P} : normal (ren_term xi P) -> normal P.
Proof. by move=> HP Q /(step_ren_termI xi) /HP. Qed.

Lemma normal_dec (P: term) : (normal P) + { Q | step P Q }.
Proof.
  elim: P.
  - move=> >. left. by apply: normal_varI.
  - move=> >. left. apply: normal_constI.
  - move=> P [IHP|[P' ?]] Q; first last.
    { move=> _. right. exists (app P' Q). by apply: step_appL. }
    move=> [IHQ|[Q' ?]]; first last.
    { right. exists (app P Q'). by apply: step_appR. }
    case: P IHP => > ?.
    + left=> ? /stepE. by firstorder done.
    + left=> ? /stepE. by firstorder done.
    + left=> ? /stepE. by firstorder done.
    + right. eexists. by apply: step_beta.
    + left=> ? /stepE. by firstorder done.
  - move=> P [IHP|[P' ?]] Q; first last.
    { move=> _. right. exists (lam P' Q). by apply: step_lamL. }
    move=> [IHQ|[Q' ?]]; first last.
    { right. exists (lam P Q'). by apply: step_lamR. }
    left. by apply: normal_lamI.
  - move=> P [IHP|[P' ?]] Q; first last.
    { move=> _. right. exists (Pi P' Q). by apply: step_PiL. }
    move=> [IHQ|[Q' ?]]; first last.
    { right. exists (Pi P Q'). by apply: step_PiR. }
    left. by apply: normal_PiI.
Qed.


(* TODO move to normal_facts ? *)
Lemma normalize {P: term} : normalizing P -> { Q | normal Q /\ red_beta P Q }.
Proof.
  elim => {}P. case: (normal_dec P).
  - move=> *. exists P. by constructor; [ | apply: rt_refl ].
  - move=> [Q HPQ] => _ /(_ Q HPQ) - [R] [? ?].
    exists R. constructor; first done.
    apply: rt_trans; [apply: rt_step|]; by eassumption.
Qed.

(* a normal term is trivially normalizing *)
Lemma normalizing_normal {P} : normal P -> normalizing P.
Proof. move=> HP. by constructor => ? /HP. Qed.

