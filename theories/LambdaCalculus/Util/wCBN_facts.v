From Undecidability.LambdaCalculus Require Import Lambda Util.term_facts.
Import L.L (term, var, app, lam).
Require Import Undecidability.L.Util.L_facts.
Import Lambda (subst, wCBN_step, wCBN_stepApp, wCBN_stepSubst).
From Stdlib Require Import Relations Lia.

From Stdlib Require Import ssreflect.

Set Default Goal Selector "!".

#[local] Notation step := wCBN_step.
#[local] Notation steps := (clos_refl_trans _ step).

Inductive stepLam_spec s t : term -> Prop :=
  | stepLam_spec_intro : stepLam_spec s t (subst (scons t var) s).
Inductive stepApp_spec s t : term -> Prop :=
  | stepApp_spec_intro : forall s', step s s' -> stepApp_spec s t (app s' t).

Lemma stepE {s t} : step s t ->
  match s with
  | app (lam s') t' => stepLam_spec s' t' t
  | app s' t' => stepApp_spec s' t' t
  | _ => False
  end.
Proof. by elim; [|case]. Qed.

Lemma step_fun s t1 t2 : step s t1 -> step s t2 -> t1 = t2.
Proof.
  move=> H. elim: H t2.
  - by move=> > /stepE [].
  - case.
    + by move=> > /stepE.
    + by move=> > ? IH ? /stepE [] ? /IH ->.
    + by move=> > /stepE.
Qed.

Lemma step_bound s k t : step s t -> bound k s -> bound k t.
Proof.
  elim.
  - move=> > /boundE [/boundE /bound_subst +] ?. apply.
    move=> [|n] /=; first done.
    move=> ?. constructor. lia.
  - move=> > ? ? /boundE [? ?].
    constructor; by auto with nocore.
Qed.

Lemma stepLam' s t t' : t' = (subst (scons t var) s) -> step (app (lam s) t) t'.
Proof. move=> ->. by apply: wCBN_stepSubst. Qed.

Lemma step_closed s t : step s t -> closed s -> closed t.
Proof. by move=> /step_bound + /closed_dcl => /[apply] /closed_dcl. Qed.

Lemma steps_bound k {s t} : steps s t -> bound k s -> bound k t.
Proof. elim; by eauto using step_bound. Qed.

Lemma closed_halt_iff {t} : closed t -> ((exists t', t = lam t') <-> (forall u, not (step t u))).
Proof.
  intros Ht. split. { by move=> [? ->] ? /stepE. }
  suff: (forall s t, closed s -> closed t -> exists u, step (app s t) u).
  { case: t Ht.
    - by move=> ? /not_closed_var.
    - move=> s t /closed_app [++] H => /H /[apply].
      by move=> [u] Hu /(_ u Hu).
    - move=> *. by eexists. }
  elim.
  - by move=> > /not_closed_var.
  - move=> ? IH1 ? IH2 ? /closed_app [/IH1] /[apply].
    move=> [u Hu] ?. eexists. apply: wCBN_stepApp. by eassumption.
  - move=> *. eexists. by apply: wCBN_stepSubst.
Qed.

Lemma stepsApp M1 M2 N : steps M1 M2 -> steps (app M1 N) (app M2 N).
Proof.
  elim=> *.
  - apply: rt_step. by apply: wCBN_stepApp.
  - apply: rt_refl.
  - by apply: rt_trans; eassumption.
Qed.
