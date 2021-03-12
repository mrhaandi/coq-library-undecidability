Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
Require Import Undecidability.FOL.ZF.
From Undecidability.FOL.Util Require Import FullTarski FullDeduction_facts Aczel_CE Aczel_TD ZF_model.
From Undecidability.FOL.Reductions Require Import PCPb_to_ZFeq PCPb_to_ZF PCPb_to_ZFD.

From Undecidability.PCP Require Import PCP PCP_undec Util.PCP_facts Reductions.PCPb_iff_dPCPb.

(* Semantic entailment in full ZF restricted to extensional models *)

Theorem PCPb_entailment_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> PCPb ⪯ entailment_ZF.
Proof.
  intros H. exists solvable. intros B. apply PCP_ZF. apply H.
Qed.

Theorem undecidable_entailment_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable entailment_ZF.
Proof.
  intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_entailment_ZF.
Qed.

Corollary undecidable_model_entailment_ZF :
  CE -> TD -> undecidable entailment_ZF.
Proof.
  intros H1 H2. now apply undecidable_entailment_ZF, normaliser_model.
Qed.

(* Semantic entailment in ZF' restricted to extensional models *)

Theorem PCPb_entailment_ZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> PCPb ⪯ entailment_ZF'.
Proof.
  intros H. exists solvable. intros B. apply PCP_ZF'. apply H.
Qed.

Theorem undecidable_entailment_ZF' :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, In psi ZF' -> rho ⊨ psi) -> undecidable entailment_ZF'.
Proof.
  intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_entailment_ZF'.
Qed.

Corollary undecidable_model_entailment_ZF' :
  CE -> undecidable entailment_ZF'.
Proof.
  intros H. now apply undecidable_entailment_ZF', extensionality_model.
Qed.

(* Semantic entailment in ZFeq' allowing for intensional models *)

Theorem PCPb_entailment_ZFeq' :
  PCPb ⪯ entailment_ZFeq'.
Proof.
  exists solvable. intros B. split; intros H.
  - eapply PCP_ZFD, soundness in H. intros D M rho H'. apply H, H'.
  - now apply PCP_ZFeq'; try apply intensional_model.
Qed.

Theorem undecidable_entailment_ZFeq' :
  undecidable entailment_ZFeq'.
Proof.
  apply (undecidability_from_reducibility PCPb_undec), PCPb_entailment_ZFeq'.
Qed.

(* Intuitionistic deduction in full ZFeq *)

Theorem PCPb_deduction_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> PCPb ⪯ deduction_ZF.
Proof.
  intros (V & M & H1 & H2 & H3).
  exists solvable. intros B. split.
  - intros H % (@PCP_ZFD intu). exists ZFeq'. split; eauto using ZFeq.
  - intros H'. specialize (tsoundness H'). clear H'. intros H'.
    apply PCPb_iff_dPCPb. eapply PCP_ZF2; eauto using ZF.
    apply (H' V M (fun _ => ∅)). intros psi [].
    + apply extensional_eq; eauto using ZF.
    + apply H3. constructor 2.
    + apply H3. constructor 3.
Qed.

Theorem undecidable_deduction_ZF :
  (exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi) -> undecidable deduction_ZF.
Proof.
   intros H. now apply (undecidability_from_reducibility PCPb_undec), PCPb_deduction_ZF.
Qed.

Corollary undecidable_model_deduction_ZF :
  CE -> TD -> undecidable deduction_ZF.
Proof.
  intros H1 H2. now apply undecidable_deduction_ZF, normaliser_model.
Qed.

(* Intuitionistic deduction in ZFeq' *)

Theorem PCPb_deduction_ZF' :
  PCPb ⪯ deduction_ZF'.
Proof.
  exists solvable. intros B. split; try apply PCP_ZFD.
  intros H' % soundness. apply PCP_ZFeq'; try apply intensional_model.
  intros D M rho H. apply H', H.
Qed.

Corollary undecidable_deduction_entailment_ZF' :
  undecidable deduction_ZF'.
Proof.
  apply (undecidability_from_reducibility PCPb_undec), PCPb_deduction_ZF'.
Qed.


