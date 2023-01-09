(*
  Reduction from:
    Intersection Type Typability (CD_TYP)
  to:
    Intersection Type Type Checking (CD_TC)
*)

From Undecidability.IntersectionTypes Require Import CD Util.CD_facts.

Require Import List PeanoNat Lia.
Require Import ssreflect ssrbool ssrfun.

Import CD (var, app, lam).

Fixpoint var_bound M :=
  match M with
  | var x => 1 + x
  | app M N => 1 + var_bound M + var_bound N
  | lam M => var_bound M
  end.

Lemma var_bound_spec M : forall_fv (fun x => x < var_bound M) M.
Proof.
  elim: M=> /=.
  - lia.
  - move=> ? IH1 ? IH2. split.
    + apply: forall_fv_impl IH1. lia.
    + apply: forall_fv_impl IH2. lia.
  - move=> ?. by apply: forall_fv_impl=> - [|?] /=; [|lia].
Qed.

Lemma var_bound_spec' Gamma M t : type_assignment Gamma M t -> 
  type_assignment (map (fun i => match nth_error Gamma i with Some phi => phi | None => (atom 0, nil) end) (seq 0 (var_bound M))) M t.
Proof.
  move=> /type_assignment_ren_fv => /(_ _ id). rewrite simpl_tm. apply.
  apply: forall_fv_impl (var_bound_spec M) => x ?.
  move=> > /(@nth_error_split ty) [Gamma1] [Gamma2] [-> ?]. subst x.
  rewrite nth_error_map nth_error_seq /=; first done.
  by rewrite nth_error_app2 ?Nat.sub_diag.
Qed.

Lemma abs_Gamma_spec Gamma M t : type_assignment Gamma M t -> exists t', type_assignment nil (Nat.iter (length Gamma) lam M) t'.
Proof.
  elim: Gamma M t. { move=> ???. eexists. by eassumption. }
  move=> [s phi] Gamma IH ?? /type_assignment_arr /IH /=.
  congr ex. congr type_assignment.
  elim: (length Gamma). { done. }
  by move=> ? /= ->.
Qed.

Require Import Undecidability.Synthetic.Definitions.

(* reduction from intersection type typability to intersection type type checking *)
Theorem reduction : CD_TYP ⪯ CD_TC.
Proof.
  exists (fun M => (nil, app (lam (lam (var 0))) (Nat.iter (var_bound M) lam M), arr (atom 0) nil (atom 0))).
  move=> M. split.
  - move=> [Gamma] [t] /var_bound_spec' /abs_Gamma_spec [t'].
    rewrite /= map_length seq_length=> ?. econstructor.
    + do 3 econstructor; first done. by left.
    + by eassumption.
    + by apply: Forall_nil.
  - move=> /= /type_assignmentE [] s phi _ + _.
    elim: (var_bound M) (nil) (s).
    { move=> ???. do 2 eexists. by eassumption. }
    move=> ? IH ? [?|???] /= /type_assignmentE; first done.
    by apply: IH.
Qed.
