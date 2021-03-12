(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    
*)

(*
  Literature:
    [1] Barendregt, Henk P. "Introduction to generalized type systems." (1991).
*)

Require Import List Relation_Operators.
Import ListNotations.

Require Import Undecidability.SemiUnification.autosubst.unscoped.
Require Import Undecidability.SemiUnification.autosubst.pts.
Require Import Undecidability.SemiUnification.autosubst.pts_more.
Require Import Undecidability.SemiUnification.autosubst.allfv_more.

Require Import Undecidability.SemiUnification.HOSemiU.

(* System Fω type environments *)
Definition environment := list term.

(* "*" is "const 0", "□" is "const 1" *)
Definition axioms : list (nat * nat) := [(0, 0); (1, 0); (1, 1)].

(* System Fω type assignment as a pure type system [1] *)
(* Γ ⊢ P : Q is type_assignment Γ P Q *)
Inductive type_assignment : environment -> term -> term -> Prop :=
  | type_assignment_ax {Gamma} :
    type_assignment Gamma (const 0) (const 1)
  | type_assignment_var {Gamma x s A} :
    type_assignment Gamma A (const s) ->
    nth_error Gamma x = Some A ->
    type_assignment Gamma (var x) A
  | type_assignment_app {Gamma P Q A B} :
    type_assignment Gamma P (Pi A B) -> type_assignment Gamma Q A -> 
    type_assignment Gamma (app P Q) (subst_term (scons Q var) B)
  | type_assignment_Pi {Gamma s1 s2 A B} : 
    In (s1, s2) axioms ->
    type_assignment Gamma A (const s1) ->
    type_assignment (A :: Gamma) B (const s2) ->
    type_assignment Gamma (Pi A B) (const s2)
  | type_assignment_lam {Gamma s1 s2 A B P} :
    In (s1, s2) axioms -> 
    type_assignment Gamma A (const s1) ->
    type_assignment (A :: Gamma) P B ->
    type_assignment (A :: Gamma) B (const s2) ->
    type_assignment Gamma (lam A P) (Pi A B)
  | type_assignment_eq {Gamma P s A B}: 
    type_assignment Gamma P A ->
    type_assignment Gamma B (const s) ->
    eq_beta A B ->
    type_assignment Gamma P B.

(* kinds : k1, k2 ::= * | k1 => k2 *)
(* well-formed kind *)
Fixpoint kind (P: term) : Prop :=
  match P with
  | const 0 => True
  | Pi P Q => kind P /\ kind Q
  | _ => False
  end.

(* pre-types sigma, tau := 
  x | sigma -> tau | forall (x : k).sigma | app sigma tau | lambda (x : k).sigma *)
Fixpoint pre_type (P: term) : Prop :=
  match P with
  | var _ => True
  | const _ => False
  | app P Q => pre_type P /\ pre_type Q
  | lam P Q => kind P /\ pre_type Q
  | Pi P Q => 
    (kind P /\ pre_type Q) \/ (* forall (x : P). Q*)
    (pre_type P /\ pre_type Q /\ exists Q', Q = ren_term shift Q') (* P -> Q *)
  end.

Fixpoint pre_term (P: term) : Prop :=
  match P with
  | var _ => True
  | const _ => False
  | app P Q => pre_term P /\ (pre_term Q \/ pre_type Q)
  | lam P Q => (pre_type P \/ kind P) /\ pre_term Q
  | Pi P Q => False
  end.

Require Import ssreflect ssrbool ssrfun.

(* "□" is not assigned any term *)
Lemma sanity_box {Gamma A} : type_assignment Gamma (const 1) A -> False.
Proof. move HB: (const 1) => B H. by elim: H HB. Qed.

Lemma kind_allfv_termI p A : kind A -> allfv_term p A.
Proof.
  elim: A p => //=.
  move=> ? IH1 ? IH2 ? [? ?].
  by constructor; [apply: IH1 | apply: IH2].
Qed.

Lemma kind_ren_term xi A : kind A -> ren_term xi A = A.
Proof.
  move=> /kind_allfv_termI H.
  by apply: ren_term_allfv_id.
Qed.

Lemma kind_subst_term sigma A : kind A -> subst_term sigma A = A.
Proof.
  move=> /kind_allfv_termI H.
  by apply: subst_term_allfv_var.
Qed.

Lemma kind_and_pre_typeE {A} : kind A -> pre_type A -> False.
Proof. elim: A => //=. by tauto. Qed.

Lemma pre_type_ren_termI {xi A} : pre_type A -> pre_type (ren_term xi A).
Proof.
  elim: A xi.
  - done.
  - done.
  - move=> ? IHA ? IHB ? /= [/IHA ? /IHB ?]. by constructor.
  - move=> ? IHA ? IHB ? /= [? /IHB ?].
    constructor; last done.
    by rewrite kind_ren_term.
  - move=> ? IHA ? IHB xi /= [|].
    + move=> [? /IHB ?]. left.
      by constructor; [rewrite kind_ren_term |].
    + move=> [/IHA ?] [/IHB ?] [Q' ?]. right.
      constructor; [done | constructor; [done |]].
      subst. exists (ren_term xi Q'). by rewrite ?term_norm.
Qed.

Lemma pre_type_subst_termI {sigma A} : (forall x, pre_type (sigma x)) ->
  pre_type A -> pre_type (subst_term sigma A).
Proof.
  elim: A sigma.
  - move=> > + _. by apply.
  - done.
  - move=> A IHA B IHB ? ? /= [? ?].
    by constructor; [apply: IHA | apply: IHB].
  - move=> A IHA B IHB ? ? /= [? ?].
    constructor; first by rewrite kind_subst_term.
    apply: IHB; last done.
    by move=> [|x]; [| apply: pre_type_ren_termI].
  - move=> ? IHA ? IHB sigma ? /= [|].
    + move=> [? ?]. left.
      constructor; first by rewrite kind_subst_term.
      apply: IHB; last done.
      by move=> [|x]; [| apply: pre_type_ren_termI].
    + move=> [/IHA {}IHA] [/IHB {}IHB] [Q' ?]. right.
      constructor; first by apply: IHA.
      constructor. apply: IHB.
      { by move=> [|x]; [| apply: pre_type_ren_termI]. }
      subst. exists (subst_term sigma Q').
      by rewrite ?term_norm.
Qed.

Lemma sanity {Gamma P Q} : type_assignment Gamma P Q ->
  (kind P /\ Q = const 1) \/
  (pre_type P /\ kind Q) \/
  (pre_term P /\ pre_type Q).
Proof.
  elim.
  - move=> _. by left.
  - move=> > /= _; by tauto.
  - move=> > /= _ [|[|[+ []]]]; first by case.
    + move=> [?] [? ?] _ [|[|]].
      * move=> [? ?]. by subst.
      * move=> [? ?]. rewrite kind_subst_term; by tauto.
      * by move=> [_ /kind_and_pre_typeE].
    + move=> ? [? ?] _ [|[|]].
      * move=> [? ?]. by subst.
      * move=> [? ?]. right. right.
        constructor; first by tauto.
        by apply: pre_type_subst_termI; [case |].
      * by move=> [_ /kind_and_pre_typeE].
    + move=> ? [?] [? [Q' ?]] _ [|[|]].
      * move=> [? ?]. by subst.
      * by move=> [_ /kind_and_pre_typeE].
      * move=> [? ?]. right. right.
        subst. rewrite term_norm subst_term_var.
        constructor; first by tauto.
        have <-: ren_term (scons 0 id) (ren_term shift Q') = Q'
        by rewrite term_norm ren_term_id.
        by apply: pre_type_ren_termI.
  - move=> ? [|s1] [|s2] > /= H _.
    + move=> [[]|[|[]]]; [done | | done].
      move=> [? _] _ [|]; first by case.
      move=> [|]; last by case.
      move=> [? _]. right. left.
      constructor; last done.
      right. ??? TODO


Lemma sanity_kind {Gamma P}: type_assignment Gamma P (const 1) ->
  kind P.
Proof.
  move HA: (const 1) => A H. elim: H HA.
  - done.
  - move=> > + ? ? ?. subst. by move=> /sanity_box.
  - admit. (* needs elim for "type_assignment Gamma0 P0 (Pi A0 (const 1))" *)
  - move=> > + _ + _ + [?]. subst.
    case; [done| case; [done| case; [|done]]].
    move=> [<-] IH1 IH2.
    by constructor; [apply: IH1 | apply: IH2].
  - done.
  - move=> > _ _ + _ _ ?. by subst => /sanity_box.
