From Undecidability Require L.L.
Require Import List.
Import L (var, app, lam).


(* S/K_term t1 .. tn = S/K t1 .. tn *)
Inductive term : Type :=
| S_term : list term -> term
| K_term : list term -> term.

(* \xy.x *)
#[local] Notation L_K :=
  (lam (lam (var 1))).
(* \xyz.(x z) (y z) *)
#[local] Notation L_S :=
  (lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))).

(*
Inductive translation : term -> term -> Prop :=
  (* \x.t where t does not contain x but may other vars? *)
  | translation_K : not_in 0 t -> translation (lower t) t' -> translation (lam t) (app L_K t')
  | translation_I : translation t (app t1 t2) -> in 0 t -> translation (lam t) (app (app S_K (lam t'1) t'2)
*)

(* this is not the full translation because of (lam (lam t)) cases,
  but can be iterated *)
  (*  k is level of K, S k is level of S, after translation need to apply/subst k,S k by K,S *)
  Fixpoint SK_step (k : nat) (t : L.term) : L.term :=
  match t with
  | var n => var n
  | app t1 t2 => app (SK_step k t1) (SK_step k t2)
  | lam (var 0) => app (app (var (S k)) (var k)) (var k)
  | lam (var (S n)) => app (var k) (var n)
  | lam (app t1 t2) => app (app (var (S k)) (lam t1)) (lam t2)
  | lam t => lam (SK_step (S k) t)
  end.

  (*
Arguments SK_step : simpl never.
*)
From Undecidability Require L.Util.L_facts.
Require Import ssreflect ssrbool ssrfun.
From Undecidability Require L.Prelim.ARS.

(*
Lemma SK_step_var n : SK_step (var n) = var n.
Proof. done. Qed.

Lemma SK_step_app s t : SK_step (app s t) = app (SK_step s) (SK_step t).
Proof. done. Qed.

Lemma SK_step_lam_app s t : SK_step (lam (app s t)) = app (app L_S (lam s)) (lam t).
Proof. done. Qed.

Lemma SK_step_L_K : SK_step L_K = L_K.
Proof. done. Qed.

Lemma SK_step_L_S : SK_step L_S = L_S.
Proof. done. Qed.

Lemma SK_step_lam_L_K : SK_step (lam L_K) = app L_K L_K.
Proof. done. Qed.

Lemma SK_step_lam_L_S : SK_step (lam L_S) = app L_K L_S.
Proof. done. Qed.

Definition SK_step_simpl := (SK_step_var, SK_step_app, SK_step_lam_app,
  SK_step_L_K, SK_step_L_S, SK_step_lam_L_K, SK_step_lam_L_S).

Lemma SK_step_lam_lam s : 
  ((lam (lam s) = L_K \/ lam (lam s) = L_S \/ lam (lam s) = lam L_K \/ lam (lam s) = lam L_S)) \/
  (SK_step (lam (lam s)) = lam (SK_step (lam s))).
Proof.
  move: s => []; try by right.
  - move=> [|[|?]]; try by right.
    tauto.
  -  (case; try by right).
    + do ? (case; try by right).
      tauto.
    + do ? (case; try by right).
      tauto.
    + case.
      * right. reflexivity.
      * admit.
      * right. simple apply erefl. reflexivity.
    tauto.
      case; try by right.
      right. rewrite /SK_step. done.
    tauto.
Qed.
*)
(* if this can be done, then iteratevely finished! *)
Lemma main s t : L_facts.step s t -> L_facts.closed s ->
  ARS.star L_facts.step 
    (L.subst (L.subst (SK_step 0 s) 0 L_K) 1 L_S)
    (L.subst (L.subst (SK_step 0 t) 0 L_K) 1 L_S)
  \/
  ARS.star L_facts.step 
    (L.subst (L.subst (SK_step 0 s) 0 L_K) 1 L_S)
    t
  .
Proof.
  elim.
  { move=> {}s {}t /=.
    move: s => [[|]||] /=.
    - admit.
    - admit. (* contradiction *)
    - move=> s1 s2.
      move: t => [[|]||] /=.
      + admit. (* maybe doable, maybe needs bound instead of closed *)
      + admit. (* contradiction t not closed *) 
      + 
      
      move=> [|[|]] /=.
        * admit.
        * admit.
        *  
  (*
   move=> {}s {}t.
    move: s => [].
    - move=> [|n] /=.
      + move: t => [].
        * move=> [|m]. admit. admit.
        * move=> s t. rewrite !SK_step_simpl. admit.
        * move=> s. rewrite !SK_step_simpl. have [|] := SK_step_lam_lam s.
          { move=> [->|->]; admit. } (* easy *)
          move=> ->. admit. (* easy *)
      + admit. (* contradiction to closedness *)
    - move=> s1 s2. rewrite /= !SK_step_simpl.  admit.
    - 
    }*)
  { move=> > ? IH /L_facts.closed_app [? ?] /=. 
    apply: L_facts.star_trans_r. by apply: IH. }
  { move=> > ? IH /L_facts.closed_app [? ?] /=. 
    apply: L_facts.star_trans_l. by apply: IH. }

Print translation.

  
(*
(* this is not the full translation because of (lam (lam t)) cases,
   but can be iterated *)
   (* i is level of K, 1+i is level of S, after translation need to apply/subst i,1+i by K,S *)
Fixpoint SK_step (i : nat) (t : L.term) : L.term :=
  match t with
  | var n => var n
  | app t1 t2 => app (SK_step t1) (SK_step t2)
  | L_K => L_K
  | L_S => L_S
  | lam (var 0) => app (app L_S L_K) L_K
  | lam (var (S n)) => app L_K (var n)
  | lam (app t1 t2) => app (app L_S (lam t1)) (lam t2)
  | lam L_K => app L_K L_K
  | lam L_S => app L_K L_S
  | lam t => lam (SK_step t)
  end.

Arguments SK_step : simpl never.

From Undecidability Require L.Util.L_facts.
Require Import ssreflect ssrbool ssrfun.
From Undecidability Require L.Prelim.ARS.

Lemma SK_step_var n : SK_step (var n) = var n.
Proof. done. Qed.

Lemma SK_step_app s t : SK_step (app s t) = app (SK_step s) (SK_step t).
Proof. done. Qed.

Lemma SK_step_lam_app s t : SK_step (lam (app s t)) = app (app L_S (lam s)) (lam t).
Proof. done. Qed.

Lemma SK_step_L_K : SK_step L_K = L_K.
Proof. done. Qed.

Lemma SK_step_L_S : SK_step L_S = L_S.
Proof. done. Qed.

Lemma SK_step_lam_L_K : SK_step (lam L_K) = app L_K L_K.
Proof. done. Qed.

Lemma SK_step_lam_L_S : SK_step (lam L_S) = app L_K L_S.
Proof. done. Qed.

Definition SK_step_simpl := (SK_step_var, SK_step_app, SK_step_lam_app,
  SK_step_L_K, SK_step_L_S, SK_step_lam_L_K, SK_step_lam_L_S).

Lemma SK_step_lam_lam s : 
  ((lam (lam s) = L_K \/ lam (lam s) = L_S \/ lam (lam s) = lam L_K \/ lam (lam s) = lam L_S)) \/
  (SK_step (lam (lam s)) = lam (SK_step (lam s))).
Proof.
  move: s => []; try by right.
  - move=> [|[|?]]; try by right.
    tauto.
  -  (case; try by right).
    + do ? (case; try by right).
      tauto.
    + do ? (case; try by right).
      tauto.
    + case.
      * right. reflexivity.
      * admit.
      * right. simple apply erefl. reflexivity.
    tauto.
      case; try by right.
      right. rewrite /SK_step. done.
    tauto.
Qed.

(* if this can be done, then iteratevely finished! *)
Lemma main s t : L_facts.step s t -> L_facts.closed s -> ARS.star L_facts.step (SK_step s) (SK_step t).
Proof.
  elim.
  { move=> {}s {}t.
    move: s => [].
    - move=> [|n] /=.
      + move: t => [].
        * move=> [|m]. admit. admit.
        * move=> s t. rewrite !SK_step_simpl. admit.
        * move=> s. rewrite !SK_step_simpl. have [|] := SK_step_lam_lam s.
          { move=> [->|->]; admit. } (* easy *)
          move=> ->. admit. (* easy *)
      + admit. (* contradiction to closedness *)
    - move=> s1 s2. rewrite /= !SK_step_simpl.  admit.
    - 
    }
  { move=> *. by apply: L_facts.star_trans_r. }
  { move=> *. by apply: L_facts.star_trans_l. }
  move=> [] /=.
    - move=> [|?]. cbn. } 

Print translation.
*)
