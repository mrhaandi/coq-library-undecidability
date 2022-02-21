From Undecidability Require L.L.
Require Import List.
Import L (var, app, lam).

(*
(* S/K_term t1 .. tn = S/K t1 .. tn *)
Inductive term : Type :=
| S_term : list term -> term
| K_term : list term -> term.
*)

(* terms extended with constants K, S *)
Inductive eterm : Type :=
  | eK : eterm
  | eS : eterm
  | evar (n : nat) : eterm
  | eapp (s : eterm) (t : eterm) : eterm
  | elam (s : eterm).

(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

Fixpoint eren (xi : nat -> nat) (t : eterm) : eterm  :=
  match t with
  | evar x => evar (xi x)
  | eapp s t => eapp (eren xi s) (eren xi t)
  | elam t => elam (eren (scons 0 (funcomp S xi)) t)
  | _ => t
  end.

Fixpoint esubst (sigma : nat -> eterm) (t : eterm) : eterm  :=
  match t with
  | evar x => sigma x
  | eapp s t => eapp (esubst sigma s) (esubst sigma t)
  | elam t => elam (esubst (scons (evar 0) (funcomp (eren S) sigma)) t)
  | _ => t
  end.

Definition closed s := forall sigma, esubst sigma s = s.

(* variable capturing substitution : bad idea *)
Fixpoint esubst' (s : eterm) (k : nat) (u : eterm) :=
  match s with
    | evar n => if Nat.eqb n k then u else evar n
    | eapp s t => eapp (esubst' s k u) (esubst' t k u)
    | elam s => elam (esubst' s (S k) u)
    | _ => s
  end.

Definition closed' s := forall n t, esubst' s n t = s.

Inductive evalue : eterm -> Prop :=
  | evalue_K0 : evalue eK
  | evalue_K1 t : evalue (eapp eK t)
  | evalue_S0 : evalue eS
  | evalue_S1 t : evalue (eapp eS t)
  | evalue_S2 s t : evalue (eapp (eapp eS s) t)
  | evalue_lam t : evalue (elam t).

(* capturing definitions *)

Inductive estep : eterm -> eterm -> Prop :=
  | estepK  s t       : evalue t -> estep (eapp (eapp eK s) t) s
  | estepS  s t u     : evalue u -> estep (eapp (eapp (eapp eS s) t) u) (eapp (eapp s u) (eapp t u))
  | estepApp  s t     : evalue t -> estep (eapp (elam s) t) (esubst' s 0 t)
  | estepAppR s t  t' : estep t t' -> estep (eapp s t) (eapp s t')
  | estepAppL s s' t  : estep s s' -> estep (eapp s t) (eapp s' t).

Fixpoint contains_elam (t : eterm) : bool :=
  match t with
  | eapp s t => contains_elam s || contains_elam t
  | elam _ => true
  | _ => false
  end.

Fixpoint contains_evar n (t : eterm) : bool :=
  match t with
  | evar m => if Nat.eqb n m then true else false
  | eapp s t => contains_evar n s || contains_evar n t
  | elam t => contains_evar (S n) t
  | _ => false
  end.

(*
Lemma has_evar_0 t : {s | t = eren S s} + { contains_evar 0 t = true }.
Proof.
Admitted.
*)

Fixpoint SK_step (t : eterm) : eterm :=
  match t with
    | eapp s t => if contains_elam s then eapp (SK_step s) t else eapp s (SK_step t)
    | elam s =>
        if contains_evar 0 s then
          match s with
          | eapp t1 t2 => eapp (eapp eS (elam t1)) (elam t2)
          | elam _ => elam (SK_step s)
          | _ => eapp (eapp eS eK) eK
          end else eapp eK (eren pred s)
    | _ => t
  end.

From Undecidability Require L.Util.L_facts.
Require Import ssreflect ssrbool ssrfun.
From Undecidability Require L.Prelim.ARS.

Lemma SK_step_not_contains_elam {t} : contains_elam t = false ->
  SK_step t = t.
Proof.
Admitted.

Lemma SK_evalue t : evalue t -> evalue (SK_step t).
Proof. Admitted.

(*
Lemma esubst_not_contains_evar {s n t} : 
  contains_evar n s = false ->
  esubst s n t = s.
Proof.
  elim: s n.
Admitted.
*)
Lemma closed_eappE s t : closed (eapp s t) -> closed s /\ closed t.
Proof.
Admitted.

Lemma closed_contains_evar {n t} : closed t -> contains_evar n t = false.
Proof.
Admitted.

Lemma SK_step_elam_false t : contains_evar 0 t = false -> SK_step (elam t) = eapp eK (eren Nat.pred t).
Proof. by move=> /= ->. Qed.

Lemma SK_step_elam_true t : contains_evar 0 t = true -> SK_step (elam t) = 
  match t with
  | eapp t1 t2 => eapp (eapp eS (elam t1)) (elam t2)
  | elam _ => elam (SK_step t)
  | _ => eapp (eapp eS eK) eK
  end.
Proof. by move=> /= ->. Qed.

Lemma esubst'elam s t n : esubst' (elam s) n t = elam (esubst' s (S n) t).
Proof. done. Qed.

Lemma esubst'eapp s1 s2 t n : esubst' (eapp s1 s2) n t = eapp (esubst' s1 n t) (esubst' s2 n t).
Proof. done. Qed.

Lemma esubst'_SK_step n s t : closed t -> esubst' (SK_step (elam s)) n t = SK_step (esubst' (elam s) n t).
Proof.
  elim: s n.
  - done.
  - done.
  - move=> [|m] n Ht /=; first done.
    case Emn: (Nat.eqb m n) => [|] /=.
    + rewrite (closed_contains_evar Ht).
     admit. (* easy *)
    + done.
  - move=> s1 IH1 s2 IH2 n Ht.
    case E: (contains_evar 0 (eapp s1 s2)) => [|].
    * move: (E) => /SK_step_elam_true ->.
     rewrite esubst'elam.
     rewrite SK_step_elam_true. admit. (* doable *)
      rewrite  !esubst'eapp.
      done.
    * move: (E) => /SK_step_elam_false ->.
    rewrite esubst'elam.
    rewrite SK_step_elam_false. admit. (* doable *)
    simpl.
    admit. (* doable *)
  - move=> s IH n Ht.
    case Es: (contains_evar 0 (elam s)) => [|].
    + move: (Es) => /SK_step_elam_true ->.
      rewrite !esubst'elam IH. done.
      rewrite SK_step_elam_true. admit. (* doable *)
      done.
    + move: (Es) => /SK_step_elam_false ->.
      rewrite !esubst'elam.
      rewrite SK_step_elam_false. admit. (* doable *)
      cbn. congr eapp.
      congr elam.
      admit. (* doable *)
Admitted.


(* actually plus instead of star *)
(* this can be shown *)
Lemma main s t : estep s t -> closed s ->
  exists n, ARS.star estep (SK_step s) (Nat.iter n SK_step t).
Proof.
  elim.
  - move=> {}s {}t /=. move E: (contains_elam s) => [].
    + move=> /estepK H ?. exists 1. by apply: ARS.starC; [|apply: ARS.starR].
    + move=> /SK_evalue /estepK H ?. exists 1 => /=.
      move: E => /SK_step_not_contains_elam ->.
      by apply: ARS.starC; [|apply: ARS.starR].
  - admit.
  - move=> {}s {}t Ht /=.
    case Es: (contains_evar 0 s) => [|]; first last.
    { move=> ?. exists 0 => /=.
      apply: ARS.starC.
      apply: estepK. done.
      admit. (* actually doable because s' is closed and renamings do nothing
      apply: ARS.starR.*) }
    case: s Es.
    + done.
    + done.
    + move=> [|n] ??; last done.
      exists 0 => /=.
      apply: ARS.starC.
      apply: estepS. done.
      apply: ARS.starC.
      apply: estepK. apply: evalue_K1.
      apply: ARS.starR.
    + move=> {}s u ?? /=. exists 0 => /=.
      apply: ARS.starC.
        apply: estepS. done.
        apply: ARS.starC.
        apply: estepAppR.
        apply: estepApp. done.
        apply: ARS.starC.
        apply: estepAppL.
        apply: estepApp. done.
        apply: ARS.starR.
    + move=> s Es ?.
      exists 1.
      apply: ARS.starC.
      apply: estepApp. done.
      rewrite esubst'_SK_step. admit. (* easy *)
      apply: ARS.starR.
  - move=> {}s {}t u Htu IH /closed_eappE [? /IH] /=.
    move=> [n Hn].
    move E: (contains_elam s) => [].
    + exists 1 => /=.
      rewrite E.
      apply: ARS.starC.
      apply: estepAppR. eassumption.
      apply: ARS.starR.
    + exists n. admit. (* easy *)
  - move=> {}s {}t u Hst IH /closed_eappE [/IH [n Hn] ?].
    admit. (* difficult, doable *)
Admitted.



(* non-capturing definitions 
!!!!!!!!!!!!!!!!!!!!!!!!

*)

Inductive estep : eterm -> eterm -> Prop :=
  | estepK  s t       : evalue t -> estep (eapp (eapp eK s) t) s
  | estepS  s t u     : evalue u -> estep (eapp (eapp (eapp eS s) t) u) (eapp (eapp s u) (eapp t u))
  | estepApp  s t     : evalue t -> estep (eapp (elam s) t) (esubst (scons t evar) s)
  | estepAppR s t  t' : estep t t' -> estep (eapp s t) (eapp s t')
  | estepAppL s s' t  : estep s s' -> estep (eapp s t) (eapp s' t).

Fixpoint contains_elam (t : eterm) : bool :=
  match t with
  | eapp s t => contains_elam s || contains_elam t
  | elam _ => true
  | _ => false
  end.

Fixpoint contains_evar n (t : eterm) : bool :=
  match t with
  | evar m => if Nat.eqb n m then true else false
  | eapp s t => contains_evar n s || contains_evar n t
  | elam t => contains_evar (S n) t
  | _ => false
  end.

Lemma has_evar_0 t : {s | t = eren S s} + { contains_evar 0 t = true }.
Proof.
Admitted.

(*
(* this is not the full translation because of (lam (lam t)) cases,
  but can be iterated *)
Fixpoint SK_step (t : eterm) : eterm :=
  match t with
    | eapp s t => if contains_elam s then eapp (SK_step s) t else eapp s (SK_step t)
    | elam s => 
        match has_evar_0 s with
        | @inleft _ _ (exist _ s' _) => eapp eK s'
        | @inright _ _ _ =>
            match s with
            | eapp t1 t2 => eapp (eapp eS (elam t1)) (elam t2)
            | elam _ => elam (SK_step s)
            | _ => eapp (eapp eS eK) eK
            end
        end
    | _ => t
  end.
*)

Fixpoint SK_step (t : eterm) : eterm :=
  match t with
    | eapp s t => if contains_elam s then eapp (SK_step s) t else eapp s (SK_step t)
    | elam s => 
        match has_evar_0 s with
        | @inleft _ _ (exist _ s' _) => eapp eK s'
        | @inright _ _ _ =>
            match s with
            | eapp t1 t2 => eapp (eapp eS (elam t1)) (elam t2)
            | elam _ => elam (SK_step s)
            | _ => eapp (eapp eS eK) eK
            end
        end
    | _ => t
  end.

From Undecidability Require L.Util.L_facts.
Require Import ssreflect ssrbool ssrfun.
From Undecidability Require L.Prelim.ARS.

Lemma SK_step_not_contains_elam {t} : contains_elam t = false ->
  SK_step t = t.
Proof.
Admitted.

Lemma SK_evalue t : evalue t -> evalue (SK_step t).
Proof. Admitted.

(*
Lemma esubst_not_contains_evar {s n t} : 
  contains_evar n s = false ->
  esubst s n t = s.
Proof.
  elim: s n.
Admitted.
*)
Lemma closed_eappE s t : closed (eapp s t) -> closed s /\ closed t.
Proof.
Admitted.

(* actually plus instead of star *)
Lemma main s t : estep s t -> closed s ->
  exists n, ARS.star estep (SK_step s) (Nat.iter n SK_step t).
Proof.
  elim.
  - move=> {}s {}t /=. move E: (contains_elam s) => [].
    + move=> /estepK H ?. exists 1. by apply: ARS.starC; [|apply: ARS.starR].
    + move=> /SK_evalue /estepK H ?. exists 1 => /=.
      move: E => /SK_step_not_contains_elam ->.
      by apply: ARS.starC; [|apply: ARS.starR].
  - admit.
  - move=> {}s {}t Ht /=.
    case: (has_evar_0 s) => [[s' ->]|Es].
    { move=> ?. exists 0 => /=.
      apply: ARS.starC.
      apply: estepK. done.
      admit. (* easy but here actually is an index shift! 
      rewrite (esubst_not_contains_evar Es).
      apply: ARS.starR.*) }
    case: s Es.
    + done.
    + done.
    + move=> [|n] ??; last done.
      exists 0 => /=.
      apply: ARS.starC.
      apply: estepS. done.
      apply: ARS.starC.
      apply: estepK. apply: evalue_K1.
      apply: ARS.starR.
    + move=> {}s u ?? /=. exists 0 => /=.
      apply: ARS.starC.
        apply: estepS. done.
        apply: ARS.starC.
        apply: estepAppR.
        apply: estepApp. done.
        apply: ARS.starC.
        apply: estepAppL.
        apply: estepApp. done.
        apply: ARS.starR.
    + move=> s /= Es ?.
      case: (has_evar_0 s) => [[s' ->]|?].
      * exists 1 => /=. admit. (* possibly *)
      * admit. (* ? *)
  - move=> {}s {}t u Htu IH /closed_eappE [? /IH] /=.
    move=> [n Hn].
    move E: (contains_elam s) => [].
    + exists 1 => /=.
      rewrite E.
      apply: ARS.starC.
      apply: estepAppR. eassumption.
      apply: ARS.starR.
    + exists n. admit. (* easy *)
  - move=> {}s {}t u Hst IH /closed_eappE [/IH [n Hn] ?].

    admit. (* difficult, doable *)
Admitted.




Lemma main s t : estep s t ->
  ARS.star estep (SK_step s) (SK_step t).
Proof.
  elim.
  - move=> {}s {}t /=. move E: (contains_elam s) => [].
    + move=> /estepK H. by apply: ARS.starC; [|apply: ARS.starR].
    + move: E => /SK_step_not_contains_elam ->.
      move=> /SK_evalue /estepK H. by apply: ARS.starC; [|apply: ARS.starR].
  - admit.
  - case.
    + admit.
    + admit.
    + admit.
    + move=> {}s {}t u Hu /=. move E: (contains_elam _) => [].
      * apply: ARS.starC.
        apply: estepS. done.
        apply: ARS.starC.
        apply: estepAppR.
        apply: estepApp. done.
        apply: estepAppL.
        apply: estepApp. done.
      
      by apply: SK_evalue.
      * 

    cbn. apply: H.




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
