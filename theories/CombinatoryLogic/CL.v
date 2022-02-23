From Undecidability Require L.L.
Require Import List Lia.
Import L (var, app, lam).

(* back to exponential construction now with eval *)

Inductive eterm : Type :=
  | eK : eterm
  | eS : eterm
  | evar (n : nat) : eterm
  | eapp (s : eterm) (t : eterm) : eterm.

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

Fixpoint eren (xi : nat -> nat) (t : eterm) : eterm  :=
  match t with
  | evar x => evar (xi x)
  | eapp s t => eapp (eren xi s) (eren xi t)
  | _ => t
  end.

(* variable capturing substitution : bad idea *)
Fixpoint esubst' (s : eterm) (k : nat) (u : eterm) :=
  match s with
    | evar n => if Nat.eqb n k then u else evar n
    | eapp s t => eapp (esubst' s k u) (esubst' t k u)
    | _ => s
  end.

Definition closed' s := forall n t, esubst' s n t = s.

Inductive evalue : eterm -> Prop :=
  | evalue_K0 : evalue eK
  | evalue_K1 t : evalue (eapp eK t)
  | evalue_S0 : evalue eS
  | evalue_S1 t : evalue (eapp eS t)
  | evalue_S2 s t : evalue (eapp (eapp eS s) t).

(* capturing definitions *)

Inductive estep : eterm -> eterm -> Prop :=
  | estepK  s t       : evalue t -> estep (eapp (eapp eK s) t) s
  | estepS  s t u     : evalue u -> estep (eapp (eapp (eapp eS s) t) u) (eapp (eapp s u) (eapp t u))
  (* wrong because reduces s in (K s) *)
  | estepAppR s t  t' : estep t t' -> estep (eapp s t) (eapp s t')
  | estepAppL s s' t  : estep s s' -> estep (eapp s t) (eapp s' t).
  
Fixpoint contains_evar n (t : eterm) : bool :=
  match t with
  | evar m => if Nat.eqb n m then true else false
  | eapp s t => contains_evar n s || contains_evar n t
  | _ => false
  end.
(*
Fixpoint contains_var n (t : L.term) : bool :=
  match t with
  | var m => if Nat.eqb n m then true else false
  | app s t => contains_var n s || contains_var n t
  | lam t => contains_var (S n) t
  end.
*)
(* exponential abstraction *)
Fixpoint abstraction (s : eterm) : eterm :=
    match s with
    | evar 0 => eapp (eapp eS eK) eK
    | evar (S n) => eapp eK (evar n)
    | eapp s t => eapp (eapp eS (abstraction s)) (abstraction t)
    | _ => eapp eK s
    end.

Fixpoint translate (s : L.term) : eterm :=
  match s with
  | var n => evar n
  | app s t => eapp (translate s) (translate t)
  | lam t => abstraction (translate t)
  end.

  Require Import Relations PeanoNat.
  #[local] Arguments clos_trans {A}.
  #[local] Arguments clos_refl_trans {A}.
  
  From Undecidability Require L.Util.L_facts.
Require Import ssreflect ssrbool ssrfun.
Unset Implicit Arguments.

Lemma evalue_abstraction t : evalue (abstraction t).
Proof.
  elim: t; [| |case|] => /=.
  all: by auto using evalue.
Qed.

(*


Lemma closed'_eappE s t : closed' (eapp s t) -> closed' s /\ closed' t.
Proof. move=> H. split => n u; by have [] := H n u. Qed.

Lemma closed'_eappI s t : closed' s -> closed' t -> closed' (eapp s t).
Proof. move=> Hs Ht n u /=. by rewrite (Hs n u) (Ht n u). Qed.

Lemma many_estepAppL s t u : clos_trans estep s t -> clos_trans estep (eapp s u) (eapp t u).
Proof.
  elim.
  - move=> > /estepAppL ?. by apply: t_step.
  - move=> > ????. by apply: t_trans; eassumption.
Qed.

Lemma many_estepAppR s t u : clos_trans estep s t -> clos_trans estep (eapp u s) (eapp u t).
Proof.
  elim.
  - move=> > /estepAppR ?. by apply: t_step.
  - move=> > ????. by apply: t_trans; eassumption.
Qed.

Lemma closed'_evarE n : closed' (evar n) -> False.
Proof. move=> /(_ n eK) /=. by rewrite Nat.eqb_refl. Qed.

Lemma closed'_erenE xi t : closed' (eren xi t) -> closed' t.
Proof.
  elim: t; [done|done| |].
  - by move=> > /closed'_evarE.
  - move=> ? IH1 ? IH2.
    move=> /closed'_eappE [/IH1 + /IH2].
    by apply: closed'_eappI.
Qed.

Lemma closed'_eren xi {t} : closed' t -> eren xi t = t.
Proof.
  elim: t; [done|done| |].
  - by move=> > /closed'_evarE.
  - move=> /= ? IH1 ? IH2.
    by move=> /closed'_eappE [/IH1 -> /IH2 ->].
Qed.

Lemma estep_abstraction s t :
  evalue t -> closed' (abstraction s) -> clos_trans estep (eapp (abstraction s) t) (esubst' s 0 t).
Proof.
  move=> Ht. elim: s.
  - move=> ?. apply: t_step. by apply: estepK.
  - move=> ?. apply: t_step. by apply: estepK.
  - move=> [|n] /= H.
    + apply: t_trans. { apply: t_step. by apply: estepS. }
      apply: t_step. apply: estepK. by apply: evalue_K1.
    + by move: H => /closed'_eappE [_] /closed'_evarE.
  - move=> s1 IH1 s2 IH2.
    case Hs1s2: (contains_evar 0 (eapp s1 s2)).
    + move: Hs1s2 => /= ->.
      move=> /closed'_eappE [/closed'_eappE] [_].
      move=> /IH1 {}IH1 /IH2 {}IH2.
      apply: t_trans. { apply: t_step. by apply: estepS. }
      apply: t_trans. { apply: many_estepAppL. by eassumption. }
      by apply: many_estepAppR.
    + move: (Hs1s2) => /= ->.
      move=> /closed'_eappE [_] /closed'_eappE [] /closed'_erenE Hs1 /closed'_erenE Hs2.
      move: Hs1 Hs2 (Hs1) (Hs2) => -> -> /closed'_eren -> /closed'_eren ->.
      apply: t_step. by apply: estepK.
Qed.

Lemma closed'_not_contains_evar t n : closed' t -> contains_evar n t = false.
Proof.
  elim: t; [done|done| |].
  - by move=> > /closed'_evarE.
  - by move=> s IH1 t IH2 /closed'_eappE /= [/IH1 -> /IH2 ->].
Qed.

Lemma esubst'_eren_pred s n t : closed' t -> contains_evar 0 s = false ->
  esubst' (eren Nat.pred s) n t = eren Nat.pred (esubst' s (S n) t).
Proof.
  move=> Ht. elim: s; [done|done| |].
  - move=> [|m]; first done.
    move=> _ /=. case: (Nat.eqb m n); last done.
    by rewrite (closed'_eren Nat.pred Ht).
  - move=> s1 IH1 s2 IH2 /=.
    by move=> /norP [/negPf /IH1 -> /negPf /IH2 ->].
Qed.

Lemma contains_evar_0_esubst' s n t : closed' t ->
  contains_evar 0 (esubst' s (S n) t) = contains_evar 0 s.
Proof.
  move=> Ht. elim: s; [done|done| |].
  - move=> [|m] /=; first done.
    case: (Nat.eqb m n); last done.
    by apply: closed'_not_contains_evar.
  - by move=> /= s1 -> s2 ->.
Qed.

Lemma esubst'_abstraction s n t :
  closed' t ->
  esubst' (abstraction s) n t = abstraction (esubst' s (S n) t).
Proof.
  move=> Ht. elim: s n; [done|done| |].
  - move=> [|m] n /=; first done.
    case E: (Nat.eqb m n); last done.
    case: t Ht => > /= ; [done|done| |].
    + by move=> /closed'_evarE.
    + move=> /closed'_eappE [H1 H2].
      move: (H1) (H2) => /closed'_eren -> /closed'_eren ->.
      by move: H1 H2 => /closed'_not_contains_evar -> /closed'_not_contains_evar ->.
  - move=> s1 IH1 s2 IH2 n.
    case Hs1s2: (contains_evar 0 (eapp s1 s2)).
    + rewrite /= !contains_evar_0_esubst' //.
      move: Hs1s2 => /= ->. by rewrite /= IH1 IH2.
    + rewrite /= !contains_evar_0_esubst' //.
      move: (Hs1s2) => /= ->.
      move: Hs1s2 => /= /norP [/negPf ? /negPf ?].
      by rewrite !esubst'_eren_pred.
Qed.

Lemma not_contains_evar_closed' t : (forall n, contains_evar n t = false) -> closed' t.
Proof.
  elim: t; [done|done| |].
  - move=> m /(_ m) /=. by rewrite Nat.eqb_refl.
  - move=> /= s IH1 t IH2 H. apply: closed'_eappI.
    + apply: IH1 => n. by have /norP [/negPf ->] := H n.
    + apply: IH2 => n. by have /norP [_ /negPf ->] := H n.
Qed.

Lemma contains_evar_pred n t : contains_evar 0 t = false ->
  contains_evar n (eren Nat.pred t) = contains_evar (S n) t.
Proof.
  elim: t; [done|done|by case|].
  by move=> s IH1 t IH2 /= /norP [/negPf /IH1 -> /negPf /IH2 ->].
Qed.

Lemma contains_evar_abstraction n s : contains_evar n (abstraction s) = contains_evar (S n) s.
Proof.
  elim: s; [done|done|by case|].
  move=> s IH1 t IH2.
  case H: (contains_evar 0 (eapp s t)).
  - move: H => /= -> /=. by rewrite IH1 IH2.
  - move: (H) => /= -> /=.
    by move: H => /= /norP [/negPf /contains_evar_pred -> /negPf /contains_evar_pred ->].
Qed.

Lemma closed'_translate s : L_facts.closed s -> closed' (translate s).
Proof.
  move=> /L_facts.closed_dcl Hs.
  apply: not_contains_evar_closed' => n.
  have : 0 <= n by lia.
  move: (0) Hs n => ?. elim.
  - move=> m x ? n /= ?.
    by have /Nat.eqb_neq -> : n <> x by lia.
  - move=> > ? IH1 ? IH2 ?? /=.
    rewrite IH1; [done|]. by rewrite IH2.
  - move=> > ? IH n ? /=.
    rewrite contains_evar_abstraction. apply: IH. lia.
Qed.

Lemma esubst'_translate s n t : L_facts.closed t ->
  esubst' (translate s) n (translate t) = translate (L.subst s n t).
Proof.
  move=> Ht. elim: s n => /=.
  - move=> m n. by case: (Nat.eqb m n).
  - move=> s1 IH1 s2 IH2 n. by rewrite IH1 IH2.
  - move=> s IH n. rewrite esubst'_abstraction. { by apply: closed'_translate. }
    by rewrite IH.
Qed.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

(* actually plus instead of star *)
(* this can be shown *)
Lemma main s t : L_facts.step s t -> L_facts.closed s ->
  clos_trans estep (translate s) (translate t).
Proof.
  elim.
  - move=> {}s {}t /= /L_facts.closed_app [Hs Ht].
    have /(estep_abstraction (translate s)) := evalue_abstraction (translate t).
    apply: unnest. { by apply: (closed'_translate (lam s)). }
    congr clos_trans.
    by apply: (esubst'_translate _ _ (lam t)).
  - move=> > ? IH /L_facts.closed_app [_ /IH] /=.
    by apply: many_estepAppR.
  - move=> > ? IH /L_facts.closed_app [/IH + _] /=.
    by apply: many_estepAppL.
Qed.

Lemma t_rt x y : clos_trans estep x y -> clos_refl_trans estep x y.
Proof. Admitted.

Arguments rt_trans {A} R.

Lemma main' s t : L.eval s t -> L_facts.closed s ->
  clos_refl_trans estep (translate s) (translate t).
Proof.
  move=> /L_facts.eval_iff []. elim.
  - move=> ? [] s' -> ?. by apply: rt_refl.
  - move=> > Hxy. move: (Hxy) => /main IH1 ? IH2 /IH2 {}IH2.
    move: Hxy => /L_facts.closed_step Hxy Hx.
    move: (Hx) => /IH1 /t_rt /(rt_trans estep). apply.
    apply: IH2. by apply: Hxy.
Qed.

(* wrong approach ? 
Lemma inverse_main s t : L_facts.closed s -> estep (translate s) t ->
  exists u, clos_refl_trans estep t (translate u) /\ L_facts.step s u.
Proof.
  move Es': (translate s) => s' Hs Hs't.
  elim: Hs't s Hs Es'.
  - move=> {}s' {}t Ht s.
    case: s => //=.
    + case => //=.
      * move=> > ? []. admit. (* impossible *)
      * admit. (* difficult, doable *)
    + admit. (* impossible *)
  - admit. (* unclear *)
  - move=> > ? IH s.
      case => //=.
        ** move=> [|?]; first done.
           move=> > /= ? []. admit. (* impossible *)
        ** 
      
      move=> > /=.
    have :=  translate_evalue

clos_refl_trans estep (translate s) (translate t).
*)
*)

Inductive eval : eterm -> eterm -> Prop :=
| eval_evalue t : evalue t -> eval t t
| eval_K0 s t : eval s eK -> eval (eapp s t) (eapp eK t)
| eval_K s t t' v u : eval s (eapp eK v) -> eval v u -> eval t t' -> eval (eapp s t) u
| eval_S0 s t : eval s eS -> eval (eapp s t) (eapp eS t)
| eval_S1 s t u : eval s (eapp eS u) -> eval (eapp s t) (eapp (eapp eS u) t)
| eval_S s t t' v w u : eval s (eapp (eapp eS v) w) -> eval (eapp (eapp v t') (eapp w t')) u -> eval t t' -> eval (eapp s t) u.

(*
Lemma translate_shape s : L_facts.closed s ->
  (exists v, translate s = eapp eK v) \/ (exists v w, translate s = eapp (eapp eS v) w).
*)

Lemma translate_not_eK0 s : translate s = eK -> False.
Proof.
  case: s => //=.
  move=> s. case: (translate s) => //=.
  by case.
Qed.

Lemma translate_not_eS0 s : translate s = eS -> False.
Proof.
  case: s => //=.
  move=> s. case: (translate s) => //=.
  by case.
Qed.

Lemma translate_not_eS1 s t : translate s = eapp eS t -> False.
Proof.
  case: s => //=.
  - move=> > [] *. apply: translate_not_eS0. by eassumption.
  - move=> s. case: (translate s) => //=.
    by case.
Qed.

Lemma abstraction_translate_not_eS1 s t : abstraction (translate s) = eapp eS t -> False.
Proof.
  case: (translate s) => //=. by case.
Qed.

#[local] Hint Resolve translate_not_eK0 : translate.
#[local] Hint Resolve translate_not_eS0 : translate.
#[local] Hint Resolve translate_not_eS1 : translate.
#[local] Hint Resolve abstraction_translate_not_eS1 : translate.

(* not sure whether possible 
Lemma eval_translate_shape s t :
  eval (translate s) t -> L_facts.closed s -> (exists v, t = eapp eK v) \/ (exists v w, t = eapp (eapp eS v) w).
Proof.
  move Es': (translate s) => s' Hs't.
  elim: Hs't s Es'.
  - move=> ? []. 
    + move=> *. exfalso. eauto with translate.
    + admit.
    + move=> *. exfalso. eauto with translate.
    + admit.
    + admit.
  - move=> s1 s2 ? IH [] //.
    + move=> ?? [] /IH {}IH ? /L_facts.closed_app [/IH]. firstorder done.
    + intros. left. by eexists.
  - move=> > ? IH1 ? IH2 ? IH3 [] //=.
    + move=> ?? [] /IH1 {}IH1 /IH3 {}IH3.
      move=> /L_facts.closed_app [/IH1 {}IH1 /IH3 {}IH3].
      move: IH1 => [|]; last by firstorder done.

    move=> /= s. have:= IH s.
    intuition. move=>
    +
  -
  
  move=> ? /translate_not_eK *. exfalso. auto. done. eauto with translate. Print evalue. 
*)

Inductive ered : eterm -> eterm -> Prop :=
  | eredK  s t       : ered (eapp (eapp eK s) t) s
  | eredS  s t u     : ered (eapp (eapp (eapp eS s) t) u) (eapp (eapp s u) (eapp t u)).

Lemma eval_red s t u : eval s u -> ered s t -> eval t u.
Proof.
  move=> Hsu. elim: Hsu t.
  - move=> ?? H1 H2. admit.
  - move=> {}s {}u. admit. (* impossible  *)
  - 
Admitted.


(* lets assume this works *)
Lemma main2 s t : L.eval s t -> L_facts.closed s ->
  eval (translate s) (translate t).
Proof.
  elim.
  { move=> {}s ?. apply: eval_evalue. by apply: evalue_abstraction. }
  move=> {}s u {}t t' v ? IH1 ? IH2 ? IH3 /L_facts.closed_app [Hs Ht].
  move: (Hs) (Ht) => /IH1 {}IH1 /IH2 {}IH2 /=.
  move: IH1 => /=.
  have /IH3 {}IH3 : L_facts.closed (L.subst u 0 t') by admit. (* doable *)
  move: (u) IH3 => [].
  - move=> [|n] /=; last admit. (* doable *)
    move=> ? ?. apply: eval_S; [eassumption| |eassumption].
    apply: eval_K; [by apply /eval_evalue /evalue_K1|done|].
    apply: eval_evalue. by apply: evalue_K1.
  - move=> s1 s2 /= H1 IH1.
    apply: eval_S; [eassumption| |eassumption].
    case: s1 H1 {IH1}.
    + move=> [|n]; last admit. (* doable *)
      move=> /=. admit.
    + admit.
    + admit.
  - admit.
Admitted.

(* lets assume this works *)
Lemma inverse_main2 s u : 
  eval (translate s) u -> L_facts.closed s -> exists t, L.eval s t.
Proof.
  move Es': (translate s) => s' Hs'u.
  elim: Hs'u s Es'.
  - move=> ? [].
    + move=> *. exfalso. by eauto with translate.
    + move=> ? [] //=.
      * move=> > [] *. exfalso. by eauto with translate.
      * move=> *. eexists. by apply: L.eval_abs.
    + move=> *. exfalso. by eauto with translate.
    + move=> ? [] //=.
      * move=> > [] *. exfalso. by eauto with translate.
      * move=> *. exfalso. by eauto with translate.
    + move=> ?? [] //=.
      * move=> > [] *. exfalso. by eauto with translate.
      * move=> *. eexists. by apply: L.eval_abs.
  - move=> s t ? IH [] //=; first last.
    { move=> *. eexists. by apply: L.eval_abs. }
    admit. (* this should be impossible, LEMMA! *)
  - move=> s t t' v {}u ? IH1 ? IH2 ? IH3 [] //=; first last.
    { move=> *. eexists. by apply: L.eval_abs. }
    move=> s1 s2 [].
    move=> /IH1 {}IH1 /IH3 {}IH3 /L_facts.closed_app [].
    

    move=> s1 s2 [] /IH. 

(* direct one full reduction *)

Inductive eterm : Type :=
  | eK : eterm
  | eS : eterm
  | evar (n : nat) : eterm
  | eapp (s : eterm) (t : eterm) : eterm.

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

Fixpoint eren (xi : nat -> nat) (t : eterm) : eterm  :=
  match t with
  | evar x => evar (xi x)
  | eapp s t => eapp (eren xi s) (eren xi t)
  | _ => t
  end.

(* variable capturing substitution : bad idea *)
Fixpoint esubst' (s : eterm) (k : nat) (u : eterm) :=
  match s with
    | evar n => if Nat.eqb n k then u else evar n
    | eapp s t => eapp (esubst' s k u) (esubst' t k u)
    | _ => s
  end.

Definition closed' s := forall n t, esubst' s n t = s.

Inductive evalue : eterm -> Prop :=
  | evalue_K0 : evalue eK
  | evalue_K1 t : evalue (eapp eK t)
  | evalue_S0 : evalue eS
  | evalue_S1 t : evalue (eapp eS t)
  | evalue_S2 s t : evalue (eapp (eapp eS s) t).

(* capturing definitions *)

Inductive estep : eterm -> eterm -> Prop :=
  | estepK  s t       : evalue t -> estep (eapp (eapp eK s) t) s
  | estepS  s t u     : evalue u -> estep (eapp (eapp (eapp eS s) t) u) (eapp (eapp s u) (eapp t u))
  (* wrong because reduces s in (K s) *)
  | estepAppR s t  t' : estep t t' -> estep (eapp s t) (eapp s t')
  | estepAppL s s' t  : estep s s' -> estep (eapp s t) (eapp s' t).
  
Fixpoint contains_evar n (t : eterm) : bool :=
  match t with
  | evar m => if Nat.eqb n m then true else false
  | eapp s t => contains_evar n s || contains_evar n t
  | _ => false
  end.
(*
Fixpoint contains_var n (t : L.term) : bool :=
  match t with
  | var m => if Nat.eqb n m then true else false
  | app s t => contains_var n s || contains_var n t
  | lam t => contains_var (S n) t
  end.
*)
(* working abstraction *)
Fixpoint abstraction (s : eterm) : eterm :=
  if contains_evar 0 s then
    match s with
    | evar 0 => eapp (eapp eS eK) eK
    | eapp s t => eapp (eapp eS (abstraction s)) (abstraction t)
    | _ => eapp eK s
    end else eapp eK (eren Nat.pred s).

Fixpoint translate (s : L.term) : eterm :=
  match s with
  | var n => evar n
  | app s t => eapp (translate s) (translate t)
  | lam t => abstraction (translate t)
  end.

  Require Import Relations PeanoNat.
  #[local] Arguments clos_trans {A}.
  #[local] Arguments clos_refl_trans {A}.
  
  From Undecidability Require L.Util.L_facts.
Require Import ssreflect ssrbool ssrfun.
Unset Implicit Arguments.

Lemma evalue_abstraction t : evalue (abstraction t).
Proof.
  elim: t => /=.
  - by auto using evalue.
  - by auto using evalue.
  - case; by auto using evalue.
  - move=> s ? t ?.
    move: (contains_evar 0 s) (contains_evar 0 t) => [] [] /=; by auto using evalue.
Qed.

Lemma closed'_eappE s t : closed' (eapp s t) -> closed' s /\ closed' t.
Proof. move=> H. split => n u; by have [] := H n u. Qed.

Lemma closed'_eappI s t : closed' s -> closed' t -> closed' (eapp s t).
Proof. move=> Hs Ht n u /=. by rewrite (Hs n u) (Ht n u). Qed.

Lemma many_estepAppL s t u : clos_trans estep s t -> clos_trans estep (eapp s u) (eapp t u).
Proof.
  elim.
  - move=> > /estepAppL ?. by apply: t_step.
  - move=> > ????. by apply: t_trans; eassumption.
Qed.

Lemma many_estepAppR s t u : clos_trans estep s t -> clos_trans estep (eapp u s) (eapp u t).
Proof.
  elim.
  - move=> > /estepAppR ?. by apply: t_step.
  - move=> > ????. by apply: t_trans; eassumption.
Qed.

Lemma closed'_evarE n : closed' (evar n) -> False.
Proof. move=> /(_ n eK) /=. by rewrite Nat.eqb_refl. Qed.

Lemma closed'_erenE xi t : closed' (eren xi t) -> closed' t.
Proof.
  elim: t; [done|done| |].
  - by move=> > /closed'_evarE.
  - move=> ? IH1 ? IH2.
    move=> /closed'_eappE [/IH1 + /IH2].
    by apply: closed'_eappI.
Qed.

Lemma closed'_eren xi {t} : closed' t -> eren xi t = t.
Proof.
  elim: t; [done|done| |].
  - by move=> > /closed'_evarE.
  - move=> /= ? IH1 ? IH2.
    by move=> /closed'_eappE [/IH1 -> /IH2 ->].
Qed.

Lemma estep_abstraction s t :
  evalue t -> closed' (abstraction s) -> clos_trans estep (eapp (abstraction s) t) (esubst' s 0 t).
Proof.
  move=> Ht. elim: s.
  - move=> ?. apply: t_step. by apply: estepK.
  - move=> ?. apply: t_step. by apply: estepK.
  - move=> [|n] /= H.
    + apply: t_trans. { apply: t_step. by apply: estepS. }
      apply: t_step. apply: estepK. by apply: evalue_K1.
    + by move: H => /closed'_eappE [_] /closed'_evarE.
  - move=> s1 IH1 s2 IH2.
    case Hs1s2: (contains_evar 0 (eapp s1 s2)).
    + move: Hs1s2 => /= ->.
      move=> /closed'_eappE [/closed'_eappE] [_].
      move=> /IH1 {}IH1 /IH2 {}IH2.
      apply: t_trans. { apply: t_step. by apply: estepS. }
      apply: t_trans. { apply: many_estepAppL. by eassumption. }
      by apply: many_estepAppR.
    + move: (Hs1s2) => /= ->.
      move=> /closed'_eappE [_] /closed'_eappE [] /closed'_erenE Hs1 /closed'_erenE Hs2.
      move: Hs1 Hs2 (Hs1) (Hs2) => -> -> /closed'_eren -> /closed'_eren ->.
      apply: t_step. by apply: estepK.
Qed.

Lemma closed'_not_contains_evar t n : closed' t -> contains_evar n t = false.
Proof.
  elim: t; [done|done| |].
  - by move=> > /closed'_evarE.
  - by move=> s IH1 t IH2 /closed'_eappE /= [/IH1 -> /IH2 ->].
Qed.

Lemma esubst'_eren_pred s n t : closed' t -> contains_evar 0 s = false ->
  esubst' (eren Nat.pred s) n t = eren Nat.pred (esubst' s (S n) t).
Proof.
  move=> Ht. elim: s; [done|done| |].
  - move=> [|m]; first done.
    move=> _ /=. case: (Nat.eqb m n); last done.
    by rewrite (closed'_eren Nat.pred Ht).
  - move=> s1 IH1 s2 IH2 /=.
    by move=> /norP [/negPf /IH1 -> /negPf /IH2 ->].
Qed.

Lemma contains_evar_0_esubst' s n t : closed' t ->
  contains_evar 0 (esubst' s (S n) t) = contains_evar 0 s.
Proof.
  move=> Ht. elim: s; [done|done| |].
  - move=> [|m] /=; first done.
    case: (Nat.eqb m n); last done.
    by apply: closed'_not_contains_evar.
  - by move=> /= s1 -> s2 ->.
Qed.

Lemma esubst'_abstraction s n t :
  closed' t ->
  esubst' (abstraction s) n t = abstraction (esubst' s (S n) t).
Proof.
  move=> Ht. elim: s n; [done|done| |].
  - move=> [|m] n /=; first done.
    case E: (Nat.eqb m n); last done.
    case: t Ht => > /= ; [done|done| |].
    + by move=> /closed'_evarE.
    + move=> /closed'_eappE [H1 H2].
      move: (H1) (H2) => /closed'_eren -> /closed'_eren ->.
      by move: H1 H2 => /closed'_not_contains_evar -> /closed'_not_contains_evar ->.
  - move=> s1 IH1 s2 IH2 n.
    case Hs1s2: (contains_evar 0 (eapp s1 s2)).
    + rewrite /= !contains_evar_0_esubst' //.
      move: Hs1s2 => /= ->. by rewrite /= IH1 IH2.
    + rewrite /= !contains_evar_0_esubst' //.
      move: (Hs1s2) => /= ->.
      move: Hs1s2 => /= /norP [/negPf ? /negPf ?].
      by rewrite !esubst'_eren_pred.
Qed.

Lemma not_contains_evar_closed' t : (forall n, contains_evar n t = false) -> closed' t.
Proof.
  elim: t; [done|done| |].
  - move=> m /(_ m) /=. by rewrite Nat.eqb_refl.
  - move=> /= s IH1 t IH2 H. apply: closed'_eappI.
    + apply: IH1 => n. by have /norP [/negPf ->] := H n.
    + apply: IH2 => n. by have /norP [_ /negPf ->] := H n.
Qed.

Lemma contains_evar_pred n t : contains_evar 0 t = false ->
  contains_evar n (eren Nat.pred t) = contains_evar (S n) t.
Proof.
  elim: t; [done|done|by case|].
  by move=> s IH1 t IH2 /= /norP [/negPf /IH1 -> /negPf /IH2 ->].
Qed.

Lemma contains_evar_abstraction n s : contains_evar n (abstraction s) = contains_evar (S n) s.
Proof.
  elim: s; [done|done|by case|].
  move=> s IH1 t IH2.
  case H: (contains_evar 0 (eapp s t)).
  - move: H => /= -> /=. by rewrite IH1 IH2.
  - move: (H) => /= -> /=.
    by move: H => /= /norP [/negPf /contains_evar_pred -> /negPf /contains_evar_pred ->].
Qed.

Lemma closed'_translate s : L_facts.closed s -> closed' (translate s).
Proof.
  move=> /L_facts.closed_dcl Hs.
  apply: not_contains_evar_closed' => n.
  have : 0 <= n by lia.
  move: (0) Hs n => ?. elim.
  - move=> m x ? n /= ?.
    by have /Nat.eqb_neq -> : n <> x by lia.
  - move=> > ? IH1 ? IH2 ?? /=.
    rewrite IH1; [done|]. by rewrite IH2.
  - move=> > ? IH n ? /=.
    rewrite contains_evar_abstraction. apply: IH. lia.
Qed.

Lemma esubst'_translate s n t : L_facts.closed t ->
  esubst' (translate s) n (translate t) = translate (L.subst s n t).
Proof.
  move=> Ht. elim: s n => /=.
  - move=> m n. by case: (Nat.eqb m n).
  - move=> s1 IH1 s2 IH2 n. by rewrite IH1 IH2.
  - move=> s IH n. rewrite esubst'_abstraction. { by apply: closed'_translate. }
    by rewrite IH.
Qed.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

(* actually plus instead of star *)
(* this can be shown *)
Lemma main s t : L_facts.step s t -> L_facts.closed s ->
  clos_trans estep (translate s) (translate t).
Proof.
  elim.
  - move=> {}s {}t /= /L_facts.closed_app [Hs Ht].
    have /(estep_abstraction (translate s)) := evalue_abstraction (translate t).
    apply: unnest. { by apply: (closed'_translate (lam s)). }
    congr clos_trans.
    by apply: (esubst'_translate _ _ (lam t)).
  - move=> > ? IH /L_facts.closed_app [_ /IH] /=.
    by apply: many_estepAppR.
  - move=> > ? IH /L_facts.closed_app [/IH + _] /=.
    by apply: many_estepAppL.
Qed.

Lemma t_rt x y : clos_trans estep x y -> clos_refl_trans estep x y.
Proof. Admitted.

Arguments rt_trans {A} R.

Lemma main' s t : L.eval s t -> L_facts.closed s ->
  clos_refl_trans estep (translate s) (translate t).
Proof.
  move=> /L_facts.eval_iff []. elim.
  - move=> ? [] s' -> ?. by apply: rt_refl.
  - move=> > Hxy. move: (Hxy) => /main IH1 ? IH2 /IH2 {}IH2.
    move: Hxy => /L_facts.closed_step Hxy Hx.
    move: (Hx) => /IH1 /t_rt /(rt_trans estep). apply.
    apply: IH2. by apply: Hxy.
Qed.

(* wrong approach ? 
Lemma inverse_main s t : L_facts.closed s -> estep (translate s) t ->
  exists u, clos_refl_trans estep t (translate u) /\ L_facts.step s u.
Proof.
  move Es': (translate s) => s' Hs Hs't.
  elim: Hs't s Hs Es'.
  - move=> {}s' {}t Ht s.
    case: s => //=.
    + case => //=.
      * move=> > ? []. admit. (* impossible *)
      * admit. (* difficult, doable *)
    + admit. (* impossible *)
  - admit. (* unclear *)
  - move=> > ? IH s.
      case => //=.
        ** move=> [|?]; first done.
           move=> > /= ? []. admit. (* impossible *)
        ** 
      
      move=> > /=.
    have :=  translate_evalue

clos_refl_trans estep (translate s) (translate t).
*)

Inductive eval : eterm -> eterm -> Prop :=
| eval_evalue t : evalue t -> eval t t
| eval_K0 s t : eval s eK -> eval (eapp s t) (eapp eK t)
| eval_K s t t' v u : eval s (eapp eK v) -> eval v u -> eval t t' -> eval (eapp s t) u
| eval_S0 s t : eval s eS -> eval (eapp s t) (eapp eS t)
| eval_S1 s t u : eval s (eapp eS u) -> eval (eapp s t) (eapp (eapp eS u) t)
| eval_S s t t' v w u : eval s (eapp (eapp eS v) w) -> eval (eapp (eapp v t') (eapp w t')) u -> eval t t' -> eval (eapp s t) u.

(*
Lemma translate_shape s : L_facts.closed s ->
  (exists v, translate s = eapp eK v) \/ (exists v w, translate s = eapp (eapp eS v) w).
*)

Lemma translate_not_eK s : translate s = eK -> False.
Proof.
  case: s => //=.
  move=> s. case: (translate s) => //=.
  - by case.
  - move=> {}s t. by case: (contains_evar 0 s || contains_evar 0 t).
Qed.

Lemma translate_not_eS s : translate s = eS -> False.
Proof.
  case: s => //=.
  move=> s. case: (translate s) => //=.
  - by case.
  - move=> {}s t. by case: (contains_evar 0 s || contains_evar 0 t).
Qed.

#[local] Hint Resolve translate_not_eK : translate.
#[local] Hint Resolve translate_not_eS : translate.

(* not sure whether possible 
Lemma eval_translate_shape s t :
  eval (translate s) t -> L_facts.closed s -> (exists v, t = eapp eK v) \/ (exists v w, t = eapp (eapp eS v) w).
Proof.
  move Es': (translate s) => s' Hs't.
  elim: Hs't s Es'.
  - move=> ? []. 
    + move=> *. exfalso. eauto with translate.
    + admit.
    + move=> *. exfalso. eauto with translate.
    + admit.
    + admit.
  - move=> s1 s2 ? IH [] //.
    + move=> ?? [] /IH {}IH ? /L_facts.closed_app [/IH]. firstorder done.
    + intros. left. by eexists.
  - move=> > ? IH1 ? IH2 ? IH3 [] //=.
    + move=> ?? [] /IH1 {}IH1 /IH3 {}IH3.
      move=> /L_facts.closed_app [/IH1 {}IH1 /IH3 {}IH3].
      move: IH1 => [|]; last by firstorder done.

    move=> /= s. have:= IH s.
    intuition. move=>
    +
  -
  
  move=> ? /translate_not_eK *. exfalso. auto. done. eauto with translate. Print evalue. 
*)

(* lets assume this works *)
Lemma main2 s t : L.eval s t -> L_facts.closed s ->
  eval (translate s) (translate t).
Proof.
  elim.
  { move=> {}s ?. apply: eval_evalue. by apply: evalue_abstraction. }
  move=> {}s u {}t t' v ? IH1 ? IH2 ? IH3 /L_facts.closed_app [Hs Ht].
  move: (Hs) (Ht) => /IH1 {}IH1 /IH2 {}IH2 /=.
  move: IH1 => /=.
  have /IH3 {}IH3 : L_facts.closed (L.subst u 0 t') by admit. (* doable *)
  move: (u) IH3 => [].
  - move=> [|n] /=; last admit. (* doable *)
    move=> ? ?. apply: eval_S; [eassumption| |eassumption].
    apply: eval_K; [by apply /eval_evalue /evalue_K1|done|].
    apply: eval_evalue. by apply: evalue_K1.
  - move=> s1 s2 H1.
    apply: evalK. move: 

  case Hu: (contains_evar 0 (translate u)).
  - case Hu': (translate u) => [||n|].
    + exfalso. by eauto with translate.
    + exfalso. by eauto with translate.
    + move: n Hu' Hu => [|n] ->; last done.
      move=> /= _ ?. apply: eval_S; [eassumption| |eassumption].
      apply: eval_K; [by apply /eval_evalue /evalue_K1| |]. move: 
    admit. (* doable *)
Admitted.


(* lets assume this works *)
Lemma inverse_main2 s u : 
  eval (translate s) u -> L_facts.closed s -> exists t, L.eval s t.
Proof.
  move Es': (translate s) => s' Hs'u.
  elim: Hs'u s Es'.
  - move=> ? [].
    + admit. (* impossible *)
    + move=> ? [] //=.
      * admit. (* impossible *)
      * move=> *. eexists. by apply: L.eval_abs.
    + admit. (* impossible *)
    + admit. (* impossible *)
    + move=> ?? [] //=.
      * admit. (* impossible *)
      * move=> *. eexists. by apply: L.eval_abs.
  -


Inductive term : Type :=
  | term_K : eterm
  | term_S : eterm
  | term_app (s : eterm) (t : eterm) : eterm.

(*
OBSOLETE



(* exponential translation, doesnt fully work *)
Fixpoint abstraction (s : eterm) : eterm :=
  match s with
  | evar 0 => eapp (eapp eS eK) eK
  | evar (S n) => eapp eK (evar n)
  | eapp s t => eapp (eapp eS (abstraction s)) (abstraction t)
  | _ => eapp eK s
  end.

Fixpoint translate (s : L.term) : eterm :=
  match s with
  | var n => evar n
  | app s t => eapp (translate s) (translate t)
  | lam t => abstraction (translate t)
  end.

  Require Import Relations PeanoNat.
  #[local] Arguments clos_trans {A}.
  From Undecidability Require L.Util.L_facts.
Require Import ssreflect ssrbool ssrfun.
Unset Implicit Arguments.

Lemma evalue_abstraction t : evalue (abstraction t).
Proof.
  elim: t => /=.
  - by auto using evalue.
  - by auto using evalue.
  - case; by auto using evalue.
  - by auto using evalue.
Qed.

Lemma closed'_eapp s t : closed' (eapp s t) -> closed' s /\ closed' t.
Proof. Admitted.

Lemma many_estepAppL s t u : clos_trans estep s t -> clos_trans estep (eapp s u) (eapp t u).
Proof.
  elim.
  - move=> > /estepAppL ?. by apply: t_step.
  - move=> > ????. by apply: t_trans; eassumption.
Qed.

Lemma many_estepAppR s t u : clos_trans estep s t -> clos_trans estep (eapp u s) (eapp u t).
Proof.
  elim.
  - move=> > /estepAppR ?. by apply: t_step.
  - move=> > ????. by apply: t_trans; eassumption.
Qed.

Lemma estep_abstraction s t :
  evalue t -> closed' (abstraction s) -> clos_trans estep (eapp (abstraction s) t) (esubst' s 0 t).
Proof.
  move=> Ht. elim: s => /=.
  - move=> ?. apply: t_step. by apply: estepK.
  - move=> ?. apply: t_step. by apply: estepK.
  - move=> [|n] /= H.
    + apply: t_trans. { apply: t_step. by apply: estepS. }
      apply: t_step. apply: estepK. by apply: evalue_K1.
    + exfalso. move: H => /closed'_eapp [_].
      move=> /(_ n eK) /=. by rewrite Nat.eqb_refl.
  - move=> s1 IH1 s2 IH2 /closed'_eapp [/closed'_eapp [_]].
    move=> /IH1 {}IH1 /IH2 {}IH2.
    apply: t_trans. { apply: t_step. by apply: estepS. }
    apply: t_trans. { apply: many_estepAppL. by eassumption. }
    by apply: many_estepAppR.
Qed.

Lemma aaa s n t :
closed' t ->
esubst' (abstraction s) n t =
abstraction (esubst' s (S n) t).
Proof.
  move=> Ht. elim: s n => /=.
  - done.
  - done.
  - move=> [|m] n /=; first done.
    case E: (Nat.eqb m n); last done.
    case: t Ht.
    + done.
    + done.
    + admit. (* doable *)
    + cbn.
    (* works only if t is closed !!!!!!!!! *)
    admit.
  - move=> s1 IH1 s2 IH2 n. by rewrite IH1 IH2.
Admitted.

Lemma esubst'_translate s n t :
  L_facts.closed t ->
  esubst' (translate s) n (translate t) =
  translate (L.subst s n t).
Proof.
  move=> Ht. elim: s n => /=.
  - move=> m n. by case: (Nat.eqb m n).
  - move=> s1 IH1 s2 IH2 n. by rewrite IH1 IH2.
  - move=> s IH n. by rewrite aaa IH.
Qed.


(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.



(* actually plus instead of star *)
(* this can be shown *)
Lemma main s t : L_facts.step s t -> L_facts.closed s ->
  clos_trans estep (translate s) (translate t).
Proof.
  elim.
  - move=> {}s {}t /= ?.
    have /(estep_abstraction (translate s)) := evalue_abstraction (translate t).
    apply: unnest. { admit. }
    congr clos_trans.
    apply: (esubst'_translate _ _ (lam t)).
  - move=> > ? IH /L_facts.closed_app [_ /IH] /=.
    by apply: many_estepAppR.
  - move=> > ? IH /L_facts.closed_app [/IH + _] /=.
    by apply: many_estepAppL.
Admitted.
      

(* full SK translation *)
Inductive translate : L.term -> eterm -> Prop :=
  | translate_var n : translate (var n) (evar n)
  | translate_app s t s' t' : translate s s' -> translate t t' -> translate (app s t) (eapp s' t')
  | translate_lam_I : translate (lam (var 0)) (eapp (eapp eS eK) eK)
  | translate_lam_K s s' s'' : s = ren S s' -> translate s' s'' -> translate (lam s) (eapp eK s'')
  (* this is wrong! S (\s') (\t') *)
  | translate_lam_S s s' s'' : contains_var 0 s = true -> translate s (eapp s' s'') -> translate (lam s) (eapp (eapp eS s') s'').

  (* domain of translate *)
Inductive translate_domain : L.term -> Prop :=
  | translate_domain_var n : translate_domain (var n)
  | translate_domain_app s t : translate_domain s -> translate_domain t -> translate_domain (app s t)
  | translate_domain_lam_I : translate_domain (lam (var 0))
  | translate_domain_lam_K s s' : s = ren S s' -> translate_domain s' -> translate_domain (lam s)
  | translate_domain_lam_S s : contains_var 0 s = true -> translate_domain s -> translate_domain (lam s).

Definition translate_domainE {s} : translate_domain s -> 
  match s with
  | app s' t' => translate_domain s' /\ translate_domain t'
  | _ => True
  end :=
    fun H => match H with
    | translate_domain_app s t Hs Ht => conj Hs Ht
    | _ => I
    end.


Fixpoint translate' s (Ds : translate_domain s) {struct Ds} : { t | translate s t }.
Proof.
  case: s Ds.
  - move=> n *. exists (evar n). by apply: translate_var.
  - move=> s t H. have [Hs Ht] := translate_domainE H.
    have [s' Hs'] := translate' s Hs.
    have [t' Ht'] := translate' t Ht.
    exists (app )

Lemma translate_domain_total s : translate_domain s.
Proof.
  elim: s.
  - by apply: translate_domain_var.
  - move=> *. by apply: translate_domain_app.
  - move=> s. case Es: (contains_var 0 s) => [|].
    { by apply: translate_domain_lam_S. }
    move=> ?. apply: translate_domain_lam_K.
    admit. (* doable with some ren *)
Admitted.


  move=> [|n].

  
  

  
  (* actually plus instead of star *)
  (* this can be shown *)
  Lemma main s t s' t' : estep s t -> closed s ->
    translate s s' -> translate t t' ->
    clos_trans estep s' t'.
  Proof.
    elim.
    - move=> {}s {}t /=.
      move=> /SK_evalue /estepK H ?. exists 1. by apply /t_step /H.
    - move=> {}s {}t u /=.
      move=> /SK_evalue /estepS H ?. exists 1. by apply /t_step /H.
    - move=> {}s {}t Ht /=.
      case Es: (contains_evar 0 s) => [|]; first last.
      { move=> ?. exists 0 => /=.
        apply: t_step.
        move: Ht => /SK_evalue /estepK.
        admit. (* actually doable because s' is closed and renamings do nothing
        apply: ARS.starR.*) }
      case: s Es.
      + done.
      + done.
      + move=> [|n] ??; last done.
        exists 1 => /=.
        apply: t_trans; [apply: t_step|]. { apply: estepS. by apply: SK_evalue. }
        apply: t_step. apply: estepK. by apply: evalue_K1.
      + move=> {}s u ?? /=. exists 1 => /=.
        apply: t_trans; [apply: t_step|]. { apply: estepS. by apply: SK_evalue. }
        apply: t_trans; [apply: t_step|]. { apply: estepAppR. apply: estepApp. by apply: SK_evalue. }
        apply: t_trans; [apply: t_step|]. { apply: estepAppL. apply: estepApp. by apply: SK_evalue. }
        (* BREAKS DOWN! *)
        

(* old multistep reduction *)

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

(* based on first elam term: does not work because of S s [t] u <> s [u] (t u) 
based on both terms does not work because (\x.F G) H does wrongly translate H
*)

(* full SK translation *)
Inductive translate : L.term -> eterm -> Prop :=
  | translate_eK : translate (lam (var 0)) eK.
  | translate_eS : translate eS eS
  | translate_evar n : translate (evar n) (evar n)
  | translate_eapp s t s' t' : translate s s' -> translate t t' -> translate (eapp s t) (eapp s' t')
  | translate_elam_I : translate (elam (evar 0)) (eapp (eapp eS eK) eK)
  | translate_elam_K s s' s'' : s = eren S s' -> translate s' s'' -> translate (elam s) (eapp eK s'')
  | translate_elam_S s s' s'' : contains_evar 0 s = true -> translate s (eapp s' s'') -> translate (elam s) (eapp (eapp eS s') s'').

(* domain of translate *)
Inductive translate_domain : eterm -> Prop :=
  | translate_domain_eK : translate_domain eK
  | translate_domain_eS : translate_domain eS
  | translate_domain_evar n : translate_domain (evar n)
  | translate_domain_eapp s t : translate_domain s -> translate_domain t -> translate_domain (eapp s t)
  | translate_domain_elam_I : translate_domain (elam (evar 0))
  | translate_domain_elam_K s s' : s = eren S s' -> translate_domain s' -> translate_domain (elam s)
  | translate_domain_elam_S s : contains_evar 0 s = true -> translate_domain s -> translate_domain (elam s).



From Undecidability Require L.Util.L_facts.
Require Import ssreflect ssrbool ssrfun.
Require Import Relations.
#[local] Arguments clos_trans {A}.

(* actually plus instead of star *)
(* this can be shown *)
Lemma main s t s' t' : estep s t -> closed s ->
  translate s s' -> translate t t' ->
  clos_trans estep s' t'.
Proof.
  elim.
  - move=> {}s {}t /=.
    move=> /SK_evalue /estepK H ?. exists 1. by apply /t_step /H.
  - move=> {}s {}t u /=.
    move=> /SK_evalue /estepS H ?. exists 1. by apply /t_step /H.
  - move=> {}s {}t Ht /=.
    case Es: (contains_evar 0 s) => [|]; first last.
    { move=> ?. exists 0 => /=.
      apply: t_step.
      move: Ht => /SK_evalue /estepK.
      admit. (* actually doable because s' is closed and renamings do nothing
      apply: ARS.starR.*) }
    case: s Es.
    + done.
    + done.
    + move=> [|n] ??; last done.
      exists 1 => /=.
      apply: t_trans; [apply: t_step|]. { apply: estepS. by apply: SK_evalue. }
      apply: t_step. apply: estepK. by apply: evalue_K1.
    + move=> {}s u ?? /=. exists 1 => /=.
      apply: t_trans; [apply: t_step|]. { apply: estepS. by apply: SK_evalue. }
      apply: t_trans; [apply: t_step|]. { apply: estepAppR. apply: estepApp. by apply: SK_evalue. }
      apply: t_trans; [apply: t_step|]. { apply: estepAppL. apply: estepApp. by apply: SK_evalue. }
      (* BREAKS DOWN! *)
      
      
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



(* based on first elam term: does not work because of S s [t] u <> s [u] (t u) *)

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

#[local] Arguments clos_trans {A}.

(* actually plus instead of star *)
(* this can be shown *)
Lemma main s t : estep s t -> closed s ->
  exists n, clos_trans estep (SK_step s) (Nat.iter n SK_step t).
Proof.
  elim.
  - move=> {}s {}t /=. move E: (contains_elam s) => [].
    + move=> /estepK ??. exists 1. by apply: t_step.
    + move=> /SK_evalue /estepK ??. exists 1.
      move: E => /SK_step_not_contains_elam /= ->.
      by apply: t_step.
  - move=> {}s {}t u /=. move Es: (contains_elam s) => [] /=.
    + move=> /estepS ??. exists 1. apply: t_step.
      by rewrite /= Es /=.
    + move Et: (contains_elam t) => [].
      * move=> /estepS ??. exists 1. apply: t_step.
        rewrite /= Es /=.
      
      move=> /SK_evalue /estepK ??. exists 1.
      move: E => /SK_step_not_contains_elam /= ->.
      by apply: t_step.
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

