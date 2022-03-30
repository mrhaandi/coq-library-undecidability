Require Import Undecidability.IntersectionTypes.CD.
Require Import Undecidability.CounterMachines.CM2X.

Require Import Undecidability.IntersectionTypes.Util.CD_facts.

Require Import List Relations PeanoNat Lia.
Import ListNotations.
Import CD (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Section Argument.

Context (P : Cm2x).

#[local] Notation ZERO := (lam (lam (var 1))).
#[local] Notation SUCC x := (lam (lam (app (var 0) (ren (funcomp S S) x)))).

(* Scott encoding of nat *)
Fixpoint enc_nat n :=
  match n with
  | 0 => lam (lam (var 1))
  | S n => lam (lam (app (var 0) (enc_nat n))) 
  end.

Definition NONE := lam (lam (var 1)).

Definition many_lam n M := Nat.iter n lam M.

Definition many_app M Ms := fold_left app Ms M.

Compute (many_app (var 0) [(var 1); (var 2); (var 3)]). 

Definition many_subst M Ms := subst (fold_right scons var Ms) M.

(* \a.\b.\W.I *)
Definition HALT := many_lam 4 (var 0).

Lemma many_subst_lam M Ms : many_subst (lam M) Ms = lam (subst (scons (var 0) (fun x=> ren S (fold_right scons var Ms x))) M).
Proof. done. Qed.

Notation tm_steps := (CD_facts.steps).

Lemma steps_many_app_many_lam n M Ms : 
  tm_steps (many_app (many_lam (n + length Ms) M) Ms) (many_subst (many_lam n M) (rev Ms)).
Proof.
  elim /rev_ind : Ms M n.
  { move=> M n /=.
    have -> : n + 0 = n by lia.
    rewrite /many_subst /= simpl_tm.
    by apply: rt_refl. }
  move=> N Ms IH M n /=.
  rewrite app_length /= /many_app fold_left_app /= -/(many_app _ _).
  have -> : n + (length Ms + 1) = (S n) +  length Ms by lia.
  apply: rt_trans.
  - apply: stepsAppL. by apply: IH.
  - rewrite /= many_subst_lam. apply: rt_step. apply: stepRed'.
    rewrite /many_subst rev_app_distr /= !simpl_tm.
    apply: ext_subst_tm => - [|x]; first done.
    by rewrite /= !simpl_tm.
Qed.

(* select i-th argument *)
Definition enc_tab i k :=
  many_lam k (if (Nat.ltb i k) then var i else HALT).

Lemma enc_tab_steps_spec i Ms :
  tm_steps (many_app (enc_tab i (length Ms)) Ms) (nth i (rev Ms) HALT).
Proof.
  have := steps_many_app_many_lam 0 (if (Nat.ltb i (length Ms)) then var i else HALT) Ms.
  congr tm_steps.
  rewrite /= -rev_length.
  elim: (rev Ms) i. { by case. }
  move=> M {}Ms IH [|i]. { done. }
  rewrite /= -IH /many_subst /=.
  have ->: Nat.ltb (S i) (S (length Ms)) = Nat.ltb i (length Ms) by done.
  have -> : (if Nat.ltb i (length Ms) then var (S i) else HALT) =
    ren S (if Nat.ltb i (length Ms) then var i else HALT).
  { by case (Nat.ltb i (length Ms)). }
  by rewrite !simpl_tm.
Qed.

(* encode instruction instr at position i *)
Definition enc_instr (i : nat) (instr : Instruction) :=
  match instr with
  | inc => (* \abw.w (1+i) b (1+a) w *)
      lam (lam (lam (many_app (var 0) [enc_tab (S i) (length P); var 1; SUCC (var 2); var 0])))
  | dec j => (* \a. a (\bw.w (1+i) b 0 w) (\a'bw.w j b a' w) *)
      lam (many_app (var 0) [
        lam (lam (many_app (var 0) [enc_tab (S i) (length P); var 1; ZERO; var 0]));
        lam (lam (lam (many_app (var 0) [enc_tab j (length P); var 1; var 2; var 0])))])
  end.

Lemma iter_plus {X} {f : X -> X} {x : X} n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
  elim: m; first by rewrite Nat.add_0_r.
  move=> m /= <-. by have ->: n + S m = S n + m by lia.
Qed.

Lemma subst_many_lam sigma n M : subst sigma (many_lam n M) =
  many_lam n (subst (Nat.iter n (fun sigma=> scons (var 0) (funcomp (ren S) sigma)) sigma) M).
Proof.
  elim: n sigma. { done. }
  move=> n IH sigma. rewrite (iter_plus 1 n) /=. congr lam.
  by rewrite IH.
Qed.

Lemma subst_enc_tab sigma i n : subst sigma (enc_tab i n) = enc_tab i n.
Proof.
  rewrite /enc_tab.
  rewrite subst_many_lam. congr many_lam.
  case E: (Nat.ltb i n); last done.
  move=> /=. elim: n i E. { done. }
  move=> n IH [|i] /=. { done. }
  by move=> /IH ->.
Qed.

Lemma ren_enc_tab xi i n : ren xi (enc_tab i n) = enc_tab i n.
Proof. by rewrite ren_as_subst_tm subst_enc_tab. Qed.

Lemma subst_enc_instr sigma i instr : subst sigma (enc_instr i instr) = enc_instr i instr.
Proof. 
  case: instr=> >; by rewrite /= !subst_enc_tab.
Qed.

(* NOT NEEDED? *)
(* Scott encoding of option *)
Definition enc_option {X : Type} (e : X -> tm) (o : option X) :=
  match o with
  | None => lam (lam (var 1))
  | Some x => lam (lam (app (var 0) (e x)))
  end.

(* NOT NEEDED? *)
Definition enc_nat3 i a b :=
  lam (app (app (app (var 0) (enc_nat i)) (enc_nat a)) (enc_nat b)).

(* \i.i P0 .. Pn *)
Definition W := lam (many_app (var 0) (rev (map (fun '(i, instr) => enc_instr i instr) (combine (seq 0 (length P)) P)))).

Lemma subst_many_app sigma M Ms : 
  subst sigma (many_app M Ms) = many_app (subst sigma M) (map (subst sigma) Ms).
Proof. Admitted.

Lemma nth_combine_seq {X: Type} {l: list X} {i x d} :
  nth_error l i = Some x -> nth i (combine (seq 0 (length l)) l) d = (i, x).
Proof.
  case: d => ??.
  rewrite combine_nth. { by rewrite seq_length. }
  move=> /[dup] ?.
  rewrite seq_nth. { apply /nth_error_Some. by congruence. }
  by move=> /(@nth_error_nth X) ->.
Qed.

Lemma W_tm_steps_enc_instr {i instr} :
  nth_error P i = Some instr ->
  tm_steps (app W (enc_tab i (length P))) (enc_instr i instr).
Proof.
  move=> Hi.
  apply: rt_trans. { apply: rt_step. by apply: stepRed'. }
  rewrite subst_many_app /=.
  have ? : i < length P. { apply /nth_error_Some. by congruence. }
  evar (Ms : list tm).
  have := enc_tab_steps_spec i Ms. subst Ms. congr tm_steps.
  - congr many_app. congr enc_tab.
    rewrite map_length rev_length map_length combine_length seq_length. lia.
  - rewrite map_rev rev_involutive map_map (map_nth' (0, inc)).
    { rewrite combine_length seq_length. lia. }
    by rewrite (nth_combine_seq Hi) subst_enc_instr.
Qed.

Lemma subst_enc_nat sigma n : subst sigma (enc_nat n) = enc_nat n.
Proof.
  elim: n sigma. { done. }
  move=> n IH ? /=. by rewrite IH.
Qed.

Lemma ren_enc_nat xi n : ren xi (enc_nat n) = enc_nat n.
Proof. by rewrite ren_as_subst_tm subst_enc_nat. Qed.

Definition W_norm := (ren_enc_nat, ren_enc_tab, subst_enc_nat, subst_enc_tab).

Lemma W_step i a b i' a' b' : CM2X.step P (i, (a, b)) = Some (i', (a', b')) -> 
  tm_steps 
    (many_app W [enc_tab i (length P); enc_nat a; enc_nat b; W])
    (many_app W [enc_tab i' (length P); enc_nat a'; enc_nat b'; W]).
Proof.
  rewrite /CM2X.step.
  case Ei: (nth_error P i) => [instr|] Hinstr; last done.
  apply: rt_trans.
  { do 3 apply: stepsAppL. by apply: (W_tm_steps_enc_instr Ei). }
  case: instr Hinstr {Ei}.
  - (* case inc *)
    move=> [<- <- <-] /=.
    apply: rt_trans. { do 2 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
    rewrite /= !W_norm.
    apply: rt_trans. { do 1 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
    rewrite /= !W_norm.
    apply: rt_trans. { do 0 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
    rewrite /= !W_norm.
    by apply: rt_refl.
  - (* case dec j *)
    case: a.
    + move=> j [<- <- <-] /=.
      apply: rt_trans. { do 2 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 3 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 2 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 1 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 0 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      by apply: rt_refl.
    + move=> j a [<- <- <-] /=.
      apply: rt_trans. { do 2 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 3 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 2 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 2 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 1 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      apply: rt_trans. { do 0 apply: stepsAppL. apply: rt_step. by apply: stepRed. }
      rewrite /= !W_norm.
      by apply: rt_refl.
Qed.
