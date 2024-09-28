Require Import List PeanoNat Lia Relations Transitive_Closure.
Import ListNotations.

From Undecidability Require Import MinskyMachines.MMA L.L Shared.Libs.DLW.Code.sss.
From Undecidability Require MinskyMachines.MM.
Import MM (mm_instr).
Require Import Undecidability.Shared.simulation.
(* TODO refactor into shared lemmas *)
Require Undecidability.MinskyMachines.Reductions.MMA_computable_to_MMA_mon_computable.
Require Import ssreflect.

Require Undecidability.L.Util.L_facts.
Import L_facts (step).

Require Undecidability.L.Prelim.ARS.

(* TODO remove *)
Axiom FF : False.

Unset Implicit Arguments.

(* general facts *)

Lemma vec_pos_nth {X : Type} {n} {v : Vector.t X n} {i} :
  vec.vec_pos v i = Vector.nth v i.
Proof.
  elim: v i; first by apply: Fin.case0.
  move=> ?? v IH i.
  pattern i. by apply: (Fin.caseS' i).
Qed.

Lemma vec_change_replace {X : Type} {n} (v : Vector.t X n) i x :
  vec.vec_change v i x = Vector.replace v i x.
Proof.
  elim: v i; first by apply: Fin.case0.
  move=> ?? v IH i.
  pattern i. apply: (Fin.caseS' i); first done.
  move=> ?. by congr Vector.cons.
Qed.

#[local] Notation lams k M := (Nat.iter k lam M).
#[local] Notation apps M Ns := (fold_left app Ns M).

Section MMA_HALTING_to_HaltLclosed.

Context {num_regs : nat}. (* number of registers - 1 *)
Notation N := (S num_regs).
Context (P : list (mm_instr (Fin.t N))). (* program *)

(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

Arguments funcomp {X Y Z} (g f) /.

(* stream cons *)
Definition scons {X : Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

(* parallel term renaming *)
Fixpoint ren (xi : nat -> nat) (t : term) : term  :=
  match t with
  | var x => var (xi x)
  | app s t => app (ren xi s) (ren xi t)
  | lam t => lam (ren (scons 0 (funcomp S xi)) t)
  end.

(* remap machine addresses to 0 .. n (n + 1 => 0) *)
Definition addr i :=
  match i - length P with
  | 0 => i
  | S i => 0
  end.

Definition enc_pair t1 t2 := lam (apps (var 0) [t1; t2]).

Definition enc_regs (regs : Vector.t nat N) := lam (apps (var 0) (Vector.to_list (Vector.map nat_enc regs))).

Definition pi i := lams (S (length P)) (var i).

Lemma eval_pi i : eval (pi i) (pi i).
Proof.
  constructor.
Qed.

#[local] Hint Resolve eval_pi : core.

Definition pi_succ := lam (apps (var 0) (map pi ((seq 1 (length P)) ++ [0]))).

Definition nat_succ := lam (lam (lam (app (var 0) (var 2)))).

Lemma subst_apps s k t ts : subst (apps t ts) k s = apps (subst t k s) (map (fun u => subst u k s) ts).
Proof.
  elim: ts t; first done.
  move=> t' ts IH t /=. by rewrite IH.
Qed.

Lemma not_eval_var_r s i : eval s (var i) -> False.
Proof.
  move E: (var i) => t H.
  elim: H i E; first done.
  move=> > ? _ ??? H ??. subst.
  by apply: H.
Qed.

Lemma not_eval_var_l t i : eval (var i) t -> False.
Proof.
  move=> H. inversion H.
Qed.

Lemma star_rt_steps_iff s t : ARS.star step s t <-> clos_refl_trans term step s t.
Proof.
  split.
  - elim=> *.
    + by apply: rt_refl.
    + by apply: rt_trans; [apply: rt_step|]; eassumption.
  - move=> /clos_rt_rt1n_iff. elim=> *.
    + by apply: ARS.starR.
    + apply: ARS.starC; by eassumption.
Qed.

Lemma eval_reflE t : eval t t -> exists s, t = lam s.
Proof.
  by move=> /L_facts.eval_iff [_].
Qed.

Lemma subst_lams n s k t : subst (lams n s) k t = lams n (subst s (n + k) t).
Proof.
  elim: n k; first done.
  move=> n IH k /=. by rewrite IH Nat.add_succ_r.
Qed.

Lemma steps_apps_l s1 s2 ts : ARS.star step s1 s2 -> ARS.star step (apps s1 ts) (apps s2 ts).
Proof.
  elim: ts s1 s2; first done.
  move=> t ts IH s1 s2 H /=. apply: IH.
  by apply: L_facts.star_trans_l.
Qed.


Fixpoint substs k ts t :=
  match t with
  | var x => nth x (map var (seq 0 k) ++ ts) (var x)
  | app s t => app (substs k ts s) (substs k ts t)
  | lam s => lam (substs (S k) ts s)
  end.

Lemma substs_apps k ts s ss : substs k ts (apps s ss) = apps (substs k ts s) (map (substs k ts) ss).
Proof.
  elim: ss s; first done.
  move=> s' ss IH s /=. by rewrite IH.
Qed.

Lemma substs_nil k t : substs k [] t = t.
Proof.
  elim: t k.
  - move=> x k /=. rewrite app_nil_r map_nth.
    have [?|?] : x < k \/ x >= k by lia.
    + by rewrite seq_nth.
    + by rewrite nth_overflow ?length_seq.
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH ? /=. by rewrite IH.
Qed.

Lemma substs_lams n s k ts : substs k ts (lams n s) = lams n (substs (n + k) ts s).
Proof.
  elim: n k; first done.
  move=> n IH k /=. by rewrite IH Nat.add_succ_r.
Qed.

Lemma substs_closed k ts t : closed t -> substs k ts t = t.
Proof.
  move=> /L_facts.closed_dcl.
  have : 0 <= k by lia.
  move: (0)=> n + H. elim: H k.
  - move=> > ? > ? /=. rewrite app_nth1.
    + rewrite length_map length_seq. lia.
    + by rewrite map_nth seq_nth; [lia|].
  - move=> > ? IH1 ? IH2 * /=.
    by rewrite IH1 ?IH2.
  - move=> > ? IH * /=. by rewrite IH; [lia|].
Qed.

Lemma substs_subst k t ts s : closed t -> Forall closed ts ->
  substs k ts (subst s (k + length ts) t) = substs k (ts ++ [t]) s.
Proof.
  move=> Ht Hts. elim: s k.
  - move=> x k /=.
    move E: (Nat.eqb x (k + length ts)) => [|].
    + move=> /Nat.eqb_eq in E. subst.
      rewrite app_assoc app_nth2 !length_app !length_map !length_seq; [lia|].
      rewrite Nat.sub_diag /=. by apply: substs_closed.
    + move=> /Nat.eqb_neq in E.
      rewrite /= !app_assoc.
      have [?|?] : x < k + length ts \/ x > k + length ts by lia.
      * rewrite (app_nth1 _ [t]); last done.
        by rewrite length_app length_map length_seq.
      * rewrite !nth_overflow; last done.
        all: rewrite !length_app length_map length_seq /=; lia.
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH ? /=. by rewrite IH.
Qed.

Lemma steps_apps_lams (ts : list term) s :
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  ARS.star step (apps (lams (length ts) s) ts) (substs 0 (rev ts) s).
Proof.
  move=> H. elim: H s.
  - move=> ? /= *. rewrite substs_nil. by apply ARS.starR.
  - move=> t' {}ts H1t' Hts IH s /Forall_cons_iff [H2t'] /[dup] ? /IH {}IH.
    move: H1t' => /L_facts.eval_iff [_] [t'' ?]. subst.
    rewrite /=. apply: ARS.star_trans.
    + apply: steps_apps_l.
      apply: ARS.starC.
      * by apply: L_facts.stepApp.
      * rewrite subst_lams.
        by apply: ARS.starR.
    + apply: ARS.star_trans; first by apply IH.
      rewrite Nat.add_0_r -length_rev.
      rewrite substs_subst; [done|by apply: Forall_rev|].
      by apply ARS.starR.
Qed.

Lemma steps_apps_lams' n (ts : list term) s :
  n = length ts ->
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  ARS.star step (apps (lams n s) ts) (substs 0 (rev ts) s).
Proof.
  move=> ->. by apply: steps_apps_lams.
Qed.

Lemma steps_eval t1 t2 t3 : ARS.star step t1 t2 -> eval t2 t3 -> eval t1 t3.
Proof.
  move=> H /L_facts.eval_iff [H1 H2].
  apply /L_facts.eval_iff. split; last done.
  apply: ARS.star_trans; by eassumption.
Qed.

Lemma eval_apps_lams (ts : list term) s t :
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  eval (substs 0 (rev ts) s) t ->
  eval (apps (lams (length ts) s) ts) t.
Proof.
  move=> /steps_apps_lams /[apply] H.
  apply: steps_eval. by apply: H.
Qed.

Lemma apps_pi_spec {i} ts t :
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  length ts = S (length P) ->
  eval (nth i (rev ts) (var 0)) t ->
  eval (apps (pi i) ts) t.
Proof.
  move=> ?? Hts Ht. rewrite /pi -Hts.
  apply: eval_apps_lams; [done..|].
  rewrite /= (nth_indep _ _ (var 0)); last done.
  suff : i >= length (rev ts) -> False by lia.
  move=> ?. rewrite nth_overflow in Ht; first done.
  by inversion Ht.
Qed.

Lemma apps_pi_spec' {i} ts t :
  i < length ts ->
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  length ts = S (length P) ->
  eval (nth (length ts - S i) ts (var 0)) t ->
  eval (apps (pi i) ts) t.
Proof.
  move=> ??? Hts Ht. rewrite /pi -Hts.
  apply: eval_apps_lams; [done..|].
  rewrite /= rev_nth; first done.
  by rewrite (nth_indep _ _ (var 0)); first lia.
Qed.

Lemma eval_apps_lams' n (ts : list term) s t :
  n = length ts ->
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  eval (substs 0 (rev ts) s) t ->
  eval (apps (lams n s) ts) t.
Proof.
  move=> ->. by apply: eval_apps_lams.
Qed.

Fixpoint vec_seq i n : Vector.t nat n :=
  match n with
  | 0 => Vector.nil _
  | S n => Vector.cons _ i _ (vec_seq (S i) n)
  end.

Fixpoint rev_vec_seq n : Vector.t nat n :=
  match n with
  | 0 => Vector.nil _
  | S n => Vector.cons _ n _ (rev_vec_seq n)
  end.

Opaque vec_seq.

Definition enum_regs : Vector.t term N := Vector.map var (Vector.rev (vec_seq 0 N)).

Lemma eval_enc_regs ts : eval (enc_regs ts) (enc_regs ts).
Proof.
  by constructor.
Qed.

#[local] Hint Resolve eval_enc_regs : core.

Lemma pi_closed i : i < S (length P) -> closed (pi i).
Proof.
  rewrite /pi. move: (S (length P)) => n.
  move=> H k u. rewrite subst_lams /=.
  case E: (Nat.eqb i (n + k)) => [|].
  - move=> /Nat.eqb_eq in E. lia.
  - done.
Qed.

Lemma pi_succ_closed : closed pi_succ.
Proof.
  move=> k u. rewrite /= subst_apps /= map_map.
  congr lam. congr fold_left.
  rewrite !map_app. congr List.app.
  - apply: map_ext_in=> i /in_seq.
    move=> [??]. by apply pi_closed.
  - by rewrite /= subst_lams Nat.add_succ_r /=.
Qed.

#[local] Hint Rewrite pi_succ_closed : subst.

Lemma pi_addr_closed i : closed (pi (addr i)).
Proof.
  apply: pi_closed. rewrite /addr.
  case E: (i - length P) => [|?]; lia.
Qed.

#[local] Hint Rewrite pi_addr_closed : subst.

(* get nth vector element *)
Definition enc_nth (x : Fin.t N) : term :=
  (* \c1 .. cN.cx *)
  lams N (var (N - 1 - proj1_sig (Fin.to_nat x))).

Lemma closed_enc_nth x : closed (enc_nth x).
Proof.
  move=> k u. rewrite /= subst_lams /=.
  by have /Nat.eqb_neq ->: num_regs - 0 - proj1_sig (Fin.to_nat x) <> num_regs + S k by lia.
Qed.

#[local] Hint Rewrite closed_enc_nth : subst.

Lemma eval_lams_N s : eval (lams N s) (lams N s).
Proof.
  constructor.
Qed.

Opaque Nat.iter.

Lemma nat_enc_closed n : closed (nat_enc n).
Proof.
  elim: n; first done.
  move=> n IH u k /=. by rewrite IH.
Qed.

#[local] Hint Rewrite nat_enc_closed : subst.

Lemma eval_nat_enc n : eval (nat_enc n) (nat_enc n).
Proof.
  by case: n; constructor.
Qed.

#[local] Hint Resolve eval_nat_enc : core.

Lemma nth_order_map : forall (X Y : Type) (f : X -> Y) (n : nat) (v : Vector.t X n) (i : nat) (H : i < n),
  Vector.nth_order (Vector.map f v) H = f (Vector.nth_order v H).
Proof.
  move=> X Y f n. elim; first by lia.
  move=> x {}n v IH [|i] H /=; first done.
  by apply: IH.
Qed.

Lemma nth_order_nth {X : Type} {n} (v : Vector.t X n) i {k} (H : k < n) :
  proj1_sig (Fin.to_nat i) = k -> Vector.nth_order v H = VectorDef.nth v i.
Proof.
  elim: v k i H.
  - move=> ?. by apply: Fin.case0.
  - move=> x {}n v IH [|k] i /=.
    + pattern i; apply: (Fin.caseS' i); first done.
      move=> i' /=. case: (Fin.to_nat i')=> /=. lia.
    + move=> ?. pattern i; apply: (Fin.caseS' i); first done.
      move=> i' /=. move E: (Fin.to_nat i') => [m Hm] /= [?].
      apply: IH. by rewrite E.
Qed.

Lemma enc_regs_spec v s t :
  eval (substs 0 (rev (Vector.to_list (Vector.map nat_enc v))) s) t ->
  eval (app (enc_regs v) (lams N s)) t.
Proof.
  move=> H. econstructor; [constructor|apply: eval_lams_N|].
  rewrite subst_apps /=. apply: eval_apps_lams'.
  - by rewrite length_map Vector.length_to_list.
  - apply /Forall_map. apply /Vector.to_list_Forall.
    apply /Vector.Forall_map.
    apply /Vector.Forall_nth=> y. rewrite nat_enc_closed.
    by apply: eval_nat_enc.
  - apply /Forall_map. apply /Vector.to_list_Forall.
    apply /Vector.Forall_map.
    apply /Vector.Forall_nth=> y. rewrite nat_enc_closed.
    by apply: nat_enc_closed.
  - move: H. congr eval. congr substs. congr rev.
    rewrite -Vector.to_list_map Vector.map_map.
    congr Vector.to_list. apply: Vector.map_ext.
    move=> c. by rewrite nat_enc_closed.
Qed.

Lemma enc_nth_spec x v : eval (app (enc_regs v) (enc_nth x)) (nat_enc (Vector.nth v x)).
Proof.
  apply: enc_regs_spec.
  move Ex: (Fin.to_nat x) => [n Hn] /=.
  rewrite /= rev_nth Vector.length_to_list; first lia.
  rewrite -Vector.to_list_nth_order; [|lia].
  move=> Hm. rewrite nth_order_map.
  rewrite -(Fin.of_nat_to_nat_inv x) Ex /=.
  rewrite (@nth_order_nth _ _ _ (Fin.of_nat_lt Hn)) ?Fin.to_nat_of_nat /=; first lia.
  by apply: eval_nat_enc.
Qed.

#[local] Hint Resolve enc_nth_spec : core.

Check vec.vec_change.

(* set nth vector element *)
Definition enc_replace (x : Fin.t N) : term :=
  (* \c.\c1 .. cN.\f.f c1 .. c .. cN *)
  lam (lams N (lam (apps (var 0) (map var (Vector.to_list (Vector.replace (Vector.map S (rev_vec_seq N)) x (N + 1))))))).

Lemma rev_vec_seq_S n : rev_vec_seq (S n) = Vector.cons _ n _ (rev_vec_seq n).
Proof.
  done.
Qed.

Opaque rev_vec_seq.

Lemma vec_In_nil {X : Type} {x} : Vector.In x (Vector.nil X) -> False.
Proof.
  intros H. by inversion H.
Qed.

Lemma vec_In_replace {X : Type} {n} {v : Vector.t X n} {i x y} :
  Vector.In y (Vector.replace v i x) -> y = x \/ Vector.In y v.
Proof.
  elim: v i x.
  - by apply: Fin.case0.
  - move=> x {}n v IH /= i x'.
    pattern i. apply: (Fin.caseS' i).
    + move=> /= /Vector.In_cons_iff [<-|?]; first by left.
      right. by constructor.
    + move=> /= j /Vector.In_cons_iff [<-|/IH [?|?]].
      * right. by constructor.
      * by left.
      * right. by constructor.
Qed.

Lemma vec_In_map {X Y : Type} {n} {f : X -> Y} {v : Vector.t X n} {y} :
  Vector.In y (Vector.map f v) -> exists x, y = f x /\ Vector.In x v.
Proof.
  elim: v.
  - by move=> /vec_In_nil.
  - move=> x {}n v IH /= /Vector.In_cons_iff [<-|/IH].
    + eexists. split; first done. by constructor.
    + move=> [? [-> ?]].
      eexists. split; first done. by constructor.
Qed.

Lemma vec_In_rev_seq n i : Vector.In i (rev_vec_seq n) -> i < n.
Proof.
  elim: n.
  - by move=> /vec_In_nil.
  - move=> n IH. rewrite rev_vec_seq_S.
    move=> /Vector.In_cons_iff [->|/IH]; lia.
Qed.

Lemma enc_replace_closed x : closed (enc_replace x).
Proof.
  move=> k u. rewrite /= subst_lams /= subst_apps /=.
  rewrite /enc_replace.
  rewrite map_map -!Vector.to_list_map.
  congr lam. congr Nat.iter. congr lam. congr fold_left.
  congr Vector.to_list. apply: Vector.map_ext_in => n /= /vec_In_replace H.
  have /Nat.eqb_neq ->: n <> S (S (num_regs + S k)); last done.
  move: H => [->|]; first by lia.
  move=> /vec_In_map [?] [->] /vec_In_rev_seq. lia.
Qed.

Lemma subst_app k s t u : subst (app s t) k u = app (subst s k u) (subst t k u).
Proof.
  done.
Qed.

Lemma subst_lam s k t : subst (lam s) k t = lam (subst s (S k) t).
Proof.
  done.
Qed.

Lemma enc_regs_closed v : closed (enc_regs v).
Proof.
  rewrite /enc_regs. move=> k u.
  rewrite /= subst_apps /=.
  rewrite Vector.to_list_map map_map.
  congr lam. congr fold_left.
  apply: map_ext=> ?. by rewrite nat_enc_closed.
Qed.

#[local] Hint Rewrite enc_regs_closed : subst.

Lemma eval_lam' s t : lam s = t -> eval (lam s) t.
Proof.
  move=> <-. by constructor.
Qed.

Opaque vec_seq.
Opaque Nat.sub.

Lemma vec_nth_rev_seq n i : VectorDef.nth (rev_vec_seq n) i = n - 1 - proj1_sig (Fin.to_nat i).
Proof.
  elim: n i.
  - by apply: Fin.case0.
  - move=> n IH i.
    pattern i. apply: (Fin.caseS' i).
    + rewrite rev_vec_seq_S /=. lia.
    + move=> {}i /=. rewrite rev_vec_seq_S /= IH.
      move: (Fin.to_nat i) => [m Hm] /=. lia.
Qed.

Opaque rev_vec_seq.

Lemma clos_t_rt_t {A : Type} {R : relation A} (x y z : A) :
  clos_trans A R x y -> clos_refl_trans A R y z -> clos_trans A R x z.
Proof.
  move=> H /clos_rt_rtn1_iff H'. elim: H' H; by eauto using clos_trans.
Qed.

Lemma t_steps_app_l s t1 t2 : clos_trans term step t1 t2 -> clos_trans term step (app s t1) (app s t2).
Proof.
  elim.
  - move=> > ?. apply: t_step. by apply: L_facts.stepAppR.
  - move=> *. apply: t_trans; by eassumption.
Qed.

Lemma t_steps_app_r s1 s2 t : clos_trans term step s1 s2 -> clos_trans term step (app s1 t) (app s2 t).
Proof.
  elim.
  - move=> > ?. apply: t_step. by apply: L_facts.stepAppL.
  - move=> *. apply: t_trans; by eassumption.
Qed.

Lemma rt_steps_app_l s t1 t2 : clos_refl_trans term step t1 t2 -> clos_refl_trans term step (app s t1) (app s t2).
Proof.
  elim.
  - move=> > ?. apply: rt_step. by apply: L_facts.stepAppR.
  - move=> *. by apply: rt_refl.
  - move=> *. apply: rt_trans; by eassumption.
Qed.

Lemma rt_steps_app_r s1 s2 t : clos_refl_trans term step s1 s2 -> clos_refl_trans term step (app s1 t) (app s2 t).
Proof.
  elim.
  - move=> > ?. apply: rt_step. by apply: L_facts.stepAppL.
  - move=> *. by apply: rt_refl.
  - move=> *. apply: rt_trans; by eassumption.
Qed.

Lemma rt_refl' : forall (A : Type) (R : relation A) (x y : A), x = y -> clos_refl_trans A R x y.
Proof.
  move=> > <-. by apply: rt_refl.
Qed.

Lemma step_app' s t : eval t t -> step (app (lam s) t) (subst s 0 t).
Proof.
  move=> /L_facts.eval_iff [_] [?] ->. by constructor.
Qed.

Lemma steps_app' s t1 t2 : eval t1 t2 -> ARS.star step (app (lam s) t1) (subst s 0 t2).
Proof.
  move=> /L_facts.eval_iff [?] [?] ?. subst.
  apply: ARS.star_trans.
  - apply: L_facts.star_trans_r. by eassumption.
  - apply: ARS.starC; last by apply: ARS.starR.
    by constructor.
Qed.



Lemma eval_rt_steps_subst s t1 t2 : eval t1 t2 -> clos_refl_trans _ step (app (lam s) t1) (subst s 0 t2).
Proof.
  move=> /L_facts.eval_iff [/star_rt_steps_iff ?] [?] ?. subst.
  apply: rt_trans.
  - apply: rt_steps_app_l. by eassumption.
  - apply: rt_step. by constructor.
Qed.

Lemma enc_replace_spec x v c t :
  eval t (nat_enc c) ->
  eval (app (enc_regs v) (app (enc_replace x) t)) (enc_regs (Vector.replace v x c)).
Proof.
  move=> Hc.
  apply: steps_eval.
  - apply: L_facts.star_trans_r.
    apply: steps_app'.
    by eassumption.
  - rewrite subst_lams.
    apply: enc_regs_spec.
    rewrite /= subst_apps substs_apps. apply: eval_lam'.
    rewrite /=. congr lam. congr fold_left.
    rewrite !map_map.
    rewrite -!Vector.to_list_map.
    congr Vector.to_list.
    apply /Vector.eq_nth_iff=> i ? <-.
    rewrite !(Vector.nth_map _ _ _ _ eq_refl) /=.
    have [?|?] := Fin.eq_dec i x.
    + subst i. rewrite !Vector.nth_replace_eq.
      have /Nat.eqb_eq ->: S (num_regs + 1) = S (S (num_regs + 0)) by lia.
      rewrite substs_closed; last done.
      by apply: nat_enc_closed.
    + rewrite !Vector.nth_replace_neq; [done..|].
      rewrite (Vector.nth_map _ _ _ _ eq_refl).
      rewrite vec_nth_rev_seq /=.
      have /Nat.eqb_neq -> /=: N - 1 - proj1_sig (Fin.to_nat i) <> S (num_regs + 0) by lia.
      move Ei: (Fin.to_nat i) => [n Hn] /=.
      rewrite rev_nth Vector.length_to_list; first lia.
      rewrite -Vector.to_list_nth_order; [|lia].
      move=> ?. rewrite nth_order_map. congr nat_enc.
      apply: nth_order_nth. rewrite Ei /=. lia.
Qed.

#[local] Hint Resolve enc_replace_spec : core.

Definition enc_inc (x : Fin.t N) : term :=
  (* \cs. cs ((replace x) (nat_succ (cs (nth x)))) *)
  lam (app (var 0) (app (enc_replace x) (app nat_succ (app (var 0) (enc_nth x))))).

Lemma subst_var_eq x s : subst (var x) x s = s.
Proof.
  by rewrite /= Nat.eqb_refl.
Qed.

Lemma subst_var_neq x y s : x <> y -> subst (var x) y s = var x.
Proof.
  by move=> /= /Nat.eqb_neq ->.
Qed.

#[local] Hint Rewrite enc_replace_closed : subst.

Lemma nat_succ_closed : closed nat_succ.
Proof.
  done.
Qed.

#[local] Hint Rewrite nat_succ_closed : subst.

Lemma nat_succ_spec t c : eval t (nat_enc c) -> eval (app nat_succ t) (nat_enc (S c)).
Proof.
  rewrite /nat_succ. move=> H.
  econstructor; [constructor|eassumption|].
  rewrite /=. by constructor.
Qed.

Lemma enc_nth_closed x : closed (enc_nth x).
Proof.
  move=> k u. rewrite /enc_nth /= subst_lams /=.
  congr Nat.iter.
  move: (Fin.to_nat x) => [n Hn] /=.
  by have /Nat.eqb_neq ->: N - 1 - n <> S (num_regs + k) by lia.
Qed.

#[local] Hint Rewrite enc_nth_closed : subst.

Opaque enc_regs enc_replace nat_succ enc_nth.

Lemma enc_inc_spec (x : Fin.t N) (v : Vector.t nat N) :
  eval (app (enc_inc x) (enc_regs v)) (enc_regs (Vector.replace v x (S (Vector.nth v x)))).
Proof.
  rewrite /enc_inc. econstructor; [constructor|done|].
  rewrite /= enc_replace_closed nat_succ_closed enc_nth_closed.
  apply: enc_replace_spec. apply: nat_succ_spec.
  by apply: enc_nth_spec.
Qed.

Lemma enc_inc_closed x : closed (enc_inc x).
Proof.
  move=> k u. rewrite /enc_inc /=.
  by autorewrite with subst.
Qed.

#[local] Hint Rewrite enc_inc_closed : subst.

Opaque enc_inc.

Definition enc_instr '(i, instr) : term :=
  match instr with
  | MM.mm_inc x =>
      (* \cs.(\cs'.\f.f (pi (S i)) cs') (inc x cs) *)
      lam (app (lam (lam (apps (var 0) [pi (addr (S i)); var 1]))) (app (enc_inc x) (var 0)))
  | MM.mm_dec x j =>
      (* \cs.(nth x cs) (\f. f (pi (S i)) cs) (\c.(\c'.\f. f (pi j) c') (replace x cs c)) *)
      lam (apps (var 0) [enc_nth x;
        lam (apps (var 0) [pi (addr (S i)); var 1]);
        lam (app (lam (lam (apps (var 0) [pi (addr j); var 1]))) (app (var 1) (app (enc_replace x) (var 0))))])
  end.

Lemma enc_instr_closed o : closed (enc_instr o).
Proof.
  move=> k u. case: o=> i [instr|instr x] /=; by autorewrite with subst.
Qed.

#[local] Hint Rewrite enc_instr_closed : subst.

Lemma eval_enc_instr o : eval (enc_instr o) (enc_instr o).
Proof.
  move: o => [] ? []; by constructor.
Qed.

#[local] Hint Resolve eval_enc_instr : core.

Lemma subst_enc_pair t1 t2 k s : subst (enc_pair t1 t2) k s = enc_pair (subst t1 (S k) s) (subst t2 (S k) s).
Proof.
  done.
Qed.

Lemma eval_enc_pair t1 t2 : eval (enc_pair t1 t2) (enc_pair t1 t2).
Proof.
  constructor.
Qed.

Opaque enc_pair pi_succ pi enc_regs.

Lemma eval_rt s t : eval s t -> clos_refl_trans term step s t.
Proof.
  move=> /L_facts.eval_iff [?] [?] ?. subst.
  by apply /star_rt_steps_iff.
Qed.

Definition enc_recurse :=
  (* \i.\cs.\run.run i cs run *)
  lam (lam (lam (apps (var 0) [var 2; var 1; var 0]))).

Lemma eval_enc_recurse : eval enc_recurse enc_recurse.
Proof.
  by constructor.
Qed.

Lemma enc_recurse_closed : closed enc_recurse.
Proof.
  done.
Qed.

#[local] Hint Resolve eval_enc_recurse : core.
#[local] Hint Rewrite enc_recurse_closed : subst.

Lemma step_rt_steps s t u : step s t -> clos_refl_trans _ step t u -> clos_refl_trans _ step s u.
Proof.
  move=> ??. by apply: rt_trans; [apply: rt_step|]; eassumption.
Qed.

Lemma mma_step_sim (instr : mm_instr (Fin.t N)) (p q : mm_state N) :
  mma_sss instr p q ->
  clos_refl_trans _ step
    (apps (enc_instr (fst p, instr)) [enc_regs (snd p); enc_recurse])
    (apps enc_recurse [pi (addr (fst q)); enc_regs (snd q)]).
Proof.
  case.
  - (* INC *)
    move=> i x v /=. rewrite vec_change_replace vec_pos_nth.
    apply: rt_trans.
    { apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
    apply: rt_trans.
    { apply: rt_steps_app_r. rewrite /=. apply: rt_steps_app_l.
      autorewrite with subst. apply: eval_rt. by apply: enc_inc_spec. }
    apply: rt_trans.
    { apply: rt_steps_app_r. autorewrite with subst. by apply: eval_rt_steps_subst. }
    apply: rt_trans.
    { rewrite /=. by apply: eval_rt_steps_subst. }
    rewrite /=. autorewrite with subst. by apply: rt_refl.
  - (* DEC *)
    move=> i x j v. rewrite vec_pos_nth /==> Hx.
    apply: rt_trans.
    { apply: rt_steps_app_r.
      apply: rt_trans.
      { by apply: eval_rt_steps_subst. }
      apply: rt_trans.
      { rewrite /=. autorewrite with subst. do 2 apply: rt_steps_app_r. by apply: eval_rt. }
      rewrite Hx /=. apply: rt_trans.
      { apply: rt_steps_app_r. apply: rt_step. by constructor. }
      apply: rt_step. rewrite /=. by constructor. }
    apply: rt_trans.
    { rewrite /=. autorewrite with subst. by apply: eval_rt_steps_subst. }
    rewrite /=. autorewrite with subst. by apply: rt_refl.
  - (* JUMP *)
    move=> i x j v c. rewrite vec_pos_nth vec_change_replace /==> Hx.
    apply: rt_trans.
    { apply: rt_steps_app_r.
      apply: rt_trans.
      { by apply: eval_rt_steps_subst. }
      apply: rt_trans.
      { rewrite /=. autorewrite with subst. do 2 apply: rt_steps_app_r. by apply: eval_rt. }
      rewrite Hx /=. apply: rt_trans.
      { apply: rt_steps_app_r. apply: rt_step. by constructor. }
      apply: rt_step. rewrite /=. by constructor. }
    apply: rt_trans.
    { rewrite /=. autorewrite with subst. apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
    apply: rt_trans.
    { rewrite /=. autorewrite with subst. apply: rt_steps_app_r. apply: rt_steps_app_l.
      apply: eval_rt. by apply: enc_replace_spec. }
    apply: rt_trans.
    { apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
    apply: rt_trans.
    { rewrite /=. autorewrite with subst. by apply: eval_rt_steps_subst. }
    rewrite /=. autorewrite with subst. by apply: rt_refl.
Qed.

(* \cs.\f.\run.cs *)
Definition enc_halt := lam (lam (lam (var 2))).
(* \i.i (halt :: P) *)
Definition enc_step := lam (apps (var 0) (rev (enc_halt :: map enc_instr (combine (seq 1 (length P)) P)))).
(* \i.\cs.step i cs recurse *)
Definition enc_run := lam (lam (apps enc_step [var 1; var 0; enc_recurse])).

Lemma enc_halt_closed : closed enc_halt.
Proof.
  done.
Qed.

Lemma enc_halt_spec cs : 
  clos_refl_trans _ step
  (apps enc_halt [enc_regs cs; enc_recurse; lam (lam (apps enc_step [var 1; var 0; enc_recurse]))])
  (enc_regs cs).
Proof.
  rewrite /enc_halt /=.
  apply: rt_trans.
  { do 2 apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { apply: rt_steps_app_r. rewrite /=. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { rewrite /=. apply: eval_rt_steps_subst. by constructor. }
  autorewrite with subst. by apply: rt_refl.
Qed.  

Lemma eval_enc_halt : eval enc_halt enc_halt.
Proof.
  by constructor.
Qed.

#[local] Hint Resolve eval_enc_halt : core.
#[local] Hint Rewrite enc_halt_closed : subst.

Opaque enc_recurse.
Opaque enc_halt.

Lemma map_subst_map_enc_instr k t l : map (fun u => subst u k t) (map enc_instr l) = map enc_instr l.
Proof.
  rewrite map_map. apply: map_ext=> ?. by rewrite enc_instr_closed.
Qed.

Lemma enc_step_closed : closed enc_step.
Proof.
  rewrite /enc_step. move=> k u /=. rewrite subst_apps /=.
  rewrite map_app map_rev map_subst_map_enc_instr /=.
  by autorewrite with subst.
Qed.

#[local] Hint Rewrite enc_step_closed : subst.

Opaque Nat.sub.

Lemma addr_spec_in_code {l instr r} :
  P = l ++ instr :: r ->
  addr (S (length l)) = S (length l).
Proof.
  rewrite /addr=> ->. rewrite length_app /=.
  by have ->: S (length l) - (length l + S (length r)) = 0 by lia.
Qed.

Lemma addr_spec_out_code {i} : i < 1 \/ S (length P) <= i -> addr i = 0.
Proof.
  rewrite /addr => - [?|?].
  - have ->: i = 0 by lia.
    by case: (length P).
  - by have ->: i - length P = S (i - length P - 1) by lia.
Qed.

Opaque addr.

Lemma map_nth' {X Y : Type} {f : X -> Y} {l i} {d} d' : i < length l -> nth i (map f l) d = f (nth i l d').
Proof.
  move=> H. rewrite (nth_indep _ _ (f d')); first by rewrite length_map.
  by apply: map_nth.
Qed.

Lemma enc_step_spec l instr r cs :
  P = l ++ instr :: r ->
  clos_refl_trans term step
    (apps enc_step [pi (addr (S (length l))); enc_regs cs])
    (app (enc_instr (S (length l), instr)) (enc_regs cs)).
Proof.
  move=> HP.
  apply: rt_trans.
  { rewrite /= /enc_step. apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { rewrite /= subst_apps /=. apply: rt_steps_app_r.
    autorewrite with subst.
    rewrite map_app map_rev map_subst_map_enc_instr /=.
    apply: eval_rt. apply: apps_pi_spec.
    - apply /Forall_app. split.
      + by apply /Forall_rev /Forall_map /Forall_forall=> *.
      + constructor; by autorewrite with subst.
    - apply /Forall_app. split.
      + apply /Forall_rev /Forall_map /Forall_forall=> * ??. by autorewrite with subst.
      + constructor; by autorewrite with subst.
    - rewrite length_app length_rev length_map length_combine length_seq /=. lia.
    - rewrite rev_app_distr rev_involutive (addr_spec_in_code HP) /=.
      rewrite (map_nth' (0, MM.mm_inc Fin.F1)).
      { rewrite length_combine length_seq HP length_app /=. lia. }
      rewrite combine_nth; first by rewrite length_seq.
      rewrite seq_nth.
      { rewrite HP length_app /=. lia. }
      have ->: nth (length l) P (INCₐ Fin.F1) = instr; last done.
      { by rewrite HP app_nth2 ?Nat.sub_diag. } }
  by apply: rt_refl.
Qed.

Lemma enc_step_0_spec :
  clos_refl_trans term step (app enc_step (pi 0)) enc_halt.
Proof.
  rewrite /enc_step.
  apply: rt_trans.
  { by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { rewrite /= subst_apps map_app map_rev map_subst_map_enc_instr /=.
    apply: eval_rt. apply: apps_pi_spec.
    - apply /Forall_app. split.
      + by apply /Forall_rev /Forall_map /Forall_forall=> *.
      + constructor; by autorewrite with subst.
    - apply /Forall_app. split.
      + apply /Forall_rev /Forall_map /Forall_forall=> * ??. by autorewrite with subst.
      + constructor; by autorewrite with subst.
    - rewrite length_app length_rev length_map length_combine length_seq /=. lia.
    - by rewrite rev_app_distr rev_involutive /=. }
  by apply: rt_refl.
Qed.

Opaque enc_step.

Lemma enc_run_closed : closed enc_run.
Proof.
  rewrite /enc_run. move=> k u /=. by autorewrite with subst.
Qed.

Lemma eval_enc_run : eval enc_run enc_run.
Proof.
  by constructor.
Qed.

#[local] Hint Rewrite enc_run_closed : subst.
#[local] Hint Resolve eval_enc_run : core.

Lemma enc_recurse_spec p :
  clos_refl_trans term step
    (apps enc_recurse [pi (addr (fst p)); enc_regs (snd p); enc_run])
    (apps enc_run [pi (addr (fst p)); enc_regs (snd p); enc_run]).
Proof.
  apply: rt_trans.
  { apply: rt_steps_app_r. apply: rt_steps_app_r. apply: rt_step. by apply: step_app'. }
  apply: rt_trans.
  { apply: rt_steps_app_r. apply: rt_step. rewrite /=. by apply: step_app'. }
  apply: rt_trans.
  { apply: rt_step. rewrite /=. by apply: step_app'. }
  rewrite /=. autorewrite with subst. by apply: rt_refl.
Qed.

Opaque enc_recurse.

#[local] Hint Rewrite subst_apps : subst.

Lemma t_steps_enc_run_enc_step i cs :
  clos_trans term step
    (apps enc_run [pi (addr i); enc_regs cs])
    (apps enc_step [pi (addr i); enc_regs cs; lam (lam (lam (apps (var 0) [var 2; var 1; var 0])))]).
Proof.
  apply: t_trans.
  { apply: t_steps_app_r. apply: t_step. apply: step_app'. by apply: eval_pi. }
  apply: clos_t_rt_t.
  { rewrite /=. apply: t_step. by apply: step_app'. }
  rewrite /=. apply: rt_refl'.
  by autorewrite with subst.
Qed.

Opaque enc_step enc_instr.

Lemma enc_run_spec (p q : mm_state N) : @sss_step _ _ (@mma_sss N) (1, P) p q ->
  clos_trans term step
    (apps enc_run [pi (addr (fst p)); enc_regs (snd p); enc_run])
    (apps enc_run [pi (addr (fst q)); enc_regs (snd q); enc_run]).
Proof.
  move=> [k [l [instr [r [cs]]]]].
  move=> [[??]] [?]. subst k p.
  move=> /mma_step_sim Hpq. apply: clos_t_rt_t.
  { rewrite /=. apply: t_steps_app_r. by apply: t_steps_enc_run_enc_step. }
  apply: rt_trans.
  { apply: rt_steps_app_r. apply: rt_steps_app_r. rewrite /=.
    apply: enc_step_spec. by eassumption. }
  apply: rt_trans.
  { apply: rt_steps_app_r. by eassumption. }
  by apply: enc_recurse_spec.
Qed.

Lemma enc_run_spec_out_code (p : mm_state N) : fst p < 1 \/ S (length P) <= fst p ->
  clos_refl_trans _ step (apps enc_run [pi (addr (fst p)); enc_regs (snd p); enc_run]) (enc_regs (snd p)).
Proof.
  move=> Hp. rewrite /enc_run.
  apply: rt_trans.
  { apply: rt_steps_app_r. apply: rt_steps_app_r. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { apply: rt_steps_app_r. rewrite /=. by apply: eval_rt_steps_subst. }
  apply: rt_trans.
  { apply: rt_steps_app_r. rewrite /=. autorewrite with subst.
    rewrite (addr_spec_out_code Hp). do 2 apply: rt_steps_app_r. by apply: enc_step_0_spec. }
  by apply: enc_halt_spec.
Qed.

Lemma closed_enc_run : closed enc_run.
Proof.
  move=> k u. rewrite /enc_run /=. by autorewrite with subst.
Qed.

Definition sync p t := t = apps enc_run [pi (addr (fst p)); enc_regs (snd p); enc_run].

Lemma sss_step_transport p q s :
  sss_step (@mma_sss N) (1, P) p q ->
  sync p s  ->
  exists t, clos_trans term step s t /\ sync q t.
Proof.
  move=> /enc_run_spec H ->.
  by exists (apps enc_run [pi (addr (fst q)); enc_regs (snd q); enc_run]).
Qed.

Lemma stuck_sss_step_transport p s : 
  stuck (sss_step (@mma_sss N) (1, P)) p ->
  sync p s -> terminates step s.
Proof.
  move=> /MMA_computable_to_MMA_mon_computable.out_code_iff Hp ->.
  exists (enc_regs (snd p)). split.
  - by apply: enc_run_spec_out_code.
  - move=> t. intros H. by inversion H.
Qed.

Lemma sss_step_dec p :
  (exists q, sss_step (@mma_sss N) (1, P) p q) \/ stuck (sss_step (@mma_sss N) (1, P)) p.
Proof.
  have [|] := subcode.in_out_code_dec (fst p) (1, P).
  - move=> /MMA_computable_to_MMA_mon_computable.in_code_step ?. by left.
  - move=> /MMA_computable_to_MMA_mon_computable.out_code_iff ?. by right.
Qed.

Opaque enc_run.

Lemma closed_apps_enc_run i cs : closed (apps enc_run [pi (addr i); enc_regs cs; enc_run]).
Proof.
  move=> k u. rewrite subst_apps /=. by autorewrite with subst.
Qed.

End MMA_HALTING_to_HaltLclosed.

Require Import Undecidability.Synthetic.Definitions.

(* Halting problem for weak call-by-value lambda-calculus *)
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.

Lemma MMA_HALTING_terminates_sss_step_iff n (P : list (mm_instr (Fin.t (S n)))) (v : Vector.t nat (S n)) :
  MMA_HALTING (P, v) <-> terminates (sss_step (@mma_sss (S n)) (1, P)) (1, v).
Proof.
  by apply: MMA_computable_to_MMA_mon_computable.sss_terminates_iff.
Qed.

(*
Lemma sss_terminates_iff {n s P} : sss_terminates (@mma_sss n) P s <-> terminates (sss_step (@mma_sss n) P) s.
Proof.
  split.
  - move=> [t] [/MMA_computable_to_MMA_mon_computable.sss_compute_iff ? /out_code_iff ?]. by exists t.
  - move=> [t] [/sss_compute_iff ? /out_code_iff ?]. by exists t.
Qed.
*)

Lemma closed_app s t : closed (app s t) -> closed s /\ closed t.
Proof.
  move=> H. split=> k u; by move: (H k u)=> [].
Qed.

Lemma closed_rt_step {s t} :
  clos_refl_trans term step s t ->
  closed s ->
  closed t.
Proof.
  elim; by eauto using L_facts.closed_step.
Qed.

Fixpoint term_size t : nat :=
  match t with
  | var _ => 1
  | app s t => 1 + term_size s + term_size t
  | lam s => 1 + term_size s
  end.

Lemma not_closed_var n : closed (var n) -> False.
Proof.
  move=> /(_ n (var (S n))) /=.
  rewrite Nat.eqb_refl=> - []. lia.
Qed.

Lemma closed_not_lambda_step s :
  closed s ->
  (not (L_facts.lambda s)) ->
  exists t, step s t.
Proof.
  elim /(Nat.measure_induction _ term_size) : s.
  move=> [n|{}s t|?].
  - by move=> ? /not_closed_var.
  - move=> IH /closed_app [].
    move: s t IH=> [?|??|?].
    + by move=> ?? /not_closed_var.
    + move=> t /[apply] IH _ _.
      case: IH.
      * rewrite /=. lia.
      * by case.
      * move=> *. eexists. apply: L_facts.stepAppL. by eassumption.
    + move=> [?|??|?].
      * by move=> ?? /not_closed_var.
      * move=> IH ? /IH {}IH _.
        case: IH.
        ** rewrite /=. lia.
        ** by case.
        ** move=> *. eexists. apply: L_facts.stepAppR. by eassumption.
      * move=> *. eexists. by constructor.
  - move=> _ _ H. exfalso. apply: H. by eexists.
Qed.

Lemma closed_stuck_lambda t :
  closed t ->
  stuck step t ->
  L_facts.lambda t.
Proof.
  move=> /closed_not_lambda_step.
  move: t=> [?|??|?].
  - case.
    + by case.
    + by move=> t ? /(_ t).
  - case.
    + by case.
    + by move=> t ? /(_ t).
  - move=> *. by eexists.
Qed.

Lemma steps_stuck_eval s t :
  closed s ->
  clos_refl_trans term step s t ->
  stuck step t ->
  eval s t.
Proof.
  move=> Hs Hst Ht. apply /L_facts.eval_iff. split.
  - by apply /star_rt_steps_iff.
  - apply: closed_stuck_lambda; last done.
    by apply: (closed_rt_step Hst).
Qed.

Lemma stuck_lam s : stuck step (lam s).
Proof.
  move=> t H. by inversion H.
Qed.

Lemma eval_steps_stuck s t : eval s t -> terminates L_facts.step s.
Proof.
  move=> /L_facts.eval_iff [?] [?] ?. subst.
  eexists. split.
  - apply /star_rt_steps_iff. by eassumption.
  - by apply: stuck_lam.
Qed.

Lemma reduction n : @MMA_HALTING (S n) ⪯ HaltLclosed.
Proof.
  unshelve eexists.
  - intros [P v]. exists (apps (enc_run P) [pi P (addr P 1); enc_regs v; enc_run P]).
    apply closed_apps_enc_run.
  - intros [P v]. split.
    + intros ?%MMA_HALTING_terminates_sss_step_iff.
      destruct (@terminates_transport _ _
        (sss_step (@mma_sss (S n)) (1, P))
        L_facts.step
        (sync P)
        (@sss_step_transport _ P)
        (@stuck_sss_step_transport _ P)
        (1, v)
        _
        eq_refl
        H) as [t [H1t H2t]].
      exists t. cbn. eapply steps_stuck_eval; [|assumption..].
      apply closed_apps_enc_run.
    + intros [t Ht%eval_steps_stuck]. cbn in Ht.
      apply MMA_HALTING_terminates_sss_step_iff.
      apply (@terminates_reflection _ _ 
        (sss_step (@mma_sss (S n)) (1, P))
        L_facts.step
        (sync P)
        L_facts.uniform_confluence
        (@sss_step_transport _ P)
        (@sss_step_dec _ P)
        (1, v)
        _
        eq_refl
        Ht).
Qed.

Print Assumptions reduction.

Fixpoint fin_seq n : list (Fin.t n) :=
  match n with
  | 0 => []
  | S n => Fin.F1 :: map Fin.FS (fin_seq n)
  end.

Lemma rt_steps_apps_r s ts t :
  clos_refl_trans _ step s t -> clos_refl_trans _ step (apps s ts) (apps t ts).
Proof.
  elim: ts s t; first done.
  move=> ?? IH ??? /=. apply: IH.
  by apply: rt_steps_app_r.
Qed.

Opaque Vector.to_list Fin.L.

Lemma combine_map_l {A B C} (f : A -> B) (l : list A) (r : list C) :
  combine (map f l) r = map (fun '(x, y) => (f x, y)) (combine l r).
Proof.
  elim: l r; first done.
  move=> > IH [|? r]; first done.
  move=> /=. by rewrite IH.
Qed.

(*
Fixpoint fin_add n : forall m, Fin.t m -> Fin.t (n + m) :=
  match n with
  | 0 => fun m x => x
  | S n => fun m x => Fin.FS (fin_add n m x)
  end.

Definition enc_set_state l k n : term :=
  apps (enc_regs (Vector.const 0 ((S l) + k + n)))
  (map (fun '(x, i) => app (enc_replace (Fin.L n (fin_add (S l) _ x))) (var i)) (combine (fin_seq k) (rev (seq 0 k)))).

Opaque enc_replace.

Lemma substs_enc_set_state_aux l k n (v : Vector.t nat k) :
  clos_refl_trans _ step
    (substs 0 (rev (map nat_enc (VectorDef.to_list v))) (enc_set_state l k n))
    (enc_regs (fold_left (fun w '(c, x) => Vector.replace w (Fin.L n (fin_add (S l) _ x)) c) (combine (Vector.to_list v) (fin_seq k)) (Vector.const 0 ((S l) + k + n)))).
Proof.
  rewrite /enc_set_state.
  move: (Vector.const 0 ((S l) + k + n))=> cs.
  rewrite substs_apps substs_closed; first by apply: enc_regs_closed.
  elim: v l cs.
  - move=> l cs /=. by apply: rt_refl.
  - move=> c {}k v IH l cs.
    have ->: rev (seq 0 (S k)) = k :: rev (seq 0 k).
    { have ->: S k = k + 1 by lia.
      by rewrite seq_app rev_app_distr. }
    apply: rt_trans.
    { rewrite /=. apply: rt_steps_apps_r. rewrite substs_closed; first by apply: enc_replace_closed.
      apply: eval_rt. apply: enc_replace_spec.
      rewrite -Vector.to_list_map -Vector.to_list_rev -Vector.to_list_nth_order.
      rewrite -Vector.map_rev nth_order_map. by apply: eval_nat_enc. }
    rewrite combine_map_l (map_map (fun '(x, y) => (Fin.FS x, y))).
    apply: rt_trans.
    { set cs' := (cs' in enc_regs cs').
      rewrite Vector.to_list_cons /=.
      have := IH (S l) cs'.
     apply: IH. }
      
       Search (VectorDef.nth_order).

       apply: nat_enc_spec. }
     rewrite map_cons.
     by done.

*)

(* apps (enc_regs (Vector.const 0 (1 + k + n))) (Vector.to_list (Vector.map (fun x => enc_replace (Fin.L n (Fin.FS x))) (rev_vec_seq k)))*)
Definition enc_set_state k n : term :=
  apps (enc_regs (Vector.const 0 (1 + k + n)))
  (map (fun '(x, i) => app (enc_replace (Fin.FS (Fin.L n x))) (var i)) (combine (fin_seq k) (rev (seq 0 k)))).

Opaque enc_replace Vector.to_list.

Lemma substs_enc_set_state_aux k n (v : Vector.t nat k) :
  clos_refl_trans _ step
    (substs 0 (rev (map nat_enc (VectorDef.to_list v))) (enc_set_state k n))
    (enc_regs (fold_left (fun w '(x, c) => Vector.replace w (Fin.FS (Fin.L n x)) c) (combine (fin_seq k) (Vector.to_list v)) (Vector.const 0 (1 + k + n)))).
Proof.
  rewrite /enc_set_state.
  move: (Vector.const 0 (1 + k + n))=> cs.
  rewrite substs_apps substs_closed; first by apply: enc_regs_closed.
    have ->: forall xs, map (substs 0 (rev (map nat_enc (VectorDef.to_list v))))
      (map (fun '(x, i) => app (enc_replace (Fin.L n (Fin.FS x))) (var i))
      (combine xs (rev (seq 0 k)))) = 
      map (fun '(x, c) => app (enc_replace (Fin.L n (Fin.FS x))) (nat_enc c))
      (combine xs (Vector.to_list v)).
  { elim: v; first by move=> ? [|??].
    move=> c k' v IH ? [|x xs]; first done.
    have ->: seq 0 (S k') = seq 0 (k' + 1).
    { congr seq. lia. }
    rewrite seq_app rev_app_distr Vector.to_list_cons /=. congr cons.
    - rewrite substs_closed; first by apply: enc_replace_closed.
      congr app. rewrite app_nth2 length_rev length_map Vector.length_to_list; first done.
      by rewrite Nat.sub_diag.
    - rewrite -IH. apply: map_ext_in=> s /in_map_iff [[y j]] [<-].
      move=> /(@in_combine_r (Fin.t _) nat) /in_rev.
      rewrite rev_involutive=> /in_seq ? /=.
      rewrite !substs_closed; [by apply: enc_replace_closed..|].
      congr app. rewrite app_nth1; last done.
      rewrite length_rev length_map Vector.length_to_list. lia. }
  
  move: (fin_seq k)=> xs.
  move: (Vector.to_list v)=> c's.
  elim: xs c's cs {v}.
  - move=> *. by apply: rt_refl.
  - move=> x xs IH [|c' c's].
    + move=> *. by apply: rt_refl.
    + move=> cs /=. apply: rt_trans.
      { apply: rt_steps_apps_r. apply: eval_rt. apply: enc_replace_spec. by apply: eval_nat_enc. }
      by apply: IH.
Qed.

Print Assumptions substs_enc_set_state_aux.

Lemma vec_eq_nth {A : Type} (n : nat) (v1 v2 : VectorDef.t A n) :
  (forall p : Fin.t n, Vector.nth v1 p = Vector.nth v2 p) <-> v1 = v2.
Proof.
  split.
  - move=> ?. apply /Vector.eq_nth_iff. by move=> i ? <-.
  - move=> /Vector.eq_nth_iff H *. by apply: H.
Qed.

Lemma substs_enc_set_state k n v :
  clos_refl_trans _ step
    (substs 0 (rev (map nat_enc (VectorDef.to_list v))) (enc_set_state k n))
    (enc_regs (Vector.append (Vector.cons nat 0 k v) (Vector.const 0 n))) .
Proof.
  have := substs_enc_set_state_aux k n v.
  congr clos_refl_trans. congr enc_regs.
  rewrite [RHS](@Vector.eta _ (k + n)).
  rewrite [LHS](@Vector.eta _ (k + n)).
  congr (@Vector.cons _ _ (k + n)); rewrite /=.
  - elim: (fin_seq k) (Vector.to_list v) (Vector.const 0 (k + n)); first done.
    move=> ?? IH [|??] ? /=; first done.
    by apply: IH.
  - apply /(vec_eq_nth (k + n))=> x.
    pattern x. apply: Fin.case_L_R'=> {}x.
    + rewrite Vector.nth_append_L.
      have : forall x c, In (x, c) (combine (fin_seq k) (Vector.to_list v)) -> Vector.nth v x = c.
      { elim: v; first done.
        move=> > IH {}x c /=. rewrite Vector.to_list_cons /=.
        move=> [[??]|]; first by subst.
        rewrite combine_map_l.
        move=> /in_map_iff [[??]] [[??]] /IH ?.
        by subst. }
      have : In (x, Vector.nth v x) (combine (fin_seq k) (Vector.to_list v)).
      { elim: v x; first by apply: Fin.case0.
        move=> > IH x.
        pattern x. apply: Fin.caseS'; first by left.
        move=> {}x. rewrite Vector.to_list_cons /=. right.
        rewrite combine_map_l. apply /in_map_iff. by eexists (_, _). }
      rewrite -Vector.append_const.
      move: (VectorDef.const 0 k).
      elim /rev_ind: (combine (fin_seq k) (Vector.to_list v)); first done.
      move=> [y j] ? IH ? /in_app_iff [/IH {}IH|].
      * move=> H. rewrite fold_left_app /=.
        rewrite [fold_left _ _ _](@Vector.eta _ (k + n)) /=.
        have [?|?] := Fin.eq_dec x y.
        { subst. rewrite Vector.nth_replace_eq.
          rewrite (H y j); last done.
          apply /in_app_iff. right. by left. }
        rewrite Vector.nth_replace_neq; first by move=> /Fin.L_inj.
        apply: IH=> *. apply: H. apply /in_app_iff. by left.
      * move=> /= [|]; last done.
        move=> [??] H. subst. rewrite fold_left_app /=.
        rewrite [fold_left _ _ _](@Vector.eta _ (k + n)) /=.
        by rewrite Vector.nth_replace_eq.
    + rewrite Vector.nth_append_R Vector.const_nth -Vector.append_const.
      elim: (fin_seq k) (Vector.to_list v) (VectorDef.const 0 k).
      * move=> /= *. by rewrite Vector.nth_append_R Vector.const_nth.
      * move=> ?? IH [|??] ? /=; first by rewrite Vector.nth_append_R Vector.const_nth.
        by rewrite Vector.replace_append_L IH.
Qed.

Lemma subst_enc_set_state k n m u : subst (enc_set_state k n) (k + m) u = enc_set_state k n.
Proof.
  rewrite /enc_set_state subst_apps enc_regs_closed.
  congr fold_left. rewrite map_map.
  apply: map_ext_in=> - [x i].
  rewrite /= enc_replace_closed.
  move=> /(@in_combine_r (Fin.t k) nat) /in_rev.
  rewrite rev_involutive.
  move=> /in_seq ?.
  by have /Nat.eqb_neq -> : i <> k + m by lia.
Qed.

Opaque enc_run pi enc_set_state enc_nth.

Lemma enc_init_spec {k n} (P : list (mm_instr (Fin.t (1 + k + n)))) (v : Vector.t nat k) :
  clos_refl_trans _ step
    (Vector.fold_left (fun (s : term) c => app s (nat_enc c))
      (lams k (apps (enc_run P) [pi P (addr P 1); enc_set_state k n; enc_run P; enc_nth (@Fin.F1 (k + n))])) v)
    (apps (enc_run P) [pi P (addr P 1); enc_regs (Vector.append (Vector.cons nat 0 k v) (Vector.const 0 n)); enc_run P; enc_nth (@Fin.F1 (k + n))]).
Proof.
  rewrite Vector.to_list_fold_left.
  have ->: forall cs t, fold_left (fun s c => app s (nat_enc c)) cs t = apps t (map nat_enc cs).
  { elim; first done.
    move=> > IH ? /=. by rewrite IH. }
  apply: rt_trans.
  { apply /star_rt_steps_iff. apply: steps_apps_lams'.
    - by rewrite length_map Vector.length_to_list.
    - apply /Forall_map /Forall_forall=> *. by apply: eval_nat_enc.
    - apply /Forall_map /Forall_forall=> *. by apply: nat_enc_closed. }
  rewrite substs_apps /=.
  apply: rt_trans.
  { do 2 apply: rt_steps_app_r. apply: rt_steps_app_l.
    by apply: substs_enc_set_state. }
  rewrite !substs_closed; [by auto using enc_run_closed, pi_addr_closed, enc_nth_closed..|].
  by apply: rt_refl.
Qed.

(* TODO use comb_proc_red *)

Lemma eval_rt_steps_eval s t u : eval s t -> clos_refl_trans _ step s u -> eval u t.
Proof.
  move=> /L_facts.eval_iff [+] [s'] ?. subst.
  move=> + /star_rt_steps_iff.
  move=> /L_facts.confluence /[apply] - [?] [H1 H2].
  apply /L_facts.eval_iff.
  have Hs' : L_facts.lambda (lam s') by eexists.
  split.
  - have := L_facts.lam_terminal Hs'.
    move: H1 H2 => []; first done.
    by move=> > + _ _ H => /H.
  - by eexists.
Qed.

Lemma clos_trans_flip {X : Type} {R : X -> X -> Prop} {x y} : clos_trans _ R x y ->
  clos_trans _ (fun y x => R x y) y x.
Proof. by elim; eauto using clos_trans. Qed.

Lemma nat_enc_inj n m : nat_enc n = nat_enc m -> n = m.
Proof.
  elim: n m.
  - by case.
  - move=> n IH [|m] /=; first done.
    by move=> [/IH] <-.
Qed.

Theorem MMA_computable_to_L_computable_closed {k} (R : Vector.t nat k -> nat -> Prop) :
  MMA_computable R -> L_computable_closed R.
Proof.
  unfold MMA_computable, L_computable_closed.
  move=> [n [P HP]].
  (* \c1...\ck. run pi_1 ((0...0) (set 1 c1) .. (set k ck)) run (\c'1...\c'n.c'1) *)
  exists (lams k (apps (enc_run P) [pi P (addr P 1); enc_set_state k n; enc_run P; enc_nth (@Fin.F1 (k + n))])).
  split.
  - intros u ?.
    rewrite subst_lams subst_apps !map_cons subst_enc_set_state.
    by rewrite !closed_enc_run pi_addr_closed enc_nth_closed.
  - move=> v. split.
    + move=> m. rewrite HP. split.
      * intros [c [v' [H1 H2]]].
        apply /L_facts.eval_iff. split; last by (case: (m); eexists).
        apply /star_rt_steps_iff. apply: rt_trans.
        { by apply: enc_init_spec. }
        move=> /MMA_computable_to_MMA_mon_computable.sss_compute_iff in H1.
        have := @clos_refl_trans_transport _ _
        (sss_step (@mma_sss ((1 + k + n))) (1, P))
        L_facts.step
        (sync P)
        (@sss_step_transport _ P)
        (1, Vector.append (Vector.cons nat 0 k v) (Vector.const 0 n))
        _
        (c, Vector.cons nat m (k + n) v')
        eq_refl
        H1.
        move=> [t [-> Ht]].
        apply: rt_trans.
        { apply: rt_steps_app_r. by eassumption. }
        apply: rt_trans.
        { apply: rt_steps_app_r. by apply: enc_run_spec_out_code. }
        apply: eval_rt. by apply: enc_nth_spec.
      * move=> /eval_rt_steps_eval => /(_ _ (enc_init_spec _ _)).
        move: (Vector.append _ _)=> {}v /[dup] /eval_steps_stuck H'.
        have /(@Acc_clos_trans term) := @terminating_Acc _ _ L_facts.uniform_confluence _ H'.
        have [i Hi] : exists i, 1 = i by eexists.
        rewrite [in addr P 1]Hi [in (1, v)]Hi.
        move E: (apps _ _) => t H.
        elim: H i v E {H' Hi}.
        move=> {}t IH1 IH2 i v ?. subst t.
        have [[[j w]]|] := @sss_step_dec (k + n) P (i, v).
        ** move=> /[dup] Hvw /enc_run_spec /=.
           move=> /(@t_steps_app_r _ _ (enc_nth (@Fin.F1 (k + n)))).
           move=> /[dup] /(@clos_trans_clos_refl_trans term) /eval_rt_steps_eval H' + /H'.
           move=> /clos_trans_flip /IH2 /(_ _ _ eq_refl) /[apply].
           move=> [c] [v'] [??]. exists c, v'. split; last done.
           apply: sss_compute_trans; last by eassumption.
           apply /MMA_computable_to_MMA_mon_computable.sss_compute_iff.
           by apply: rt_step.
        ** move=> /[dup] /MMA_computable_to_MMA_mon_computable.out_code_iff /enc_run_spec_out_code H.
           move=> /[dup] /MMA_computable_to_MMA_mon_computable.out_code_iff H''.
           move=> /stuck_sss_step_transport => /(_ _ eq_refl) [t] H'.
           move: H=> /(rt_steps_app_r _ _ (enc_nth (@Fin.F1 (k + n)))).
           move=> /eval_rt_steps_eval /[apply].
           have /L_facts.eval_iff [+ [??]] := enc_nth_spec (@Fin.F1 (k + n)) v.
           move=> /star_rt_steps_iff /eval_rt_steps_eval /[apply].
           have := eval_nat_enc (Vector.nth v Fin.F1).
           move=> /L_facts.eval_iff /L_facts.eval_unique + /L_facts.eval_iff => /[apply].
           move=> /nat_enc_inj <-.
           exists i, (snd (@Vector.splitat _ 1 (k + n) v)).
           split; last done.
           apply /MMA_computable_to_MMA_mon_computable.sss_compute_iff.
           apply: rt_refl'. congr pair.
           rewrite [LHS](@MMA_computable_to_MMA_mon_computable.Facts.vec_append_splitat _ 1 (k + n)).
           by rewrite (Vector.eta v).
    + move=> o /eval_rt_steps_eval => /(_ _ (enc_init_spec _ _)).
      move: (Vector.append _ _)=> {}v /[dup] /eval_steps_stuck H'.
      have /(@Acc_clos_trans term) := @terminating_Acc _ _ L_facts.uniform_confluence _ H'.
      move: (1) => i.
      move E: (apps _ _) => t H.
      elim: H i v E {H'}.
      move=> {}t IH1 IH2 i v ?. subst t.
      have [[[j w]]|] := @sss_step_dec (k + n) P (i, v).
      * move=> /enc_run_spec /=.
        move=> /(@t_steps_app_r _ _ (enc_nth (@Fin.F1 (k + n)))).
        move=> /[dup] /(@clos_trans_clos_refl_trans term) /eval_rt_steps_eval H' + /H'.
        by move=> /clos_trans_flip /IH2 /(_ _ _ eq_refl) /[apply].
      * move=> /[dup] /MMA_computable_to_MMA_mon_computable.out_code_iff /enc_run_spec_out_code H.
        move=> /stuck_sss_step_transport => /(_ _ eq_refl) [t] H'.
        move: H=> /(rt_steps_app_r _ _ (enc_nth (@Fin.F1 (k + n)))).
        move=> /eval_rt_steps_eval /[apply].
        have /L_facts.eval_iff [+ [??]] := enc_nth_spec (@Fin.F1 (k + n)) v.
        move=> /star_rt_steps_iff /eval_rt_steps_eval /[apply].
        have := eval_nat_enc (Vector.nth v Fin.F1).
        move=> /L_facts.eval_iff /L_facts.eval_unique + /L_facts.eval_iff => /[apply] <-.
        by eexists.
Qed.

Print Assumptions MMA_computable_to_L_computable_closed.
