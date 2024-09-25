Require Import List PeanoNat Lia.
Import ListNotations.

From Undecidability Require Import MinskyMachines.MMA L.L Shared.Libs.DLW.Code.sss.
From Undecidability Require MinskyMachines.MM.
Import MM (mm_instr).

Require Import ssreflect.

Unset Implicit Arguments.

(*
#[local] Notation "i // s -1> t" := (one_step (@mma_sss _) i s t) (at level 70, no associativity).
*)

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

Lemma apps_pi_spec i ts t : length ts = S (length P) -> eval (nth i ts (var 0)) t -> eval (apps (pi i) ts) t.
Proof.
(*
  elim: ts i t.
  - by move=> [|?]? /= /not_eval_var_l.
  - move=> t' ts IH [|i] t /= H.
    + 
*)
Admitted.

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

Require Undecidability.L.Util.L_facts.
Import L_facts (step).

Require Undecidability.L.Prelim.ARS.

(*
Lemma substs_lam s k t : subst ts (lam s) = lam (subst s (S k) t).
Proof.
  done.
Qed.
*)

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

Lemma eval_apps_lams' n (ts : list term) s t :
  n = length ts ->
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  eval (substs 0 (rev ts) s) t ->
  eval (apps (lams n s) ts) t.
Proof.
  move=> ->. by apply: eval_apps_lams.
Qed.

Print Assumptions eval_apps_lams'.

Lemma pi_succ_spec i : eval (app pi_succ (pi (addr i))) (pi (addr (S i))).
Proof.
  econstructor; [constructor|apply: eval_pi|].
  rewrite subst_apps /= map_map.
  rewrite /pi /addr. move: (length P) => length.
  have [H|[H|H]]: S i <= length \/ i = length \/ S i > length by lia.
  - have ->: i - length = 0 by lia.
    have ->: S i - length = 0 by lia.
Admitted.

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

Lemma nth_of_list {X : Type} (d : X) (l : list X) i :
  Vector.nth (Vector.of_list l) i = nth (proj1_sig (Fin.to_nat i)) l d.
Proof.
Admitted.


Lemma vec_nth_rev_seq_list k n i :
  Vector.nth (Vector.of_list (rev (seq k n))) i = k + n - 1 - proj1_sig (Fin.to_nat i).
Proof.
  rewrite (nth_of_list 0).
  case: (Fin.to_nat i) => [m Hm] /=.
  rewrite length_rev in Hm.
  rewrite rev_nth; first done.
  rewrite length_seq in Hm.
  rewrite seq_nth length_seq; lia.
Qed.

(*
Lemma vec_nth_rev_seq k n i :
  Vector.nth (Vector.rev (vec_seq k n)) i = k + n - 1 - proj1_sig (Fin.to_nat i).
Proof.
  elim: n k i.
  - move=> ?. by apply: Fin.case0.
  - move=> n IH k /=.
Admitted.
*)
(*

  Vector.to_list_rev:
forall (A : Type) (n : nat) (v : VectorDef.t A n),
VectorDef.to_list (VectorDef.rev v) = rev (VectorDef.to_list v)


  Search Vector.to_list.
   Search Vector.rev.
    change (S n) with (1 + n).
    move=> i.
    rewrite Vector.rev_cons.
    pattern i.
    apply: (Fin.case_L_R' _ i).
    
     rewrite Vector.shiftin_nth. Search Vector.nth. Vector.nth_shiftin.
    rewrite /vec_seq.
    pattern i. apply: (Fin.caseS' i).
    + 
     first done.
  Search Vector.nth.
  Search (nth _ (rev _)).
  Search (Vector.nth (Vector.rev _)).
Admitted.
*)

Opaque vec_seq.

Definition enum_regs : Vector.t term N := Vector.map var (Vector.rev (vec_seq 0 N)).

Lemma eval_enc_regs ts : eval (enc_regs ts) (enc_regs ts).
Proof.
  by constructor.
Qed.

(* get nth vector element *)
Definition enc_nth (x : Fin.t N) : term :=
  (* \c1 .. cN.cx *)
  lams N (var (N - 1 - proj1_sig (Fin.to_nat x))).

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

Lemma eval_nat_enc n : eval (nat_enc n) (nat_enc n).
Proof.
  by case: n; constructor.
Qed.

Lemma nth_order_map : forall (X Y : Type) (f : X -> Y) (n : nat) (v : Vector.t X n) (i : nat) (H : i < n),
  Vector.nth_order (Vector.map f v) H = f (Vector.nth_order v H).
Proof.
  move=> X Y f n. elim; first by lia.
  move=> x {}n v IH [|i] H /=; first done.
  by apply: IH.
Qed.

Lemma nth_order_vec_pos {X : Type} {n} {v : Vector.t X n} {i j} (H : i < n) (H' : j < n) :
  i = j -> Vector.nth_order v H = vec.vec_pos v (Fin.of_nat_lt H').
Proof.
Admitted.

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
(*
Lemma nth_order_nth {X : Type} {n} {v : Vector.t X n} {i j} (H : i < n) (H' : j < n) :
  i = j -> Vector.nth_order v H = Vector.nth v (Fin.of_nat_lt H').
Proof.
Admitted.
*)

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

Check vec.vec_change.

(* set nth vector element *)
Definition enc_replace (x : Fin.t N) : term :=
  (* \c.\c1 .. cN.\f.f c1 .. c .. cN *)
  lam (lams N (lam (apps (var 0) (map var (Vector.to_list (Vector.replace (Vector.map S (rev_vec_seq N)) x (N + 1))))))).

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

Lemma eval_lam' s t : lam s = t -> eval (lam s) t.
Proof.
  move=> <-. by constructor.
Qed.


Lemma vec_change_replace {X : Type} {n} (v : Vector.t X n) i x :
  vec.vec_change v i x = Vector.replace v i x.
Proof.
Admitted.

Opaque vec_seq.
Opaque Nat.sub.

Lemma vec_nth_rev_seq n i : VectorDef.nth (rev_vec_seq n) i = n - 1 - proj1_sig (Fin.to_nat i).
Proof.
  elim: n i.
  - by apply: Fin.case0.
  - move=> n IH i.
    pattern i. apply: (Fin.caseS' i).
    + move=> /=. lia.
    + move=> {}i /=. rewrite IH.
      move: (Fin.to_nat i) => [m Hm] /=. lia.
Qed.

Opaque rev_vec_seq.

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

Print Assumptions enc_replace_spec.

Definition enc_inc (x : Fin.t N) : term :=
  (* \cs. cs ((replace x) (nat_succ (cs (nth x)))) *)
  lam (app (var 0) (app (enc_replace x) (app nat_succ (app (var 0) (enc_nth x))))).

Lemma subst_ren n t k s : closed s -> subst (ren (fun x => n + x) t) (n + k) s = ren (fun x => n + x) (subst t k s).
Proof.
Admitted.

Lemma subst_var_eq x s : subst (var x) x s = s.
Proof.
  by rewrite /= Nat.eqb_refl.
Qed.

Lemma subst_var_neq x y s : x <> y -> subst (var x) y s = var x.
Proof.
  by move=> /= /Nat.eqb_neq ->.
Qed.

Lemma enc_replace_closed x : closed (enc_replace x).
Proof.
Admitted.

Lemma nat_succ_closed : closed nat_succ.
Proof.
Admitted.

Lemma nat_succ_spec t c : eval t (nat_enc c) -> eval (app nat_succ t) (nat_enc (S c)).
Proof.
Admitted.

Lemma enc_nth_closed x : closed (enc_nth x).
Proof.
Admitted.

Opaque enc_regs enc_replace nat_succ enc_nth.

Lemma enc_inc_spec (x : Fin.t N) (v : Vector.t nat N) :
  eval (app (enc_inc x) (enc_regs v)) (enc_regs (Vector.replace v x (S (Vector.nth v x)))).
Proof.
  rewrite /enc_inc. econstructor; [constructor|apply: eval_enc_regs|].
  rewrite /= enc_replace_closed nat_succ_closed enc_nth_closed.
  apply: enc_replace_spec. apply: nat_succ_spec.
  by apply: enc_nth_spec.
Qed.

Lemma enc_inc_closed x : closed (enc_inc x).
Proof.
Admitted.

Opaque enc_inc.

Definition enc_instr '(i, instr) : term :=
  match instr with
  | MM.mm_inc x =>
      (* \cs.(\cs'.\f.f (pi (S i)) cs') (inc x cs) *)
      lam (app (lam (lam (apps (var 0) [pi (addr (S i)); var 1]))) (app (enc_inc x) (var 0)))
  | MM.mm_dec x j =>
      (* \cs.cs (\c1..cN.cx (\f. f (pi (S i)) cs) (\c.\f. f (pi j) (replace x cs c))) *)
  
  var 0
  end.

Definition enc_state (p : mm_state N) : term :=
  lam (apps (var 0) [pi (addr (fst p)); (enc_regs (snd p))]).

Lemma eval_enc_state p : eval (enc_state p) (enc_state p).
Proof.
  constructor.
Qed.

Lemma subst_enc_pair t1 t2 k s : subst (enc_pair t1 t2) k s = enc_pair (subst t1 (S k) s) (subst t2 (S k) s).
Proof.
  done.
Qed.

Lemma closed_pi i : closed (pi (addr i)).
Proof.
Admitted.

(*
Lemma eval_apps_lams {n : nat} (ts : Vector.t term n) s t u :
  eval (snd (Vector.fold_right (fun s' '(n, t') => (S n, subst t' n s')) ts (0, s))) t ->
  eval u (lams n s) ->
  eval (apps u (VectorDef.to_list ts)) t.
Proof.
  elim: ts s t u.
  - admit. (* eval_trans *)
  - move=> t' {}n ts IH s t u.
    rewrite Vector.to_list_cons /=.
    move=> H Hu. apply: IH; first last.
    + econstructor; [eassumption|..].
  simpl.
  rewrite -/Vector.fold_right.
  cbn.
Admitted.
*)

(*
Lemma eval_apps_lams {n : nat} (ts : Vector.t term n) s t :
  eval (snd (Vector.fold_right (fun s' '(n, t') => (S n, subst t' n s')) ts (0, s))) t ->
  eval (apps (lams n s) (VectorDef.to_list ts)) t.
Proof.
  elim: ts s t; first done.
  move=> t' {}n ts IH s t.
  rewrite Vector.to_list_cons /=.
  simpl.
  rewrite -/Vector.fold_right.
  cbn.
Admitted.
*)

Lemma eval_enc_pair t1 t2 : eval (enc_pair t1 t2) (enc_pair t1 t2).
Proof.
  constructor.
Qed.

Lemma vec_fold_right_map {X Y Z : Type} (f : Y -> Z -> Z) (g : X -> Y) {n : nat} (v : Vector.t X n) (z : Z) :
  Vector.fold_right f (Vector.map g v) z = Vector.fold_right (fun x z => f (g x) z) v z.
Proof.
Admitted.


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

Lemma pi_addr_closed i : closed (pi (addr i)).
Proof.
  apply: pi_closed.
  rewrite /addr.
  case E: (i - length P) => [|?]; lia.
Qed.

Opaque enc_pair pi_succ pi enc_regs.

Axiom FF : False.

Lemma vec_pos_nth {X : Type} {n} {v : Vector.t X n} {i} :
  vec.vec_pos v i = Vector.nth v i.
Proof.
Admitted.

Lemma mma_step_sim (instr : mm_instr (Fin.t N)) (p q : mm_state N) :
  mma_sss instr p q -> eval (app (enc_instr (fst p, instr)) (enc_regs (snd p))) (enc_state q).
Proof.
  case.
  - (* INC *)
    move=> i x v /=.
    econstructor; [by constructor|by apply: eval_enc_regs|].
    rewrite /= pi_addr_closed enc_inc_closed.
    econstructor; [by constructor|by apply: enc_inc_spec|].
    rewrite /= pi_addr_closed vec_pos_nth vec_change_replace.
    by constructor.
  - (* DEC *)
    destruct FF.
  - (* JUMP *)
    destruct FF.
Qed.

(* \cs.\f.\run.cs *)
Definition enc_halt := lam (lam (lam (var 2))).
(* \i.\cs.i (halt :: P) cs *)
Definition enc_step := lam (lam (apps (var 1) (enc_halt :: map enc_instr (combine (seq 1 (length P)) P) ++ [var 0]))).
(* \(i, cs).(i, cs) (\i.\cs.step i cs) (\i'.\cs'.\run.run i' cs' run) *)
Definition enc_run := lam (apps (var 0) [lam (lam (apps enc_step [var 1; var 0]));
  lam (lam (lam (apps (var 0) [var 2; var 1; var 0])))]).

Lemma enc_run_spec (p q : mm_state N) : @sss_step _ _ (@mma_sss N) (1, P) p q ->
  ARS.star L_facts.step (apps enc_run [enc_state p; enc_run]) (apps enc_run [enc_state q; enc_run]).
Proof.
  move=> [k [l [instr [r [cs]]]]].
  move=> [[??]] [?]. subst k p.
  Check sss_step.
Admitted.

Lemma enc_halt_spec (p : mm_state N) : fst p < 1 \/ S (length P) <= fst p ->
  ARS.star L_facts.step (apps enc_run [enc_state p; enc_run]) (nat_enc (Vector.hd (snd p))).
Proof.
Admitted.

Lemma enc_run_spec' {i v t} : eval (app (app enc_run (enc_state (i, v))) enc_run) t ->
  exists cs, t = enc_regs cs.
Proof.
Admitted.

Lemma closed_enc_run : closed enc_run.
Proof.
Admitted.

Lemma closed_enc_state p : closed (enc_state p).
Proof.
Admitted.

Lemma transport p q : sss_output (@mma_sss N) (1, P) p q ->
  eval (app (app enc_run (enc_state p)) enc_run) (enc_regs (snd q)).
Proof.
Admitted.

Lemma reflection p cs : eval (app (app enc_run (enc_state p)) enc_run) (enc_regs cs) ->
  exists k, sss_steps (@mma_sss N) (1, P) k p (0, cs).
Proof.
Admitted.

End MMA_HALTING_to_HaltLclosed.

Opaque enc_run enc_state.

Require Import Undecidability.Synthetic.Definitions.

(* Halting problem for weak call-by-value lambda-calculus *)
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.

Lemma reduction n : @MMA_HALTING (S n) ⪯ HaltLclosed.
Proof.
  unshelve eexists.
  - intros [P v]. exists (apps (enc_run P) [enc_state P (1, v); enc_run P]).
    intros u k. cbn. by rewrite !closed_enc_run closed_enc_state.
  - intros [P v]. split.
    + intros [q Hq]. exists (enc_regs (snd q)). cbn in *.
      now apply transport. (* simulation *)
    + intros [t Ht]. cbn in Ht.
      assert (H't := enc_run_spec' Ht). destruct H't as [cs ?]. subst.
      exists (0, cs). split.
      * now apply reflection. (* inverse simulation *)
      * cbn. lia.
Qed.

Print Assumptions reduction.

Theorem MMA_computable_to_L_computable_closed {k} (R : Vector.t nat k -> nat -> Prop) :
  MMA_computable R -> L_computable_closed R.
Proof.
  unfold MMA_computable, L_computable_closed.
  move=> [n [P HP]].
  (* \c1...\cn. run (\f.f pi_1 (\g.g 0 c1 .. ck 0 .. 0)) run (\c'1...\c'n.c'1)) *)
  pose t_state := lam (apps (var 0) [pi P (addr P 1);
    lam (apps (var 0) ([nat_enc 0] ++ map var (rev (seq 1 k)) ++ (repeat (nat_enc 0) n)))]).
  exists (lams (1 + k + n) (apps (enc_run P) [t_state; enc_run P; lams (1 + k + n) (var (k + n))])).
  assert (H_t_state : closed t_state).
  { admit. }
  split.
  - intros u ?.
    rewrite subst_lams subst_apps !map_cons !closed_enc_run subst_lams H_t_state.
    now rewrite subst_var_neq; [lia|].
  - move=> v. split.
    + move=> m. rewrite HP. split.
      * intros [c [v' [H1 H2]]]. admit. (* forwards simulation *)
      * admit. (* backwards simulation *)
Admitted.
