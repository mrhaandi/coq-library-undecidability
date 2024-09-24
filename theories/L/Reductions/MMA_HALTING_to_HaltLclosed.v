Require Import List PeanoNat Lia.
Import ListNotations.

From Undecidability Require Import MinskyMachines.MMA L.L Shared.Libs.DLW.Code.sss.
From Undecidability Require MinskyMachines.MM.
Import MM (mm_instr).

Require Import ssreflect.

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

Fixpoint substs ts t :=
  match t with
  | var x => nth x ts (var x)
  | app s t => app (substs ts s) (substs ts t)
  | lam s => lam (substs (var 0 :: ts) s)
  end.

Fixpoint reds s ts :=
  match ts with
  | [] => s
  | t :: ts =>
    match s with
    | var x => s
    | app s1 s2 => s
    | lam s => reds (subst s 0 t) ts
    end
  end.

Lemma substs_nil t : substs [] t = t.
Proof.
Admitted.

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

(*
Lemma subst_substs ts s t k : L_facts.bound k s ->
  subst (substs ts s) k t = substs (fold_left (fun t's t => ) ts []) map (fun u => subst u k t) (combine (seq 0 ts) s.
Proof.
  move=> H. elim: H t ts.
  - move=> {}k n ? t ts /=.
    have E: var n = (fun u => subst u k t) (var n).
    { rewrite /=. admit. }
    by rewrite E map_nth -E.
  - move=> {}k s1 s2 ? IH1 ? IH2 t ts /=.
    by rewrite IH1 IH2.
  - move=> {}k {}s ? IH t ts /=.
    rewrite IH /=.
    Search (nth _ (map _ _)).
*)
(*
Lemma subst_substs ts s t k : L_facts.bound k s ->
  subst (substs ts s) k t = substs (fold_left (fun t's t => ) ts []) map (fun u => subst u k t) (combine (seq 0 ts) s.
Proof.
  move=> H. elim: H t ts.
  - move=> {}k n ? t ts /=.
    have E: var n = (fun u => subst u k t) (var n).
    { rewrite /=. admit. }
    by rewrite E map_nth -E.
  - move=> {}k s1 s2 ? IH1 ? IH2 t ts /=.
    by rewrite IH1 IH2.
  - move=> {}k {}s ? IH t ts /=.
    rewrite IH /=.
    Search (nth _ (map _ _)).

Lemma subst_substs ts s t k : L_facts.bound k s ->
  subst (substs ts s) k t = substs (map (fun u => subst u k t) (combine (seq 0 ts) s.
Proof.
  move=> H. elim: H t ts.
  - move=> {}k n ? t ts /=.
    have E: var n = (fun u => subst u k t) (var n).
    { rewrite /=. admit. }
    by rewrite E map_nth -E.
  - move=> {}k s1 s2 ? IH1 ? IH2 t ts /=.
    by rewrite IH1 IH2.
  - move=> {}k {}s ? IH t ts /=.
    rewrite IH /=.
    Search (nth _ (map _ _)).
*)

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

Lemma steps_apps_lams (ts : list term) s :
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  ARS.star step (apps (lams (length ts) s) ts) (reds (lams (length ts) s) ts).
Proof.
  move=> H. elim: H s.
  - move=> ? /= *. by apply ARS.starR.
  - move=> t' {}ts H1t' Hts IH s /Forall_cons_iff [H2t'] /[dup] ? /IH {}IH.
    rewrite /= subst_lams Nat.add_0_r.
    apply: ARS.star_trans; [|by apply: IH].
    apply: steps_apps_l.
    move: H1t' => /L_facts.eval_iff [_] [t'' ?]. subst.
    apply: ARS.starC.
    + by apply: L_facts.stepApp.
    + rewrite subst_lams Nat.add_0_r.
      by apply: ARS.starR.
Qed.

Print Assumptions steps_apps_lams.

Lemma eval_apps_lams (ts : list term) s t :
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  eval (substs (rev ts) s) t ->
  eval (apps (lams (length ts) s) ts) t.
Proof.
  elim: ts s t.
  - move=> ??. by rewrite /= substs_nil.
  - move=> t' ts IH s t /Forall_cons_iff [H1t'] /IH {}IH.
    move=> /Forall_cons_iff [H2t'] /IH {}IH /=.
Admitted.
(*
    rewrite /=.
    have : eval (app (lam (lams (length ts) s)) t')
    rewrite !rev_app_distr /= !fold_left_app /=.

  elim /rev_ind: ts s t.
  - move=> ??. by rewrite /= substs_nil.
  - move=> t' ts IH s t /Forall_app [/IH {}IH] /Forall_cons_iff [H1t' _].
    move=> /Forall_app [/IH {}IH] /Forall_cons_iff [H2t' _].
    rewrite !rev_app_distr /= !fold_left_app /=.
*)

(*
Lemma eval_apps_lams (ts : list term) s t :
  Forall (fun t' => eval t' t') ts ->
  eval (snd (fold_right (fun t' '(n, s') => (S n, subst s' n t')) (0, s) ts)) t ->
  eval (apps (lams (length ts) s) ts) t.
Proof.
  elim /rev_ind: ts s t; first done.
  move=> t' ts IH s t /Forall_app [/IH {}IH] /Forall_cons_iff [Ht' _].
  rewrite !fold_left_app /=.
  move=> H.
  econstructor; [|eassumption|].
  - rewrite length_app /= Nat.iter_add.
    apply IH. admit.
Admitted.
*)

Lemma eval_apps_lams' n (ts : list term) s t :
  n = length ts ->
  Forall (fun t' => eval t' t') ts ->
  Forall closed ts ->
  eval (substs (rev ts) s) t ->
  eval (apps (lams n s) ts) t.
Proof.
  move=> ->. by apply: eval_apps_lams.
Qed.

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

Definition enum_regs : Vector.t term N := Vector.map var (Vector.rev (vec_seq 0 N)).

Definition enc_inc (x : Fin.t N) : term :=
  let n := proj1_sig (Fin.to_nat x) in
  lam (app (var 0) (lams N (app (lam (lam (apps (var 0) (map var ((seq 2 n) ++ [1] ++ seq (n+2) (N-n-2)))))) (app nat_succ (var n))))).

Lemma eval_enc_regs ts : eval (enc_regs ts) (enc_regs ts).
Proof.
  constructor.
Qed.



Lemma subst_ren n t k s : closed s -> subst (ren (fun x => n + x) t) (n + k) s = ren (fun x => n + x) (subst t k s).
Proof.
Admitted.

Lemma eval_lams_N s : eval (lams N s) (lams N s).
Proof.
  constructor.
Qed.

Lemma subst_var_eq x s : subst (var x) x s = s.
Proof.
  by rewrite /= Nat.eqb_refl.
Qed.

Lemma nat_enc_closed n : closed (nat_enc n).
Proof.
Admitted.

Lemma eval_nat_enc n : eval (nat_enc n) (nat_enc n).
Proof.
Admitted.

Lemma enc_inc_spec (x : Fin.t N) (v : Vector.t nat N) :
  eval (app (enc_inc x) (enc_regs v)) (enc_regs (vec.vec_change v x (S (vec.vec_pos v x)))).
Proof.
  rewrite /enc_inc. econstructor; [constructor|apply: eval_enc_regs|].
  rewrite /= subst_lams /= subst_apps /= map_map.
  rewrite /enc_regs. econstructor; [constructor|apply: eval_lams_N|].
  rewrite subst_apps /=. (* apply: eval_apps_lams'. 
  - by rewrite length_map Vector.length_to_list.
  - apply /Forall_map. apply /Vector.to_list_Forall.
    apply /Vector.Forall_map.
    apply /Vector.Forall_nth=> y. rewrite nat_enc_closed.
    apply: eval_nat_enc.
  - apply /Forall_map. apply /Vector.to_list_Forall.
    apply /Vector.Forall_map.
    apply /Vector.Forall_nth=> y. rewrite nat_enc_closed. apply: nat_enc_closed.
  - 
    *)
Admitted.

Opaque enc_inc.

Definition enc_instr (instr : mm_instr (Fin.t N)) : term :=
  match instr with
  | MM.mm_inc x =>
      lam (lam (apps (lam (lam (enc_pair (var 2) (var 1)))) [app pi_succ (var 1); app (enc_inc x) (var 0)]))
        (*
      
      
      app (var 0) (
        lams N (enc_pair
          (app pi_succ (var (S N)))
          (enc_regs (Vector.replace enum_regs x (app nat_succ (Vector.nth enum_regs x))))))))*)
  | MM.mm_dec x k => var 0
  end.

Definition enc_state (p : mm_state N) : term :=
  enc_pair (pi (addr (fst p))) (enc_regs (snd p)).

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

Lemma subst_app k s t u : subst (app s t) k u = app (subst s k u) (subst t k u).
Proof.
  done.
Qed.

Lemma subst_lam s k t : subst (lam s) k t = lam (subst s (S k) t).
Proof.
  done.
Qed.

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

Lemma enc_inc_closed x : closed (enc_inc x).
Proof.
Admitted.

Opaque enc_pair pi_succ pi enc_regs.

Axiom FF : False.

(* enc_instr at certain position? *)

Lemma mma_step_sim (instr : mm_instr (Fin.t N)) (p q : mm_state N) :
  mma_sss instr p q -> eval (apps (enc_instr instr) [pi (addr (fst p)); enc_regs (snd p)]) (enc_state q).
Proof.
  case.
  - (* INC *)
    move=> i x v /=.
    econstructor; [|apply: eval_enc_regs|].
    + econstructor; [constructor|apply: eval_pi|].
      rewrite subst_lam. by constructor.
    + rewrite /= !subst_enc_pair /= !enc_inc_closed.
      econstructor; [|apply: enc_inc_spec|].
      * econstructor; [constructor| |by rewrite /=; constructor].
        rewrite !pi_succ_closed !pi_addr_closed. by apply: pi_succ_spec.
      * rewrite !subst_enc_pair /= !pi_addr_closed.
        rewrite /enc_state /=. apply: eval_enc_pair.
  - (* DEC *)
    destruct FF.
  - (* JUMP *)
    destruct FF.
Qed.

(* \cs.\f.\run.cs *)
Definition enc_halt := lam (lam (lam (var 2))).
(* \i.\cs.i (halt :: P) cs *)
Definition enc_step := lam (lam (apps (var 1) (enc_halt :: map enc_instr P ++ [var 0]))).
(* \(i, cs).(i, cs) (\i.\cs.step i cs) (\i'.\cs'.\run.run i' cs' run) *)
Definition enc_run := lam (apps (var 0) [lam (lam (apps enc_step [var 1; var 0]));
  lam (lam (lam (apps (var 0) [var 2; var 1; var 0])))]).

Lemma enc_run_spec (p q : mm_state N) : @sss_step _ _ (@mma_sss N) (1, P) p q ->
  ARS.star L_facts.step (apps enc_run [enc_state p; enc_run]) (apps enc_run [enc_state q; enc_run]).
Proof.
Admitted.

Lemma enc_halt_spec (p : mm_state N) : fst p < 1 \/ S (length P) <= fst p ->
  ARS.star L_facts.step (apps enc_run [enc_state p; enc_run]) (nat_enc (Vector.hd (snd p))).
Proof.
Admitted.

Lemma enc_run_spec' {i v t} : eval (app (app enc_run (enc_state (i, v))) enc_run) t ->
  exists cs, t = enc_regs cs.
Proof.
Admitted.


End MMA_HALTING_to_HaltLclosed.


Require Import Undecidability.Synthetic.Definitions.

(* Halting problem for weak call-by-value lambda-calculus *)
Definition HaltLclosed (s : {s : term | closed s}) := exists t, eval (proj1_sig s) t.

Lemma reduction n : @MMA_HALTING (S n) ⪯ HaltLclosed.
Proof.
  unshelve eexists.
  - intros [P v]. exists (apps (enc_run P) [enc_state P (1, v); enc_run P]).
    admit.
  - intros [P v]. split.
    + intros [q Hq]. exists (nat_enc (Vector.hd (snd q))). cbn. admit. (* forwards simulation *)
    + intros [t Ht]. cbn in Ht. assert (H't := enc_run_spec' Ht).
      destruct H't as [cs ?]. subst.
      exists (0, cs). split.
      * admit. (* backwards simulation *)
      * cbn. lia.
Admitted.


Theorem MMA_computable_to_L_computable_closed {k} (R : Vector.t nat k -> nat -> Prop) :
  MMA_computable R -> L_computable_closed R.
Proof.
  unfold MMA_computable, L_computable_closed.
  move=> [n [P HP]].
  exists (apps (enc_run P) [(var 0); enc_run P]). (* TODO actual wrapper *)
  split.
  - admit. (* closedness *)
  - move=> v. split.
    + move=> m. rewrite HP. split.
      * intros [c [v' [H1 H2]]]. admit. (* forwards simulation *)
      * admit. (* backwards simulation *)
Admitted.