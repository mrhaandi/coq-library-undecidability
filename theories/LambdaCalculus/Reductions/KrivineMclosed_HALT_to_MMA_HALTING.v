(* TODO move to MinskyMachines *)
From Undecidability Require Import
  LambdaCalculus.Krivine MinskyMachines.MM.
From Undecidability Require
  LambdaCalculus.Krivine MinskyMachines.MMA.mma_defs.
From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Import PeanoNat List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.

#[local] Notation mm_instr := (mm_instr (pos 5)).
#[local] Notation counter := (pos 5).
#[local] Notation mm_state := (mm_state 5).

#[local] Notation "P // s -[ k ]-> t" := (sss_steps (@mma_sss _) P k s t).
#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).
#[local] Notation "P // s -+> t" := (sss_progress (@mma_sss _) P s t).
#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

#[local] Arguments vec_change_neq {X n v p q x}.
#[local] Arguments vec_change_eq {X n v p q x}.

Module Argument.

Lemma vec_change_comm {X : Type} {n : nat} {v : vec X n} {p q : pos n} {x y : X} : p <> q -> 
  vec_change (vec_change v p x) q y = vec_change (vec_change v q y) p x.
Proof.
  move=> Hpq.
  apply: vec_pos_ext => r.
  case: (pos_eq_dec p r); case: (pos_eq_dec q r).
  - move=> ??. by subst.
  - move=> ? <-. by rewrite (vec_change_neq (nesym Hpq)) !(vec_change_eq erefl).
  - move=> <- ?. by rewrite (vec_change_neq (Hpq)) !(vec_change_eq erefl).
  - move=> Hqr Hpr. by do ? rewrite ?(vec_change_neq (Hpr)) ?(vec_change_neq (Hqr)).
Qed.

Lemma vec_change_same' {X : Type} {n : nat} (v : vec X n) (p : pos n) (x : X) :
  vec_pos v p = x -> vec_change v p x = v.
Proof. move=> <-. by apply: vec_change_same. Qed.

(* auxiliary counters *)
Notation A := (Fin.F1 : counter).
Notation B := (Fin.FS (Fin.F1) : counter).
(* data counters *)
Notation TS := (Fin.FS (Fin.FS (Fin.F1)) : counter).
Notation CTX := (Fin.FS (Fin.FS (Fin.FS (Fin.F1))) : counter).
Notation U := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) : counter).

(* simplify vec_change statements *)
Definition vec_norm {X Y: counter} (HXY : X <> Y) := (
  fun v n m => @vec_change_comm nat _ v X Y n m HXY,
  fun v n m => @vec_change_idem nat _ v X n m,
  fun v n m => @vec_change_idem nat _ v Y n m,
  fun v n => @vec_change_neq nat _ v X Y n HXY,
  fun v n => @vec_change_neq nat _ v Y X n (nesym HXY),
  fun v n => @vec_change_eq nat _ v X X n erefl,
  fun v n => @vec_change_eq nat _ v Y Y n erefl,
  fun v => @vec_change_same nat _ v X,
  fun v => @vec_change_same nat _ v Y).

Definition Q_step (Q : list mm_instr) (offset i : nat) (v : vec nat 5) : option mm_state :=
  match nth_error Q i with
  | None => None
  | Some (INC x) => Some ((S i) + offset, vec_change v x (S (vec_pos v x)))
  | Some (DEC x p) => Some (
      match vec_pos v x with
      | 0 => ((S i) + offset, v)
      | S n => (p, vec_change v x n)
      end)
  end.

Lemma Q_step_spec (Q : list mm_instr) offset i v j w : 
  Q_step Q offset i v = Some (j, w) ->
  sss_step (mma_sss (n:=5)) (offset, Q) (i + offset, v) (j, w).
Proof.
  rewrite /Q_step. case E: (nth_error Q i) => [t|]; last done.
  move: E => /(@nth_error_split mm_instr) => - [l] [r] [-> <-].
  move=> Ht. exists offset, l, t, r, v. split; [|split]; [done|congr pair; lia|].
  move: t Ht => [].
  - move=> x [<-] <-. by apply: in_mma_sss_inc.
  - move=> x p.
    move Ex: (vec_pos v x) => [|?].
    + move=> [<- <-]. by apply: in_mma_sss_dec_0.
    + move=> [<- <-]. by apply: in_mma_sss_dec_1.
Qed.

Lemma Q_step_spec' (Q : list mm_instr) offset i v j w st : 
  Q_step Q offset i v = Some (j, w) ->
  (offset, Q) // (j, w) ->> st ->
  (offset, Q) // (i + offset, v) ->> st.
Proof.
  move=> /Q_step_spec ? ?.
  apply: sss_compute_trans; [|by eassumption].
  exists 1. apply: in_sss_steps_S; [by eassumption|].
  by apply: in_sss_steps_0.
Qed.

Fact sss_compute_refl i P (st : mm_state) : (i, P) // st ->> st.
Proof. exists 0. by apply: in_sss_steps_0. Qed.

Fact sss_compute_refl' i P (st1 st2 : mm_state) : st1 = st2 -> (i, P) // st1 ->> st2.
Proof. move=> ->. by apply: sss_compute_refl. Qed.

Arguments Q_step /.

(* X := 0 *)
Definition ZERO (X: counter) (offset: nat) : list mm_instr :=
  [DEC X (0+offset)].

Definition ZERO_length := 1.

Lemma ZERO_spec X v offset :
  (offset, ZERO X offset) // (0 + offset, v) ->> (ZERO_length+offset, vec_change v X 0).
Proof.
  move En: (vec_pos v X) => n.
  elim: n v En.
  - move=> v En.
    apply: Q_step_spec'. { by rewrite /= En. }
    apply: sss_compute_refl'. congr pair.
    by rewrite vec_change_same'.
  - move=> n IH v En.
    apply: Q_step_spec'. { by rewrite /= En. }
    rewrite -(vec_change_idem v X n 0).
    apply: IH. by apply: vec_change_eq.
Qed.

(* jump to address p *)
Definition JMP p (offset : nat) : list mm_instr :=
  [INC A; DEC A p].

Definition JMP_length := 2.

Lemma JMP_spec p v offset :
  (offset, JMP p offset) // (0 + offset, v) ->> (p, v).
Proof.
  apply: Q_step_spec'. { done. }
  apply: Q_step_spec'. { by rewrite /= vec_change_eq. }
  apply: sss_compute_refl'. by rewrite vec_change_idem vec_change_same.
Qed.

Arguments ZERO : simpl never.
Arguments plus : simpl never.

(* Y := X + Y *)
Definition MOVE (X Y: counter) (offset: nat) : list mm_instr :=
  JMP (3+offset) offset ++ [INC Y; DEC X (2+offset)].

Definition MOVE_length := JMP_length+2.

Lemma ext_counter (P : counter -> Prop) : 
  P A -> P B -> P TS -> P CTX -> P U -> forall (X : counter), P X.
Proof.
  move=> ?????.
  do 5 (move=> {}X; apply (Fin.caseS' X); first done).
  by apply: Fin.case0.
Qed.

Lemma MOVE_spec X Y v offset :
  let x := vec_pos v X in
  let y := vec_pos v Y in
  X <> Y ->
  (offset, MOVE X Y offset) // (offset, v) ->> (MOVE_length+offset, vec_change (vec_change v Y (y+x)) X 0).
Proof.
  move=> /= HXY.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (offset, JMP (3+offset) offset))).
    { exists []. eexists. split; [done|rewrite /=; lia]. }
    by apply: JMP_spec. }
  move En: (vec_pos v X) => n.
  move Ew: (vec_change _ X 0) => w.
  elim: n v En w Ew.
  - move=> v En w <-.
    apply: Q_step_spec'. { by rewrite /= En. }
    apply: sss_compute_refl'. congr pair.
    rewrite (vec_change_same' _ Y); [lia|].
    by rewrite vec_change_same'.
  - move=> n IH v En w <-.
    apply: Q_step_spec'. { by rewrite /= En. }
    apply: Q_step_spec'. { done. }
    apply: IH.
    + by rewrite (vec_change_neq (nesym HXY)) vec_change_eq.
    + rewrite !(vec_norm HXY). congr vec_change. congr vec_change. lia.
Qed.

(* Y := X *)
Definition COPY (X Y: counter) (offset: nat) : list mm_instr :=
  let i := offset in JMP (2+JMP_length+i) i ++
  let j := JMP_length + i in [INC A; INC Y] ++
  let i := 2 + j in [DEC X j] ++
  let i := 1 + i in MOVE A X i ++ [].

Definition COPY_length := length (COPY A A 0).

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_ind (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Lemma COPY_spec X Y v offset :
  let x := vec_pos v X in let y := vec_pos v Y in let a := vec_pos v A in
  A <> X -> A <> Y -> X <> Y ->
  (offset, COPY X Y offset) // (offset, v) ->>
    (COPY_length+offset, vec_change (vec_change (vec_change v X (a+x)) Y (x+y)) A 0).
Proof.
  move=> /= HX HY HXY. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: JMP_spec. }
  move Ew: (vec_change _ A _) => w.
  elim /(measure_ind (fun v => vec_pos v X)): v w Ew.
  move=> v IH w <-. case Ex: (vec_pos v X) => [|x].
  { apply: Q_step_spec'. { by rewrite /= Ex. }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, MOVE _ _ _))).
      { eexists _, _. rewrite /COPY. by do 2 rewrite [LHS]app_assoc. }
      rewrite ?H'. by apply: MOVE_spec. }
    apply: sss_compute_refl'. congr pair.
    congr vec_change. rewrite !(vec_norm HXY). congr vec_change. lia. }
  apply: Q_step_spec'. { by rewrite /= Ex. }
  apply: Q_step_spec'. { done. }
  apply: Q_step_spec'. { done. }
  apply: IH.
  - rewrite !(vec_norm HXY) !(vec_norm HX). lia.
  - do ? rewrite ?(vec_norm HX) ?(vec_norm HY) ?(vec_norm HXY).
    congr vec_change. congr vec_change; last by lia.
    congr vec_change. lia.
Qed.


(* X := X+X *)
Definition DOUBLE (X: counter) (offset: nat) : list mm_instr :=
  let i := offset in ZERO A offset ++ 
  let i := ZERO_length + i in JMP (JMP_length + 2 + i) i ++
  let i := JMP_length + i in [INC A; INC A; DEC X i] ++
  let i := 3 + i in MOVE A X i.

Definition DOUBLE_length := ZERO_length + JMP_length + 3 + MOVE_length.

Arguments app : simpl never.

Lemma DOUBLE_spec X v offset :
  let x := vec_pos v X in
  A <> X ->
  (offset, DOUBLE X offset) // (offset, v) ->>
    (DOUBLE_length+offset, vec_change (vec_change v X (x+x)) A 0).
Proof.
  have H' : forall i, offset + i = i + offset by lia.
  move=> /= HX.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (offset, ZERO A offset))).
    { exists []. eexists. split; [done|rewrite /=; lia]. }
    by apply: ZERO_spec. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { rewrite /= /DOUBLE. by do 2 eexists. }
    rewrite ?H'. by apply: JMP_spec. }
  move Ev': (vec_change v A 0) => v'.
  have :
    let x := vec_pos v' X in forall w, w = vec_change (vec_change v' X 0) A (x+x+(vec_pos v' A)) ->
    (offset, DOUBLE X offset) //
    (JMP_length + 2 + (ZERO_length + offset), v') ->>
    (JMP_length + 3 + (ZERO_length + offset), w).
  { move En: (vec_pos v' X) => n.
    elim: n (v') En.
    - move=> v'' En x w ->.
      rewrite !Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= En. }
      apply: sss_compute_refl'. congr pair.
      rewrite (vec_change_same' _ X); first done.
      by rewrite vec_change_same'.
    - move=> n IH v'' En x w ->.
      rewrite !Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= En. }
      rewrite !Nat.add_assoc. apply: Q_step_spec'. { done. }
      apply: Q_step_spec'. { done. }
      apply: IH.
      + by rewrite !(vec_change_neq HX) vec_change_eq.
      + rewrite !(vec_norm HX). congr vec_change. lia. }
  move=> /(_ _ erefl) /sss_compute_trans. apply.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, MOVE _ _ _))).
    { rewrite /= /DOUBLE. do 2 eexists. by do 2 rewrite [LHS]app_assoc. }
      rewrite ?H'. by apply: MOVE_spec. }
  apply: sss_compute_refl'. congr pair.
  rewrite -Ev' !(vec_norm HX). congr vec_change. congr vec_change. lia.
Qed.

(* X := (X+X+1)*(2^Y) *)
Definition PACK (X Y: counter) (offset: nat) : list mm_instr :=
  DOUBLE X offset ++
  let i := DOUBLE_length + offset in [INC X] ++
  let i := 1 + i in JMP (DOUBLE_length+JMP_length+i) i ++
  let i := JMP_length + i in DOUBLE X i ++
  [DEC Y i].

Definition PACK_length :=  DOUBLE_length + 1 + JMP_length + DOUBLE_length + 1.

Lemma asdd (n m : nat) v (X Y : counter): 
  (X = Y -> n = m) ->
  (X <> Y -> n = vec_pos v X)
  -> n = vec_pos (vec_change v Y m) X.
Proof.
  have [|] := pos_eq_dec X Y.
  - move=> -> /(_ erefl) -> _. by rewrite vec_change_eq.
  - move=> /[dup] /nesym /vec_change_neq ->.
    by move=> + _ H => /H.
Qed.

Lemma PACK_spec X Y v offset :
  let x := vec_pos v X in
  let y := vec_pos v Y in
  A <> X -> A <> Y -> X <> Y ->
  (offset, PACK X Y offset) // (offset, v) ->>
    (PACK_length+offset, vec_change (vec_change (vec_change v X ((x+x+1) * (2 ^ y))) Y 0) A 0).
Proof.
  move=> /= HX HY HXY. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, DOUBLE _ _))).
    { exists []. by eexists. }
    rewrite ?H'. by apply: DOUBLE_spec. }
  apply: Q_step_spec'. { done. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { do 2 eexists. rewrite /PACK. by rewrite [LHS]app_assoc. }
    rewrite ?H'. by apply: JMP_spec. }
  move Ev': (v' in _ // (_, v') ->> _) => v'.
  have HAv' : vec_pos v' A = 0.
  { by rewrite -Ev' (vec_change_neq (nesym HX)) vec_change_eq. }
  have :
    let x := vec_pos v' X in let y := vec_pos v' Y in
    forall w, w = vec_change (vec_change (vec_change v' A 0) Y 0) X (x * (2 ^ y)) ->
    (offset, PACK X Y offset) //
    (DOUBLE_length + JMP_length + (1 + (DOUBLE_length + offset)), v') ->>
    (1 + DOUBLE_length + JMP_length + (1 + (DOUBLE_length + offset)), w).
  { move En: (vec_pos v' Y) => n /=.
    elim: n (v') En HAv'.
    - move=> v'' En HAv'' w ->.
      rewrite !Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= En. }
      apply: sss_compute_refl'. congr pair.
      rewrite (vec_change_same' _ A) // (vec_change_same' _ Y) // vec_change_same' //=.
      lia.
    - move=> n IH v'' En HAv'' w ->.
      rewrite !Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= En. }
      apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, DOUBLE _ _))).
        { do 2 eexists. rewrite /PACK. by do 2 rewrite app_assoc. }
        rewrite ?H'. by apply: DOUBLE_spec. }
      apply: IH.
      + by rewrite !(vec_change_neq HY) !(vec_change_neq HXY) vec_change_eq.
      + by rewrite vec_change_eq.
      + rewrite !(vec_norm HY) !(vec_norm HX) !(vec_norm HXY) /=.
        congr vec_change. congr vec_change. lia. }
  move=> /(_ _ erefl) /sss_compute_trans. apply.
  apply: sss_compute_refl'. congr pair.
  rewrite -Ev' /=. do ? rewrite ?(vec_norm HY) ?(vec_norm HX) ?(vec_norm HXY).
  congr vec_change. congr vec_change. lia.
Qed.

(* X := X/2 + A if X even goto p else goto q *)
Definition HALF (X: counter) (p q: nat) (offset: nat) : list mm_instr :=
  let i := offset in JMP (JMP_length + 1 + i) i ++
  let i := JMP_length + i in let j := i in [INC A; DEC X (2+JMP_length+MOVE_length+i)] ++
  let i := 2 + i in MOVE A X i ++
  let i := MOVE_length + i in JMP p i ++
  let i := JMP_length + i in [DEC X j] ++
  let i := 1 + i in MOVE A X i ++
  let i := MOVE_length + i in JMP q i.

Definition HALF_length := length (HALF A 0 0 0).

(* second component is true iff n is even *)
Fixpoint half (n: nat) : (nat * bool) :=
  match n with
  | 0 => (0, true)
  | S n' => 
      match half n' with
      | (m, b) => if b then (m, false) else (S m, true)
      end
  end.

Lemma half_spec n :
  match half n with
  | (m, b) => n = (if b then 0 else 1) + m + m
  end.
Proof. elim: n => [|n] /=; [done|case: (half n) => ? []; lia]. Qed.

(*
Lemma sig_half (n: nat) : { m | n = m + m } + { m | n = 1 + m + m }.
Proof.
  elim : n. { left. by exists 0. }
  move=> n [[m Hm]|[m Hm]].
  - right. exists m. lia.
  - left. exists (S m). lia.
Qed.
*)




Lemma HALF_spec X p q v offset :
  let x := vec_pos v X in let a := vec_pos v A in
  A <> X ->
  (offset, HALF X p q offset) // (offset, v) ->>
    let '(m, b) := half x in (if b then p else q, vec_change (vec_change v X (a+m)) A 0).
Proof.
  move=> /= HX. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: JMP_spec. }
  move Hst: (st in _ // _ ->> st) => st.
  elim /(measure_ind (fun v => vec_pos v X)) : v st Hst.
  move=> v IH st <-.
  case EX: (vec_pos v X) => [|[|n]].
  { apply: Q_step_spec'. { by rewrite /= EX. }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, MOVE _ _ _))).
      { eexists _, _. by rewrite /HALF [LHS]app_assoc. }
      rewrite ?H'. by apply: MOVE_spec. }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, JMP _ _))).
      { eexists _, _. by rewrite /HALF [LHS]app_assoc [LHS]app_assoc. }
      rewrite ?H'. by apply: JMP_spec. }
    apply: sss_compute_refl'. by rewrite EX !Nat.add_0_r. }
  { apply: Q_step_spec'. { by rewrite /= EX. }
    rewrite !Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= (vec_change_eq erefl). }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, MOVE _ _ _))).
      { eexists _, _. rewrite /HALF. by do 4 rewrite [LHS]app_assoc. }
      rewrite ?H'. by apply: MOVE_spec. }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, JMP _ _))).
      { eexists _, _. rewrite /HALF. by do 5 rewrite [LHS]app_assoc. }
      rewrite ?H'. by apply: JMP_spec. }
    apply: sss_compute_refl'. by rewrite !(vec_norm HX) !Nat.add_0_r. }
  apply: Q_step_spec'. { by rewrite /= EX. }
  rewrite !Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= (vec_change_eq erefl). }
  apply: Q_step_spec'. { done. }
  apply: IH. { rewrite !(vec_norm HX). lia. }
  rewrite !(vec_norm HX) /=.
  have := half_spec n. case: (half n) => m [] ->.
  - rewrite !(vec_norm HX). congr pair. congr vec_change. congr vec_change. lia.
  - rewrite !(vec_norm HX). congr pair. congr vec_change. congr vec_change. lia.
Qed.

(* IF X = 0 then GOTO p else GOTO q *)
Definition BR (X: counter) (p q: nat) (offset: nat) : list mm_instr :=
  let i := offset in [DEC X (JMP_length + 1 + i)] ++
  let i := 1 + i in JMP p i ++
  let i := JMP_length + i in [INC X] ++
  let i := 1 + i in JMP q i.  

Lemma BR_spec X p q v offset :
  let x := vec_pos v X in
  (offset, BR X p q offset) // (offset, v) ->> (if x is 0 then p else q, v).
Proof.
  move=> /=. have H' : forall i, offset + i = i + offset by lia.
  case EX: (vec_pos v X) => [|n].
  - apply: (Q_step_spec' _ _ 0). { by rewrite /= EX. }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, JMP _ _))).
      { eexists _, _. done. }
      rewrite ?H'. by apply: JMP_spec. }
    by apply: sss_compute_refl'.
  - apply: (Q_step_spec' _ _ 0). { by rewrite /= EX. }
    apply: Q_step_spec'. { done. }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, JMP _ _))).
      { eexists _, _. rewrite /BR. by do 2 rewrite [LHS]app_assoc. }
      rewrite ?H'. by apply: JMP_spec. }
    apply: sss_compute_refl'. congr pair.
    by rewrite (vec_change_eq erefl) vec_change_idem -EX vec_change_same.
Qed.

Definition BR_length := length (BR A 0 0 0).
Arguments BR_length : simpl never.

Lemma half_spec_odd n : half ((n + n + 1) * 2 ^ 0) = (n, false).
Proof.
  have := half_spec ((n + n + 1) * 2 ^ 0).
  case: (half _) => m [] /= *; congr pair; lia.
Qed.

Lemma half_spec_even n m : half ((n + n + 1) * 2 ^ (S m)) = ((n + n + 1) * 2 ^ m, true).
Proof.
  have := half_spec ((n + n + 1) * 2 ^ (S m)).
  case: (half _) => k []; rewrite /= => ?; congr pair; lia.
Qed.

(* IF X = (n+n+1)*2^m THEN X := n AND Y := m *)
Definition UNPACK (X Y: counter) (offset: nat) : list mm_instr :=
  let i := offset in BR X 0 (BR_length + i) i ++
  let i := BR_length + i in ZERO A i ++
  let i := ZERO_length + i in ZERO Y i ++
  let j := ZERO_length + i in HALF X (HALF_length + j) (JMP_length + 1 + HALF_length + j) j ++
  let i := HALF_length + j in [INC Y] ++
  let i := 1 + i in JMP j i.

Definition UNPACK_length := length (UNPACK A A 0).

Lemma UNPACK_spec {X Y m n v offset} :
  let x := vec_pos v X in
  x = (n + n + 1) * (2 ^ m) ->
  A <> X -> A <> Y -> X <> Y ->
  (offset, UNPACK X Y offset) // (offset, v) ->>
    (UNPACK_length + offset, vec_change (vec_change (vec_change v X n) Y m) A 0).
Proof.
  move=> /= H'X HX HY HXY. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, BR _ _ _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: BR_spec. }
  have ->: vec_pos v X = S (vec_pos v X - 1).
  { rewrite H'X. have := Nat.pow_nonzero 2 m. lia. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, ZERO _ _))).
    { by eexists _, _. }
    rewrite ?H'. by apply: ZERO_spec. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, ZERO _ _))).
    { eexists _, _. by rewrite /UNPACK [LHS]app_assoc. }
    rewrite ?H'. by apply: ZERO_spec. }
  suff : forall v' w', 
    w' = vec_change (vec_change v' X n) Y (m + vec_pos v' Y) ->
    vec_pos v' X = (n + n + 1) * 2 ^ m ->
    vec_pos v' A = 0 ->
    (offset, UNPACK X Y offset) //
    (ZERO_length + BR_length + ZERO_length + offset, v') ->> (UNPACK_length + offset, w').
  { apply.
    - by rewrite !(vec_norm HXY) !(vec_norm HY) !(vec_norm HX) Nat.add_0_r.
    - by rewrite !(vec_norm HXY) !(vec_norm HX).
    - by rewrite !(vec_norm HY). }
  elim: m {H'X}.
  { move=> v' w' -> H'v' H''v'.
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, HALF _ _ _ _))).
      { eexists _, _. rewrite /UNPACK. by do 2 rewrite [LHS]app_assoc. }
      rewrite ?H'. by apply: HALF_spec. }
    rewrite H'v' half_spec_odd.
    apply: sss_compute_refl'. congr pair.
    rewrite H''v' !Nat.add_0_l !(vec_norm HXY) !(vec_norm (nesym HX)).
    congr vec_change. by rewrite vec_change_same'. }
  move=> m IH v' w' -> H'v' H''v'.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, HALF _ _ _ _))).
    { eexists _, _. rewrite /UNPACK. by do 2 rewrite [LHS]app_assoc. }
    rewrite ?H'. by apply: HALF_spec. }
  rewrite H'v' half_spec_even.
  rewrite !Nat.add_assoc. apply: Q_step_spec'. { done. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { eexists _, _. rewrite /UNPACK. by do 4 rewrite [LHS]app_assoc. }
    rewrite ?H'. by apply: JMP_spec. }
  apply: IH.
  - do ? rewrite ?(vec_norm (nesym HY)) ?(vec_norm (nesym HX)) ?(vec_norm HXY).
    rewrite (vec_change_same' v' A 0 H''v').
    congr vec_change. congr vec_change. lia.
  - by rewrite !(vec_norm HXY) !(vec_norm HX) H''v'.
  - by rewrite !(vec_norm HY).
Qed.

Lemma UNPACK_spec' {X Y v offset} :
  vec_pos v X = 0 ->
  (offset, UNPACK X Y offset) // (offset, v) ->> (0, v).
Proof.
  move=> H'X. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, BR _ _ _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: BR_spec. }
  rewrite H'X. by apply: sss_compute_refl.
Qed.

(*
(* IF X = (n+n+1)*2^m THEN X := n AND Y := m *)
Definition UNPACK (X Y: counter) (offset: nat) : list mm_instr :=
  let i := offset in BR X 0 (BR_length + i) i ++
  let i := BR_length + i in ZERO A i ++
  let j := ZERO_length + i in HALF X (HALF_length + j) (JMP_length + 1 + HALF_length + j) j ++
  let i := HALF_length + j in [INC Y] ++
  let i := 1 + i in JMP j i.

Definition UNPACK_length := length (UNPACK A A 0).

Lemma UNPACK_spec X Y m n v offset :
  let x := vec_pos v X in
  let y := vec_pos v Y in
  x = (n+n+1) * (2 ^ m) ->
  A <> X -> A <> Y -> X <> Y ->
  (offset, UNPACK X Y offset) // (offset, v) ->>
    (UNPACK_length + offset, vec_change (vec_change (vec_change v X n) Y (m+y)) A 0).
Proof.
  move=> /= H'X HX HY HXY. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, BR _ _ _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: BR_spec. }
  have ->: vec_pos v X = S (vec_pos v X - 1).
  { rewrite H'X. have := Nat.pow_nonzero 2 m. lia. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, ZERO _ _))).
    { by eexists _, _. }
    rewrite ?H'. by apply: ZERO_spec. }
  move Ew: (w in _ // _ ->> (_, w)) => w.
  elim: m v H'X w Ew.
  { move=> v H'X ? <-.
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, HALF _ _ _ _))).
      { eexists _, _. by rewrite /UNPACK [LHS]app_assoc. }
      rewrite ?H'. by apply: HALF_spec. }
    rewrite !(vec_norm HX) H'X half_spec_odd.
    apply: sss_compute_refl'. congr pair.
    by rewrite !Nat.add_0_l !(vec_norm HX) !(vec_norm HXY). }
  move=> m IH v H'X ? <-.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, HALF _ _ _ _))).
    { eexists _, _. by rewrite /UNPACK [LHS]app_assoc. }
    rewrite ?H'. by apply: HALF_spec. }
  rewrite !(vec_norm HX) H'X half_spec_even.
  rewrite !Nat.add_assoc. apply: Q_step_spec'. { done. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { eexists _, _. rewrite /UNPACK. by do 3 rewrite [LHS]app_assoc. }
    rewrite ?H'. by apply: JMP_spec. }
  rewrite !(vec_norm HX) !(vec_norm HY).
  apply: IH. { by rewrite !(vec_norm HXY). }
  rewrite !(vec_norm HXY). congr vec_change. congr vec_change. congr vec_change. lia.
Qed.
*)

Definition enc_pair (m n: nat) := (n+n+1)*(2^m).

Import L (term, var, app, lam).

Fixpoint enc_term (s: term) : nat :=
  match s with
  | var n => enc_pair 0 n
  | lam s => enc_pair 1 (enc_term s)
  | app s t => enc_pair (2 + enc_term t) (enc_term s)
  end.

Fixpoint enc_list (ns : list nat) : nat :=
  match ns with
  | [] => 0
  | n::ns => enc_pair n (enc_list ns)
  end.

Fixpoint enc_closure (u: eterm) :=
  match u with
  | closure ctx s => enc_pair (enc_list (map enc_closure ctx)) (enc_term s)
  end.

Definition enc_cs ctx := enc_list (map enc_closure ctx).
Arguments enc_cs !ctx /.

Lemma HUA : A <> U.
Proof. done. Qed.


Lemma counters_eta (v : vec nat 5) :
  v = Vector.hd v ## 
    Vector.hd (VectorDef.tl v) ## 
    Vector.hd (VectorDef.tl (VectorDef.tl v)) ## 
    Vector.hd (VectorDef.tl (VectorDef.tl (VectorDef.tl v))) ##
    Vector.hd (VectorDef.tl (VectorDef.tl (VectorDef.tl (VectorDef.tl v)))) ##
    Vector.tl (VectorDef.tl (VectorDef.tl (VectorDef.tl (VectorDef.tl v)))).
Proof.
  by do 5 (rewrite [LHS](Vector.eta v); congr Vector.cons; move: (Vector.tl v) => {}v).
Qed.

Definition CASE_VAR0 (p: nat) (offset : nat) : list mm_instr :=
  let i := offset in UNPACK CTX U i ++
  let i := UNPACK_length + i in UNPACK U CTX i ++
  let i := UNPACK_length + i in JMP p i.

Definition CASE_VAR0_length := length (CASE_VAR0 0 0).

Lemma CASE_VAR0_spec ctx' t' ctx p v offset :
  vec_pos v CTX = enc_cs ((closure ctx' t') :: ctx) ->
  (offset, CASE_VAR0 p offset) // (offset, v) ->>
    (p, vec_change (vec_change (vec_change v U (enc_term t')) CTX (enc_cs ctx')) A 0).
Proof.
  move=> /= Hv. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: (UNPACK_spec Hv). }
  move Ev': (vec_change _ A 0) => v'.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
    { by eexists _, _. }
    rewrite ?H'.
    have /= /UNPACK_spec : vec_pos v' U = enc_closure (closure ctx' t').
    { by rewrite -Ev' (counters_eta v). } by apply. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { eexists _, _. by rewrite /CASE_VAR0 [LHS]app_assoc. }
    rewrite ?H'. by apply: JMP_spec. }
  apply: sss_compute_refl'. congr pair.
  by rewrite -Ev' (counters_eta v).
Qed.

Definition CASE_VARS (p: nat) (offset : nat) : list mm_instr :=
  let i := offset in UNPACK CTX B i ++
  let i := UNPACK_length + i in ZERO B i ++
  let i := ZERO_length + i in PACK U B i ++
  let i := PACK_length + i in JMP p i.

Definition CASE_VARS_length := length (CASE_VARS 0 0).

Lemma CASE_VARS_spec u ctx n p v offset :
  vec_pos v CTX = enc_cs (u :: ctx) ->
  vec_pos v U = n ->
  vec_pos v B = 0 ->
  (offset, CASE_VARS p offset) // (offset, v) ->>
    (p, vec_change (vec_change (vec_change v U (enc_term (var n))) CTX (enc_cs ctx)) A 0).
Proof.
  move=> /= HCTX HU HB. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: (UNPACK_spec HCTX). }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, ZERO _ _))).
    { by eexists _, _. }
    rewrite ?H'. by apply: ZERO_spec. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, PACK _ _ _))).
    { eexists _, _. by rewrite /CASE_VARS [LHS]app_assoc. }
    rewrite ?H'. by apply: PACK_spec. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { eexists _, _. rewrite /CASE_VARS. by do 2 rewrite [LHS]app_assoc. }
    rewrite ?H'. by apply: JMP_spec. }
  apply: sss_compute_refl'. move: HCTX HU HB. rewrite (counters_eta v) /=.
  by move=> ? -> ->.
Qed.

Definition CASE_APP (p: nat) (offset : nat) : list mm_instr :=
  let i := offset in PACK B CTX i ++
  let i := PACK_length + i in PACK TS B i ++
  let i := PACK_length + i in COPY TS CTX i ++
  let i := COPY_length + i in UNPACK CTX B i ++
  let i := UNPACK_length + i in UNPACK B CTX i ++
  let i := UNPACK_length + i in JMP p i ++
  [].

Definition CASE_APP_length := length (CASE_APP 0 0).

Arguments Nat.pow : simpl never.

Lemma CASE_APP_spec ts ctx t p v offset :
  vec_pos v TS = enc_cs ts ->
  vec_pos v CTX = enc_cs ctx ->
  vec_pos v B = enc_term t ->
  (offset, CASE_APP p offset) // (offset, v) ->>
    (p, vec_change (vec_change v TS (enc_cs ((closure ctx t)::ts))) A 0).
Proof.
  move=> /= HTS HCTX HB. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, PACK _ _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: PACK_spec. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, PACK _ _ _))).
    { by eexists _, _. }
    rewrite ?H'. by apply: PACK_spec. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, COPY _ _ _))).
    { eexists _, _. rewrite /CASE_APP. by do 1 rewrite [LHS]app_assoc. }
    rewrite ?H'. by apply: COPY_spec. }
  do ? (rewrite ?(vec_change_eq erefl); try (rewrite vec_change_neq; first done)).
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
    { eexists _, _. rewrite /CASE_APP. by do 2 rewrite [LHS]app_assoc. }
    rewrite ?H'. apply: UNPACK_spec; [|done ..].
    do ? (rewrite ?(vec_change_eq erefl); try (rewrite vec_change_neq; first done)).
    by rewrite Nat.add_0_r. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
    { eexists _, _. rewrite /CASE_APP. by do 3 rewrite [LHS]app_assoc. }
    rewrite ?H'. apply: UNPACK_spec; [|done ..].
    do ? (rewrite ?(vec_change_eq erefl); try (rewrite vec_change_neq; first done)).
    done. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { eexists _, _. rewrite /CASE_APP. by do 4 rewrite [LHS]app_assoc. }
    rewrite ?H'. by apply: JMP_spec. }
  apply: sss_compute_refl'. move: HTS HCTX HB. rewrite (counters_eta v) /=.
  by move=> -> -> ->.
Qed.

Definition CASE_LAM (p: nat) (offset : nat) : list mm_instr :=
  let i := offset in UNPACK TS B i ++
  let i := UNPACK_length + i in PACK CTX B i ++
  let i := PACK_length + i in JMP p i ++
  [].

Definition CASE_LAM_length := length (CASE_LAM 0 0).

Lemma CASE_LAM_spec t ts ctx p v offset :
  vec_pos v TS = enc_cs (t :: ts) ->
  vec_pos v CTX = enc_cs ctx ->
  vec_pos v B = 0 ->
  (offset, CASE_LAM p offset) // (offset, v) ->>
    (p, vec_change (vec_change (vec_change v TS (enc_cs ts)) CTX (enc_cs (t::ctx))) A 0).
Proof.
  move=> /= HTS HCTX HB. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: (UNPACK_spec HTS). }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, PACK _ _ _))).
    { by eexists _, _. }
    rewrite ?H'. by apply: PACK_spec. }
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, JMP _ _))).
    { eexists _, _. rewrite /CASE_VARS. by do 1 rewrite [LHS]app_assoc. }
    rewrite ?H'. by apply: JMP_spec. }
  apply: sss_compute_refl'. move: HTS HCTX HB. rewrite (counters_eta v) /=.
  by move=> ? -> ->.
Qed.

Lemma CASE_LAM_spec' p v offset :
  vec_pos v TS = enc_cs [] ->
  (offset, CASE_LAM p offset) // (offset, v) ->> (0, v).
Proof.
  move=> /= HTS. have H' : forall i, offset + i = i + offset by lia.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
    { by eexists [], _. }
    rewrite ?H'. by apply: (UNPACK_spec' HTS). }
  by apply: sss_compute_refl.
Qed.

Definition NOOP (offset : nat) : list mm_instr :=
  JMP (JMP_length + offset) offset.

Definition NOOP_length := length (NOOP 0).

Lemma NOOP_spec v offset :
  (offset, NOOP offset) // (offset, v) -+> (NOOP_length+offset, v).
Proof.
  exists 2. split; first by lia.
  apply: in_sss_steps_S. { by apply: (Q_step_spec _ offset 0). }
  apply: in_sss_steps_S. { apply: Q_step_spec. by rewrite /= (vec_change_eq erefl). }
  rewrite vec_change_idem vec_change_same.
  by apply: in_sss_steps_0.
Qed.

Definition PROG (offset : nat) : list mm_instr :=
  let i := offset in NOOP i ++
  let i := NOOP_length + i in UNPACK U B i ++
  let i := UNPACK_length + i in [DEC B (CASE_VARS_length+CASE_VAR0_length+2+i)] ++
  (* var _ CASE *) let i := 1 + i in [DEC U (CASE_VAR0_length+1+i)] ++
  (* var 0 CASE *) let i := 1 + i in CASE_VAR0 offset i ++
  (* var (S n) CASE *) let i := CASE_VAR0_length + i in CASE_VARS offset i ++
  let i := CASE_VARS_length + i in [DEC B (CASE_LAM_length+1+i)] ++
  (* lam s CASE *) let i := 1 + i in CASE_LAM offset i ++
  (* app s t CASE *) let i := CASE_LAM_length + i in CASE_APP offset i ++
  [].

Definition Krivine_step : (list eterm * list eterm * term) -> option (list eterm * list eterm * term) :=
  fun '(ts, ctx, t) =>
  match t with
  | var 0 => 
      match ctx with
      | [] => None
      | (closure ctx t)::_ => Some (ts, ctx, t)
      end
  | var (S n) =>
      match ctx with
      | [] => None
      | _::ctx => Some (ts, ctx, var n)
      end
  | lam s =>
      match ts with
      | [] => None
      | t::ts => Some (ts, t::ctx, s)
      end
  | app s t => Some ((closure ctx t)::ts, ctx, s)
  end.

Lemma iter_plus {X} {f : X -> X} {x : X} n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
  elim: m; first by rewrite Nat.add_0_r.
  move=> m /= <-. by have ->: n + S m = S n + m by lia.
Qed.

Lemma oiter_None {X : Type} (f : X -> option X) k : Nat.iter k (obind f) None = None.
Proof. elim: k; [done | by move=> /= ? ->]. Qed.

Lemma Krivine_step_spec ts ctx t : halt_cbn ts ctx t <-> 
  exists k ctx' t', Nat.iter k (obind Krivine_step) (Some (ts, ctx, t)) = Some ([], ctx', lam t').
Proof.
  split.
  - elim.
    1-4: by move=> > ? [n] [ctx'] [t'] IH; exists (S n), ctx', t'; rewrite (iter_plus 1 n).
    move=> >. exists 0. by do 2 eexists.
  - move=> [k] [ctx'] [t'].
    elim: k ts ctx t. { move=> > [-> -> ->]. by apply: halt_lam. }
    move=> k IH ts ctx t. rewrite (iter_plus 1 k) /=.
    case: t.
    + move=> [|n].
      * case: ctx; first by rewrite oiter_None.
        move=> [? ?] ? /IH ?. by apply: halt_var_0.
      * case: ctx; first by rewrite oiter_None.
        move=> [? ?] ? /IH ?. by apply: halt_var_S.
    + move=> ?? /IH ?. by apply: halt_app.
    + move=> ?. case: ts; first by rewrite oiter_None.
      move=> ?? /IH ?. by apply: halt_lam_ts.
Qed.

Lemma HAB : A <> B.
Proof. done. Qed.

Lemma HACTX : A <> CTX.
Proof. done. Qed.

Lemma HBCTX : B <> CTX.
Proof. done. Qed.

Lemma HCTXU : CTX <> U.
Proof. done. Qed.

Lemma HAU : A <> U.
Proof. done. Qed.

Lemma HBU : B <> U.
Proof. done. Qed.

Lemma PROG_spec ts ctx t v ts' ctx' t' offset :
  vec_pos v TS = enc_cs ts ->
  vec_pos v CTX = enc_cs ctx ->
  vec_pos v U = enc_term t ->
  Krivine_step (ts, ctx, t) = Some (ts', ctx', t') ->
  exists w, 
    vec_pos w TS = enc_cs ts' /\
    vec_pos w CTX = enc_cs ctx' /\
    vec_pos w U = enc_term t' /\
    (offset, PROG offset) // (offset, v) -+> (offset, w).
Proof.
  have H' : forall i, offset + i = i + offset by lia.
  case: t.
  - move=> [|n] /=; (case: ctx; first done).
    + (* case (var 0) *)
      move=> [ctx'' t'' ?] H1v H2v H3v  [<- <- <-].
      exists (vec_change (vec_change (vec_change (vec_change v U (enc_term t'')) CTX (enc_cs ctx'')) B 0) A 0).
      split. { move: H1v. by rewrite (counters_eta v). }
      split. { move: H2v. by rewrite (counters_eta v). }
      split. { move: H3v. by rewrite (counters_eta v). }
      apply: sss_progress_compute_trans.
      { apply: (subcode_sss_progress (P := (_, NOOP _))).
        { by eexists [], _. }
        rewrite ?H'. by apply: NOOP_spec. }
      apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
        { by eexists _, _. }
        rewrite ?H'. by apply: (UNPACK_spec H3v). }
      rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= !(vec_norm HAB). }
      rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= !(vec_norm HAU) !(vec_norm HBU). }
      apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, CASE_VAR0 _ _))).
        { eexists _, _. rewrite /PROG. by do 3 rewrite [LHS]app_assoc. }
        rewrite ?H'. apply: CASE_VAR0_spec.
        do ? (rewrite vec_change_neq; first done). by eassumption. }
      apply: sss_compute_refl'. by rewrite (counters_eta v).
    + (* case (var (S n)) *)
      move=> ? ctx'' H1v H2v H3v  [<- <- <-].
      exists (vec_change (vec_change (vec_change (vec_change v U (enc_term (var n))) CTX (enc_cs ctx'')) B 0) A 0).
      split. { move: H1v. by rewrite (counters_eta v). }
      split. { move: H2v. by rewrite (counters_eta v). }
      split. { move: H3v. by rewrite (counters_eta v). }
      apply: sss_progress_compute_trans.
      { apply: (subcode_sss_progress (P := (_, NOOP _))).
        { by eexists [], _. }
        rewrite ?H'. by apply: NOOP_spec. }
      apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
        { by eexists _, _. }
        rewrite ?H'. by apply: (UNPACK_spec H3v). }
      rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= !(vec_norm HAB). }
      rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= !(vec_norm HAU) !(vec_norm HBU). }
      apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, CASE_VARS _ _))).
        { eexists _, _. rewrite /PROG. by do 4 rewrite [LHS]app_assoc. }
        rewrite ?H'. apply: CASE_VARS_spec.
        - do ? (rewrite vec_change_neq; first done). by eassumption.
        - by rewrite (vec_change_eq erefl).
        - do ? (rewrite vec_change_neq; first done). by rewrite (vec_change_eq erefl). }
      apply: sss_compute_refl'. by rewrite (counters_eta v).
  - (* case (app s t) *)
    move=> s t H1v H2v H3v [<- <- <-].
    exists (vec_change (vec_change (vec_change (vec_change v U (enc_term s)) B (enc_term t)) TS (enc_cs ((closure ctx t)::ts))) A 0).
    split. { move: H1v. by rewrite (counters_eta v). }
    split. { move: H2v. by rewrite (counters_eta v). }
    split. { move: H3v. by rewrite (counters_eta v). }
    apply: sss_progress_compute_trans.
    { apply: (subcode_sss_progress (P := (_, NOOP _))).
      { by eexists [], _. }
      rewrite ?H'. by apply: NOOP_spec. }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
      { by eexists _, _. }
      rewrite ?H'. by apply: (UNPACK_spec H3v). }
    rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= -/enc_term !(vec_norm HAB). }
    rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= !(vec_norm HAB). }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, CASE_APP _ _))).
      { eexists _, _. rewrite /PROG. by do 7 rewrite [LHS]app_assoc. }
      rewrite ?H'. apply: CASE_APP_spec.
      - do ? (rewrite vec_change_neq; first done). by eassumption.
      - do ? (rewrite vec_change_neq; first done). by eassumption.
      - do ? (rewrite vec_change_neq; first done). by rewrite (vec_change_eq erefl). }
    apply: sss_compute_refl'. by rewrite (counters_eta v).
  - (* case (lam s) *)
    move=> s. case: ts; first done.
    move=> t'' ts'' H1v H2v H3v [<- <- <-].
    exists (vec_change (vec_change (vec_change (vec_change (vec_change v U (enc_term s)) TS (enc_cs ts'')) CTX (enc_cs (t''::ctx))) B 0) A 0).
    split. { move: H1v. by rewrite (counters_eta v). }
    split. { move: H2v. by rewrite (counters_eta v). }
    split. { move: H3v. by rewrite (counters_eta v). }
    apply: sss_progress_compute_trans.
    { apply: (subcode_sss_progress (P := (_, NOOP _))).
      { by eexists [], _. }
      rewrite ?H'. by apply: NOOP_spec. }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
      { by eexists _, _. }
      rewrite ?H'. by apply: (UNPACK_spec H3v). }
    rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= -/enc_term !(vec_norm HAB). }
    rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= !(vec_norm HAB). }
    apply: sss_compute_trans.
    { apply: (subcode_sss_compute (P := (_, CASE_LAM _ _))).
      { eexists _, _. rewrite /PROG. by do 6 rewrite [LHS]app_assoc. }
      rewrite ?H'. apply: CASE_LAM_spec.
      - do ? (rewrite vec_change_neq; first done). by eassumption.
      - do ? (rewrite vec_change_neq; first done). by eassumption.
      - do ? (rewrite vec_change_neq; first done). by rewrite (vec_change_eq erefl). }
    apply: sss_compute_refl'. by rewrite (counters_eta v).
Qed.

Arguments Krivine_step : simpl never.

Lemma simulation {ts ctx t} v : halt_cbn ts ctx t ->
  vec_pos v TS = enc_cs ts ->
  vec_pos v CTX = enc_cs ctx ->
  vec_pos v U = enc_term t ->
  (sss_terminates (@mma_sss _) (1, PROG 1) (1, v)).
Proof.
  have H' : forall n, 1 + n = n + 1 by lia.
  move=> /Krivine_step_spec [k] [ctx'] [t']. elim: k v ts ctx t.
  { move=> v ts ctx t [] -> -> ->.
    rewrite /sss_terminates /sss_output.
    move=> H1v H2v H3v. eexists. split.
    - apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, NOOP _))).
        { by eexists [], _. }
        apply: sss_progress_compute. by apply: NOOP_spec. }
      apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, UNPACK _ _ _))).
        { by eexists _, _. }
        rewrite ?H'. by apply: (UNPACK_spec H3v). }
      rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= -/enc_term !(vec_norm HAB). }
      rewrite ?Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= !(vec_norm HAB). }
      apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, CASE_LAM _ _))).
        { eexists _, _. rewrite /PROG. by do 6 rewrite [LHS]app_assoc. }
        rewrite ?H'. apply: CASE_LAM_spec'.
        do ? (rewrite vec_change_neq; first done). by eassumption. }
      apply: sss_compute_refl.
    - left. rewrite /=. lia. }
  move=> n IH v ts ctx t. rewrite (iter_plus 1 n) /=.
  case E: (Krivine_step _) => [[[ts'' ctx''] t''] | ]; last by rewrite oiter_None.
  move=> IH'.
  move: E => /PROG_spec /[apply] /[apply] /[apply] /(_ 1) [w].
  move=> [+] [+] [+] /sss_progress_compute.
  move: IH' => /(IH w) /[apply] /[apply] /[apply].
  move=> [] st [] + ? /sss_compute_trans H => /H {}H.
  by exists st.
Qed.

Require Import Undecidability.L.Util.L_facts.
Require Import Undecidability.LambdaCalculus.Util.term_facts.
Require Import Undecidability.Shared.Libs.DLW.Code.subcode.

#[local] Notation all := (fold_right and True).

Fixpoint eclosed (u : eterm) :=
  let '(closure ctx t) := u in bound (length ctx) t /\ all (map eclosed ctx).

Lemma Krivine_step_eclosed ts ctx t ts' ctx' t' :
  Krivine_step (ts, ctx, t) = Some (ts', ctx', t') ->
  all (map eclosed ts) -> eclosed (closure ctx t) ->
  all (map eclosed ts') /\ eclosed (closure ctx' t').
Proof.
  rewrite /Krivine_step. case: t.
  - move=> [|n].
    + case: ctx; first done.
      move=> [? ?] ? [<- <- <-] /=. tauto.
    + case: ctx; first done.
      move=> [? ?] ? [<- <- <-] /= ? [/boundE ?] [[]] *.
      split; [done|split;[|done]]. constructor. lia.
  - move=> > [<- <- <-] /= ? [/boundE]. tauto.
  - move=> ?. case: ts; first done.
    move=> > [<- <- <-] /= ? [/boundE]. tauto.
Qed.

(* needs closedness of input so that there are no illegal inputs *)
Lemma inverse_simulation ts ctx t v :
  vec_pos v TS = enc_cs ts ->
  vec_pos v CTX = enc_cs ctx ->
  vec_pos v U = enc_term t ->
  all (map eclosed ts) ->
  eclosed (closure ctx t) ->
  (sss_terminates (@mma_sss _) (1, PROG 1) (1, v)) ->
  halt_cbn ts ctx t.
Proof.
  suff : forall ts ctx t,
  (sss_terminates (@mma_sss _) (1, PROG 1) (1, v)) ->
  all (map eclosed ts) ->
  eclosed (closure ctx t) ->
  vec_pos (snd (1, v)) TS = enc_cs ts ->
  vec_pos (snd (1, v)) CTX = enc_cs ctx ->
  vec_pos (snd (1, v)) U = enc_term t ->
    exists (k : nat) (ctx' : list eterm) (t' : term),
    Nat.iter k (obind Krivine_step) (Some (ts, ctx, t)) =
    Some ([], ctx', lam t').
  { do 6 (move=> /[apply]). by move=> /Krivine_step_spec. }
  move=> {}ts {}ctx {}t [] st [] [k] + Hst.
  elim /(measure_ind id): k ts ctx t v.
  move=> [|k].
  { move=> _ > /sss_steps_0_inv ?. subst st.
    exfalso. move: Hst => /=. lia. }
  move=> IH ts ctx t v HSk.
  case E: (Krivine_step (ts, ctx, t)) => [[[ts'' ctx''] t'']|]; first last.
  { move=> Hts [Ht Hctx] *. move: E. rewrite /Krivine_step -/Krivine_step.
    case: (t) Ht.
    - move=> [|n]; (case: (ctx); last by case); move=> /boundE /=; lia.
    - done.
    - case: (ts); last done. move=> *. by eexists 0, _, _. }
  move: (E) => /Krivine_step_eclosed /[apply] /[apply].
  move=> [] /IH /[apply] {}IH.
  move: (E) => /PROG_spec /[apply] /[apply] /[apply] /(_ 1).
  move=> [w] [+] [+] [+] => /IH /[apply] /[apply] {}IH.
  move: Hst HSk => /subcode_sss_progress_inv /[apply] /[apply].
  move=> /(_ (@mma_defs.mma_sss_fun _) (subcode_refl _)).
  move=> [q] [] /IH /[apply] => - [k'] [ctx'] [t'] Hk'.
  exists (1+k'), ctx', t'. by rewrite iter_plus /= E.
Qed.

Definition input t :=
  0 ## 0 ## 0 ## 0 ## enc_term t ## (Vector.nil _).

End Argument.

Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.L.Util.L_facts.
Require Import Undecidability.LambdaCalculus.Util.term_facts.

Theorem reduction : KrivineMclosed_HALT ⪯ (@MMA_HALTING 5).
Proof.
  exists (fun '(exist _ t _) => 
    (Argument.PROG 1, Argument.input t)).
  move=> [t Ht]. split.
  - move=> /Argument.simulation. by apply.
  - move=> /Argument.inverse_simulation. apply; [done..|].
    split; last done.
    apply /closed_dcl /closed_I.
    move=> ?. by rewrite L_subst_wCBN_subst.
Qed.
