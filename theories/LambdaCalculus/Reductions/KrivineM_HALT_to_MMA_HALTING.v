(* TODO move to MinskyMachines *)
From Undecidability Require Import
  LambdaCalculus.Krivine MinskyMachines.MM.
From Undecidability.Shared.Libs.DLW
  Require Import Vec.pos Vec.vec Code.sss.

Require Import PeanoNat List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.

#[local] Notation mm_instr := (mm_instr (pos 6)).
#[local] Notation counter := (pos 6).
#[local] Notation mm_state := (mm_state 6).

#[local] Notation "P // s -[ k ]-> t" := (sss_steps (@mma_sss _) P k s t).
#[local] Notation "P // s ->> t" := (sss_compute (@mma_sss _) P s t).
#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

#[local] Arguments vec_change_neq {X n v p q x}.
#[local] Arguments vec_change_eq {X n v p q x}.

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
Notation C := (Fin.FS (Fin.FS (Fin.F1)) : counter).
(* data counters *)
Notation TS := (Fin.FS (Fin.FS (Fin.FS (Fin.F1))) : counter).
Notation CTX := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) : counter).
Notation U := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))) : counter).

(* simplify vec_change statements *)
Definition vec_norm {X Y: counter} (HXY : X <> Y) := (
  fun v n m => @vec_change_comm nat _ v X Y n m HXY,
  fun v n m => @vec_change_idem nat _ v X n m,
  fun v n m => @vec_change_idem nat _ v Y n m,
  fun v n => @vec_change_neq nat _  v X Y n HXY,
  fun v n => @vec_change_neq nat _  v Y X n (nesym HXY),
  fun v n => @vec_change_eq nat _  v X X n erefl,
  fun v n => @vec_change_eq nat _  v Y Y n erefl).

Definition Q_step (Q : list mm_instr) (offset i : nat) (v : vec nat 6) : option mm_state :=
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
  sss_step (mma_sss (n:=6)) (offset, Q) (i + offset, v) (j, w).
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

Lemma asd (P : counter -> Prop) : 
  P A -> P B -> P C -> P TS -> P CTX -> P U -> forall (X : counter), P X.
Proof.
Admitted.

(* TODO use universaly 
Definition simpl_vec_change {X Y : counter} (HXY : X <> Y) :=
  (fun v n => @vec_change_neq nat _  v X Y n HXY,
   fun v n => @vec_change_neq nat _  v Y X n (nesym HXY),
   fun v n => @vec_change_eq nat _  v X X n erefl,
   fun v n => @vec_change_eq nat _  v Y Y n erefl).
*)



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

Fixpoint half (n: nat) : nat + nat :=
  match n with
  | 0 => inl 0
  | S n' => 
      match half n' with
      | inl m => inr m
      | inr m => inl (S m)
      end
  end.

Lemma half_spec n : 
  match half n with
  | inl m => n = m + m
  | inr m => n = 1 + m + m
  end.
Proof. elim: n => [|n] /=; [done|case: (half n); lia]. Qed.

Lemma sig_half (n: nat) : { m | n = m + m } + { m | n = 1 + m + m }.
Proof.
  elim : n. { left. by exists 0. }
  move=> n [[m Hm]|[m Hm]].
  - right. exists m. lia.
  - left. exists (S m). lia.
Qed.

(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_ind (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Lemma HALF_spec X p q v offset :
  let x := vec_pos v X in let a := vec_pos v A in
  A <> X ->
  (offset, HALF X p q offset) // (offset, v) ->>
    match half x with
    | inl m => (p, vec_change (vec_change v X (a+m)) A 0)
    | inr m => (q, vec_change (vec_change v X (a+m)) A 0)
    end.
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
  have := half_spec n. case: (half n).
  - move=> m ?. rewrite !(vec_norm HX). congr pair. congr vec_change. congr vec_change. lia.
  - move=> m ?. rewrite !(vec_norm HX). congr pair. congr vec_change. congr vec_change. lia.
Qed.
