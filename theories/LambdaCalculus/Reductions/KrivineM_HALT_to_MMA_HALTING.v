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

(* auxiliary counters *)
Notation A := (Fin.F1 : counter).
Notation B := (Fin.FS (Fin.F1) : counter).
Notation C := (Fin.FS (Fin.FS (Fin.F1)) : counter).
(* data counters *)
Notation TS := (Fin.FS (Fin.FS (Fin.FS (Fin.F1))) : counter).
Notation CTX := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))) : counter).
Notation U := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))) : counter).

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
    by rewrite [i in vec_change v X i](esym En) vec_change_same.
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
  rewrite vec_change_idem vec_change_same.
  by apply: sss_compute_refl.
Qed.

Arguments ZERO : simpl never.
Arguments plus : simpl never.

(* Y := X + Y *)
Definition MOVE (X Y: counter) (offset: nat) : list mm_instr :=
  JMP (3+offset) offset ++ [INC Y; DEC X (2+offset)].

Definition MOVE_length := JMP_length+2.

Arguments vec_change_neq {X n v p q x}.
Arguments vec_change_eq {X n v p q x}.

Lemma asd (P : counter -> Prop) : 
  P A -> P B -> P C -> P TS -> P CTX -> P U -> forall (X : counter), P X.
Proof.
Admitted.

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
    rewrite Nat.add_0_r. rewrite vec_change_same.
    by rewrite [i in vec_change v X i](esym En) vec_change_same.
  - move=> n IH v En w <-.
    apply: Q_step_spec'. { by rewrite /= En. }
    apply: Q_step_spec'. { done. }
    apply: IH.
    + by rewrite (vec_change_neq (nesym HXY)) vec_change_eq.
    + apply: vec_pos_ext => Z.
      case: (pos_eq_dec X Z); case: (pos_eq_dec Y Z).
      * move=> ??. by subst.
      * move=> ? <-. by rewrite !(vec_change_eq erefl).
      * move=> <- ?. rewrite !(vec_change_neq (HXY)) !(vec_change_eq erefl). lia.
      * move=> HYZ HXZ. by rewrite !(vec_change_neq (HXZ)) !(vec_change_neq (HYZ)) !(vec_change_neq (HXZ)).
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
      by rewrite [i in vec_change v'' X i](esym En) !vec_change_same.
    - move=> n IH v'' En x w ->.
      rewrite !Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= En. }
      rewrite !Nat.add_assoc. apply: Q_step_spec'. { done. }
      apply: Q_step_spec'. { done. }
      apply: IH.
      + by rewrite !(vec_change_neq HX) vec_change_eq.
      + apply: vec_pos_ext => Z.
        case: (pos_eq_dec X Z); case: (pos_eq_dec A Z).
        * move=> ??. by subst.
        * move=> ? <-. by do ? rewrite ?(vec_change_eq erefl) ?(vec_change_neq HX).
        * move=> <- ?. do ? rewrite ?(vec_change_eq erefl) ?(vec_change_neq (nesym HX)). lia.
        * move=> HAZ HXZ. by do ? rewrite ?(vec_change_neq (HXZ)) ?(vec_change_neq (HAZ)). }
  move=> /(_ _ erefl) /sss_compute_trans. apply.
  apply: sss_compute_trans.
  { apply: (subcode_sss_compute (P := (_, MOVE _ _ _))).
    { rewrite /= /DOUBLE. do 2 eexists. by do 2 rewrite [LHS]app_assoc. }
      rewrite ?H'. by apply: MOVE_spec. }
  apply: sss_compute_refl'. congr pair.
  rewrite -Ev'. apply: vec_pos_ext => Z.
  case: (pos_eq_dec X Z); case: (pos_eq_dec A Z).
  - move=> ??. by subst.
  - move=> ? <-. do ? rewrite ?(vec_change_eq erefl) ?(vec_change_neq HX). lia.
  - move=> <- ?. by do ? rewrite ?(vec_change_eq erefl) ?(vec_change_neq (nesym HX)).
  - move=> HAZ HXZ. by do ? rewrite ?(vec_change_neq (HXZ)) ?(vec_change_neq (HAZ)).
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

(* TODO use universaly *)
Definition simpl_vec_change {X Y : counter} (HXY : X <> Y) :=
  (fun v n => @vec_change_neq nat _  v X Y n HXY,
   fun v n => @vec_change_neq nat _  v Y X n (nesym HXY),
   fun v n => @vec_change_eq nat _  v X X n erefl,
   fun v n => @vec_change_eq nat _  v Y Y n erefl).

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
      have -> : (vec_pos v'' X) * 2 ^ 0 = vec_pos v'' X by simpl; lia.
      apply: vec_pos_ext => Z. case: (pos_eq_dec X Z).
      { move=> <-. by do ? rewrite ?(simpl_vec_change HX). }
      move=> HXZ. case: (pos_eq_dec Y Z).
      { move=> <-. by do ? rewrite ?(simpl_vec_change HY) ?(simpl_vec_change HXY). }
      move=> HYZ. case: (pos_eq_dec A Z).
      { move=> <-. by do ? rewrite ?(simpl_vec_change HX) ?(simpl_vec_change HY). }
      move=> HAZ.
      by do ? rewrite ?(simpl_vec_change HX) ?(simpl_vec_change HY) ?(simpl_vec_change HXY) ?(simpl_vec_change HAZ) ?(simpl_vec_change HXZ) ?(simpl_vec_change HYZ).
    - move=> n IH v'' En HAv'' w ->.
      rewrite !Nat.add_assoc. apply: Q_step_spec'. { by rewrite /= En. }
      apply: sss_compute_trans.
      { apply: (subcode_sss_compute (P := (_, DOUBLE _ _))).
        { do 2 eexists. rewrite /PACK. by do 2 rewrite app_assoc. }
        rewrite ?H'. by apply: DOUBLE_spec. }
      apply: IH.
      + by rewrite !(vec_change_neq HY) !(vec_change_neq HXY) vec_change_eq.
      + by rewrite vec_change_eq.
      + apply: vec_pos_ext => Z.
        case: (pos_eq_dec X Z); case: (pos_eq_dec Y Z).
        * move=> ??. by subst.
        * move=> ? <-. do ? rewrite ?(vec_change_eq erefl) ?(vec_change_neq HX) ?(vec_change_neq (nesym HXY)) /=.
          lia.
        * move=> <- ?. by do ? rewrite ?(vec_change_eq erefl) ?(vec_change_neq HXY) ?(vec_change_neq (nesym HXY)).
        * move=> HYZ HXZ. do ? rewrite ?(vec_change_neq (HXZ)) ?(vec_change_neq (HYZ)) ?(vec_change_neq (nesym HXY)).
          case: (pos_eq_dec A Z).
          ** move=> <-. by rewrite ?(vec_change_eq erefl).
          ** move=> HAZ. by rewrite ?(vec_change_neq (HAZ)) ?(vec_change_neq (HXZ)) ?(vec_change_neq (HYZ)). }
  move=> /(_ _ erefl) /sss_compute_trans. apply.
  apply: sss_compute_refl'. congr pair.
  rewrite -Ev'. apply: vec_pos_ext => Z.
  case: (pos_eq_dec X Z).
  { move=> <-. do ? rewrite ?(simpl_vec_change HX) ?(simpl_vec_change HY) ?(simpl_vec_change HXY). lia. }
  move=> HXZ. case: (pos_eq_dec Y Z).
  { move=> <-. by do ? rewrite ?(simpl_vec_change HY) ?(simpl_vec_change HXY). }
  move=> HYZ. case: (pos_eq_dec A Z).
  { move=> <-. by do ? rewrite ?(simpl_vec_change HX) ?(simpl_vec_change HY) ?(simpl_vec_change HXY). }
  move=> HAZ.
  by do ? rewrite ?(simpl_vec_change HX) ?(simpl_vec_change HY) ?(simpl_vec_change HXY) ?(simpl_vec_change HAZ) ?(simpl_vec_change HXZ) ?(simpl_vec_change HYZ).
Qed.

