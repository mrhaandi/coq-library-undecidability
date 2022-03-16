(*
reduction from SSTS01 to intersection type inhabitation
*)

Require Import Undecidability.IntersectionTypes.CDV.

Require Import Undecidability.StringRewriting.SSTS.

Require Import List PeanoNat Lia.
Import ListNotations.

Import CDV (var, app, lam).

Require Import ssreflect ssrbool ssrfun.

Section Argument.

Definition bullet := atom 0.
Definition star := atom 1.
(*indicates second symbol*)
Definition hash := atom 2.
(*indicates first symbol*)
Definition dollar := atom 3.
(*indicates very first split, used once*)
Definition triangle := atom 4.
Definition isl := atom 5.
Definition isr := atom 6.

(*encodes elements of the alphabet including 0 and 1*)
Definition symbol (a : nat) := atom (7 + a).

Definition s_init : ty :=
  [arr [hash; dollar] triangle].

Definition s_star : ty := [
  arr [arr [bullet] star] star; 
  arr [arr [isl] star] hash;
  arr [arr [isr] hash; arr [bullet] dollar] dollar].

Definition s_0 : ty :=
  [arr [symbol 0] star; arr [symbol 0] hash; arr [symbol 1] dollar].

Definition s_1 : ty := [symbol 1].

#[local] Notation rule := ((nat * nat) * (nat * nat))%type.

Context (rs : list rule).

Definition symbols :=
  (flat_map (fun '((a,b),(c,d)) => [a; b; c; d]) rs) ++ [0; 1].

Definition s_id_rules : ty :=
  map (fun (a : nat) => (arr [bullet] (arr [symbol a] (symbol a)))) symbols.

Definition s_rule (r : rule) : ty :=
  match r with
  | ((x,y),(x',y')) => 
      (arr [isl] (arr [symbol x'] (symbol x))) ::
      (arr [isr] (arr [symbol y'] (symbol y))) ::
      s_id_rules
  end.

Definition s_pos (i j : nat) : ty := if Nat.eqb i j then [isr] else (if Nat.eqb i (S j) then [isl] else [bullet]).

(*used for initialization, expansion, and termination*)
Definition Γ_init : list ty := [s_init; s_star; s_0; s_1].

Definition Γ_step : list ty := map s_rule rs.

(*information on 'neighboring' environments*)
Definition Γ_lr (bound : nat) (i : nat) : list ty := map (fun j => s_pos i j) (seq 0 bound).

(*collection of all the above type environments*)
Definition Γ_all (bound i : nat) :=
  Γ_lr bound i ++ (Γ_init ++ Γ_step).

Lemma In_nth_In t x (Gamma : list ty) :
  In t (nth x Gamma []) ->
  In (nth x Gamma []) Gamma.
Proof.
  elim: Gamma x. { by case. }
  by move=> > IH [|x] => [|/IH] ?; [left|right].
Qed.

Lemma map_nth' {A B : Type} {f : A -> B} {l : list A} {d : B} {n : nat} (d' : A) :
n < length l -> nth n (map f l) d = f (nth n l d').
Proof.
elim: l n=> /=; first by lia.
move=> ?? IH [|n] ?; first done.
apply: IH. lia.
Qed.

Inductive Γ_all_spec (bound i x : nat) t : Prop :=
  | Γ_all_lr_r : t = isr -> (forall i', nth x (Γ_all bound i') [] = s_pos i' x) -> i = x -> Γ_all_spec bound i x t
  | Γ_all_lr_l : t = isl -> (forall i', nth x (Γ_all bound i') [] = s_pos i' x) -> i = S x -> Γ_all_spec bound i x t
  | Γ_all_lr_bullet : t = bullet -> (forall i', nth x (Γ_all bound i') [] = s_pos i' x) -> i <> x -> i <> S x -> Γ_all_spec bound i x t
  | Γ_all_init_init : t = (arr [hash; dollar] triangle) -> (forall i', nth x (Γ_all bound i') [] = s_init) -> Γ_all_spec bound i x t
  | Γ_all_init_star_star : t = (arr [arr [bullet] star] star) -> (forall i', nth x (Γ_all bound i') [] = s_star) -> Γ_all_spec bound i x t
  | Γ_all_init_star_hash : t = (arr [arr [isl] star] hash) -> (forall i', nth x (Γ_all bound i') [] = s_star) -> Γ_all_spec bound i x t
  | Γ_all_init_star_dollar : t = (arr [arr [isr] hash; arr [bullet] dollar] dollar) -> (forall i', nth x (Γ_all bound i') [] = s_star) -> Γ_all_spec bound i x t
  | Γ_all_init_0_star : t = (arr [symbol 0] star) -> (forall i', nth x (Γ_all bound i') [] = s_0) -> Γ_all_spec bound i x t
  | Γ_all_init_0_hash : t = (arr [symbol 0] hash) -> (forall i', nth x (Γ_all bound i') [] = s_0) -> Γ_all_spec bound i x t
  | Γ_all_init_0_dollar : t = (arr [symbol 1] dollar) -> (forall i', nth x (Γ_all bound i') [] = s_0) -> Γ_all_spec bound i x t
  | Γ_all_init_1 : t = (symbol 1) -> (forall i', nth x (Γ_all bound i') [] = s_1) -> Γ_all_spec bound i x t
  | Γ_all_step_l a b a' b' : t = (arr [isl] (arr [symbol a'] (symbol a))) -> (forall i', nth x (Γ_all bound i') [] = s_rule ((a, b), (a', b'))) -> In ((a, b), (a', b')) rs -> Γ_all_spec bound i x t
  | Γ_all_step_r a b a' b' : t = (arr [isr] (arr [symbol b'] (symbol b))) -> (forall i', nth x (Γ_all bound i') [] = s_rule ((a, b), (a', b'))) -> In ((a, b), (a', b')) rs -> Γ_all_spec bound i x t
  | Γ_all_step_e a b a' b' e : t = (arr [bullet] (arr [symbol e] (symbol e))) -> (forall i', nth x (Γ_all bound i') [] = s_rule ((a, b), (a', b'))) -> In ((a, b), (a', b')) rs -> In e symbols -> Γ_all_spec bound i x t.

Lemma nth_Γ_common x bound i i' :
  x >= length (Γ_lr bound i) ->
  nth x (Γ_all bound i') [] = nth x (Γ_all bound i) [].
Proof.
  move=> Hx. rewrite /Γ_all [LHS](@app_nth2 ty).
  { move: Hx. by rewrite /Γ_lr !map_length !seq_length. }
  rewrite [RHS](@app_nth2 ty); first done.
  by rewrite /Γ_lr !map_length !seq_length.
Qed.

Lemma In_Γ_allE bound i x t :
  In t (nth x (Γ_all bound i) []) ->
  Γ_all_spec bound i x t.
Proof.
  have [|] : x < length (Γ_lr bound i) \/ x >= length (Γ_lr bound i) by lia.
  { rewrite /Γ_lr map_length seq_length => Hx.
    have H'x : forall i', nth x (Γ_all bound i') [] = s_pos i' x.
    { move=> i'. rewrite /Γ_all (@app_nth1 ty). { by rewrite /Γ_lr map_length seq_length. }
      rewrite /Γ_lr (map_nth' 0). { by rewrite seq_length. }
      by rewrite seq_nth. }
    rewrite H'x /s_pos. case Eix: (Nat.eqb i x).
    { case; last done. move=> ?. move=> /Nat.eqb_eq in Eix. subst. by apply: Γ_all_lr_r. }
    case E'ix: (Nat.eqb i (S x)).
    { case; last done. move=> ?. move=> /Nat.eqb_eq in E'ix. subst. by apply: Γ_all_lr_l. }
    case; last done. move=> <-. move=> /Nat.eqb_neq in Eix. move=> /Nat.eqb_neq in E'ix.
    by apply: Γ_all_lr_bullet. }
  rewrite /Γ_all. move=> /[dup] /(@app_nth2 ty) + /nth_Γ_common.
  rewrite /Γ_all. move=> ->. move: (x - _).
  case. { move=> Hx. by do 1 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]). }
  case. { move=> Hx. by do 3 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]). }
  case. { move=> Hx. by do 3 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]). }
  case. { move=> Hx. by do 1 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]). }
  move=> x' /= + /[dup] /In_nth_In. move: (nth x' _ _) => phi Hx'.
  move=> /in_map_iff [[[? ?][? ?]]] /= [?]. move: Hx'. subst phi.
  move=> H'x ? /=.
  do 2 (case; [move=> <-; by eauto using Γ_all_spec, erefl with nocore|]).
  move=> /in_map_iff [?] [<-]. by eauto using Γ_all_spec, erefl with nocore.
Qed.

(*head form : x M1 .. Mn where x is free of bound*)
Inductive normal_form : tm -> Prop :=
  | normal_head : forall M, head_form M -> normal_form M
  | normal_abs : forall M, normal_form M -> normal_form (lam M)
with head_form : tm -> Prop :=
  | head_var : forall x, head_form (var x)
  | head_app : forall M N, head_form M -> normal_form N -> head_form (app M N).

Lemma type_assignmentE Gamma M t : type_assignment Gamma M t ->
  match M with
  | var x => In t (nth x Gamma nil)
  | lam M' => 
    match t with
    | atom _ => False
    | arr phi' t' => type_assignment (phi' :: Gamma) M' t'
    end
  | app M' N' => exists phi',
      type_assignment Gamma M' (arr phi' t) /\ Forall (type_assignment Gamma N') phi'
  end.
Proof. by case=> *; do ? eexists; eassumption. Qed.

(*
Lemma type_assignmentE' Gamma M t : type_assignment Gamma M t ->
  match M with
  | var x => In t (nth x Gamma nil)
  | lam M' => 
      match t with
      | atom _ => False
      | arr phi' t' => type_assignment (phi' :: Gamma) M' t'
      end
  | app M' N' => exists phi',
      type_assignment Gamma M' (arr phi' t) /\ Forall (type_assignment Gamma N') phi'
  end.
Proof. by case=> *; do ? eexists; eassumption. Qed.
*)
(*
Lemma In_nthE t x (Gamma : list ty) :
  In t (nth x Gamma []) ->
  exists phi, In phi Gamma /\ In t phi.
Proof.
  move=> /[dup] /In_nth_In *. eexists. by split; eassumption. 
Qed.

Lemma InΓ_stepE t x :
  In t (nth x Γ_step []) ->
  exists r, In t (s_rule r) /\ In r rs.
Proof. 
  move=> /In_nthE [?] [/in_map_iff] [r] [<-] *. by exists r. 
Qed.

Lemma InΓ_lrE t x bound i :
  In t (nth x (Γ_lr bound i) []) ->
  exists j, In t (s_pos i j) /\ j < bound.
Proof.
  move=> /In_nthE [?] [/in_map_iff] [j] [<-] /in_seq [? ?] ?. by exists j.
Qed.
*)

(*only s_rule can be used deriving a type with two parameters for a normal form*)
Lemma two_params_rule (bound i: nat) N (phi psi : ty) (s : sty) :
  head_form N ->
  type_assignment (Γ_all bound i) N (arr phi (arr psi s)) ->
  (exists x (e : nat), N = var x /\ s = symbol e).
Proof.
  move=> H. elim: H phi psi s.
  { move=> x > /type_assignmentE.
    move=> /In_Γ_allE [] // > [] *; subst; by eexists _, _. }
  move=> > ? IH ? > /type_assignmentE - [phi'] [] /IH.
  firstorder done.
Qed.

Lemma nf_hf_atom Gamma N a :
  normal_form N ->
  type_assignment Gamma N (atom a) ->
  head_form N.
Proof.
  case; [done|]. by move=> ?? /type_assignmentE.
Qed.

(*if triangle is inhabited in (Γ_init ++ Γ_step rs), then hash, dollar is inhabited in (Γ_all rs 0 0)*)
Lemma soundness_init (N : tm) :
  head_form N ->
  type_assignment (Γ_init ++ Γ_step) N triangle ->
  exists (N' : tm), head_form N' /\
  type_assignment (Γ_all 0 0) N' hash /\
  type_assignment (Γ_all 0 0) N' dollar.
Proof.
  case.
  { by move=> x /type_assignmentE /(In_Γ_allE 0 0) []. }
  move=> ? N' []; first last.
  { move=> > /two_params_rule H ??.
    move=> /type_assignmentE [?] [/type_assignmentE] [?] [].
    by move=> /(H 0 0) [?] [?] []. }
  move=> ?? /type_assignmentE [?] [] /type_assignmentE /(In_Γ_allE 0 0) [] //.
  move=> [->] ? /Forall_cons_iff [?] /Forall_cons_iff [? _].
  exists N'. split; last done.
  apply: nf_hf_atom; by eassumption.
Qed.

Fixpoint tm_size (M : tm) :=
  match M with
  | var _ => 1
  | app M' N' => 1 + tm_size M' + tm_size N'
  | lam M' => 1 + tm_size M'
  end.

(* induction/recursion principle wrt. a decreasing measure f *)
(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
(forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

(*
(* TODO later extend to necessary types *)
Lemma hash_spec phi x bound i :
  In (arr phi hash) (nth x (Γ_all bound i) []) ->
  nth x (Γ_all bound i) [] = s_0 \/ nth x (Γ_all bound i) [] = s_star.
Proof.
  move=> /[dup] /In_nth_In. move: (nth x _ _) => psi.
  move=> /in_app_iff [].
  { move=> /in_map_iff [?] [<-] _. rewrite /s_pos.
    do 2 (case: (Nat.eqb _ _); [by case|]). by case. }
  move=> /in_app_iff [] /=; first last.
  { move=> /in_map_iff [[[? ?][? ?]]] [<- _] /=.
    do 4 (case; [done|]).
    by move=> /in_map_iff [?] []. }
  intuition subst; firstorder done.
Qed.
*)

(*
Lemma In_atom_Gamma a x bound i : In (atom a) (nth x (Γ_all bound i) []) ->
  atom a = symbol 1 \/ atom a = isl \/ atom a = isr \/ atom a = bullet.
Proof.
  move=> /In_nthE [?] [/in_app_iff] [].
  { move=> /in_map_iff [?] [<-] _. rewrite /s_pos.
Admitted.
*)

(*
NEEDS PREDICATE FOR IN GAMMA
*)
(*if stars, hash, dollar is inhabited in (Γ_all rs bound [0 .. 1+bound]), then 0 is inhabited in (Γ_all rs bound [0 .. bound'])*)
Lemma soundness_expand (bound : nat) (N : tm) :
  head_form N ->
  Forall (fun Γi => type_assignment Γi N star) (map (Γ_all bound) (seq 0 bound)) ->
  type_assignment (Γ_all bound 0) N hash ->
  type_assignment (Γ_all bound (1+bound)) N dollar ->
  exists bound' N',
    head_form N' /\
    Forall (fun Γi => type_assignment Γi N' (symbol 0)) (map (Γ_all bound') (seq 0 (1+bound'))).
Proof.
  elim /(measure_rect tm_size): N bound.
  move=> ? + bound Hx. case: Hx.
  { by move=> ? IH ? /type_assignmentE /In_Γ_allE []. }
  move=> M N []; first last.
  { move=> > /two_params_rule H ???? /type_assignmentE [?] [/type_assignmentE] [?] [].
    by move=> /H [?] [?] []. }
  move=> ? H0N IH IH' /type_assignmentE [?] [/type_assignmentE].
  move=> /In_Γ_allE [] //.
  - move=> [->] Hx /Forall_cons_iff [H1N _].
    move: H0N IH IH' H1N => [].
    { move=> ? [].
      - by move=> ??? /type_assignmentE /In_Γ_allE [].
      - by move=> > /two_params_rule H ??? /type_assignmentE [?] [/H] [?] [?] []. }
    move=> N' H0N' IH IH' /type_assignmentE H1N'.
    move=> /type_assignmentE [?] [/type_assignmentE].
    rewrite Hx. case; [done|case;[done|case;[|done]]].
    move=> [<-] /Forall_cons_iff [/type_assignmentE H2N'] /Forall_cons_iff [/type_assignmentE H3N' _].
    have /= := IH N' _ (S bound). case.
    TODO

