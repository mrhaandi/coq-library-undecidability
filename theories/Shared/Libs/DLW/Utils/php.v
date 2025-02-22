(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Ralph Matthes [+]                              *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation IRIT -- CNRS   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(* * Pigeonhole principle *)

From Stdlib Require Import Arith Lia List Permutation Relations.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70, no associativity).

Section incl.

  Variable X : Type.
  
  Implicit Type l : list X.
  
  Fact incl_cons_linv l m x : incl (x::m) l -> In x l /\ incl m l.
  Proof.
    intros H; split.
    + apply H; left; auto.
    + intros ? ?; apply H; right; auto.
  Qed.

  Fact incl_app_rinv l m p : incl m (l++p) -> exists m1 m2, m ~p m1++m2 /\ incl m1 l /\ incl m2 p.
  Proof.
    induction m as [ | x m IHm ].
    + exists nil, nil; simpl; repeat split; auto; intros ? [].
    + intros H.
      apply incl_cons_linv in H.
      destruct H as (H1 & H2).
      destruct (IHm H2) as (m1 & m2 & H3 & H4 & H5).
      apply in_app_or in H1; destruct H1.
      * exists (x::m1), m2; repeat split; auto.
        - constructor 2; auto.
        - intros ? [|]; subst; auto.
      * exists m1, (x::m2); repeat split; auto.
        - apply Permutation_cons_app; auto.
        - intros ? [|]; subst; auto.
  Qed.
  
  Fact incl_cons_rinv x l m : incl m (x::l) -> exists m1 m2, m ~p m1 ++ m2 /\ Forall (eq x) m1 /\ incl m2 l.
  Proof.
    intros H.
    apply (@incl_app_rinv (x::nil) _ l) in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    exists m1, m2; repeat split; auto.
    rewrite Forall_forall.
    intros a Ha; apply H2 in Ha; destruct Ha as [ | [] ]; auto.
  Qed.

  Fact incl_right_cons_choose x l m : incl m (x::l) -> In x m \/ incl m l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as ( m1 & m2 & H1 & H2 & H3 ); simpl in H1.
    destruct m1 as [ | y m1 ].
    + right.
      intros u H; apply H3; revert H.
      apply Permutation_in; auto.
    + left.
      apply Permutation_in with (1 := Permutation_sym H1).
      rewrite Forall_forall in H2.
      rewrite (H2 y); left; auto.
  Qed.

  Fact incl_left_right_cons x l y m : incl (x::l) (y::m) -> y = x  /\ In y l 
                                                         \/ y = x  /\ incl l m
                                                         \/ In x m /\ incl l (y::m).
  Proof.
    intros H; apply incl_cons_linv in H.
    destruct H as [ [|] H2 ]; auto.
    apply incl_right_cons_choose in H2; tauto.
  Qed.

  Fact perm_incl_left m1 m2 l: m1 ~p m2 -> incl m2 l -> incl m1 l.
  Proof. intros H1 H2 ? H. apply H2; revert H; apply Permutation_in; auto. Qed.

  Fact perm_incl_right m l1 l2: l1 ~p l2 -> incl m l1 -> incl m l2.
  Proof.
    intros H1 H2 ? ?; apply Permutation_in with (1 := H1), H2; auto.
  Qed.
  
End incl.

Section Permutation_tools.

  Variable X : Type.
  
  Implicit Types (l : list X).
  
  Theorem Permutation_In_inv l1 l2: l1 ~p l2 -> forall x, In x l1 -> exists l, exists r, l2 = l++x::r.
  Proof. intros H ? ?; apply in_split, Permutation_in with (1 := H); auto. Qed.
  
  Fact perm_in_head x l : In x l -> exists m, l ~p x::m.
  Proof.
    induction l as [ | y l IHl ].
    + destruct 1.
    + intros [ ? | H ]; subst.
      * exists l; apply Permutation_refl.
      * destruct (IHl H) as (m & Hm).
        exists (y::m).
        apply Permutation_trans with (2 := perm_swap _ _ _).
        constructor 2; auto.
  Qed.

End Permutation_tools.

Section pigeon_list.

  Variable (X : Type).

  Implicit Types (l m : list X).
  
  Inductive list_has_dup : list X -> Prop :=
    | in_list_hd0 : forall l x, In x l -> list_has_dup (x::l)
    | in_list_hd1 : forall l x, list_has_dup l -> list_has_dup (x::l).
  
  Fact list_hd_cons_inv x l : list_has_dup (x::l) -> In x l \/ list_has_dup l.
  Proof. inversion 1; subst; auto. Qed.

  Definition list_has_dup_cons_inv := list_hd_cons_inv.

  Fact list_has_dup_cons_iff x l : list_has_dup (x::l) <-> In x l \/ list_has_dup l.
  Proof.
    split.
    + apply list_hd_cons_inv.
    + intros []; [ constructor 1 | constructor 2 ]; auto.
  Qed.
  
  Fact list_has_dup_app_left l m : list_has_dup m -> list_has_dup (l++m).
  Proof. induction l; simpl; auto; constructor 2; auto. Qed.
  
  Fact list_has_dup_app_right l m : list_has_dup l -> list_has_dup (l++m).
  Proof. 
    induction 1; simpl.
    + constructor 1; apply in_or_app; left; auto.
    + constructor 2; auto.
  Qed.

  Fact perm_list_has_dup l m : l ~p m -> list_has_dup l -> list_has_dup m.
  Proof.
    induction 1 as [ | x l m H1 IH1 | x y l | ]; auto; 
      intros H; apply list_hd_cons_inv in H.
    + destruct H as [ H | H ].
      * apply Permutation_in with (1 := H1) in H.
        apply in_list_hd0; auto.
      * apply in_list_hd1; auto.
    + destruct H as [ [ H | H ] | H ]; subst.
      * apply in_list_hd0; left; auto.
      * apply in_list_hd1, in_list_hd0; auto.
      * apply list_hd_cons_inv in H.
        destruct H as [ H | H ].
        - apply in_list_hd0; right; auto.
        - do 2 apply in_list_hd1; auto.
  Qed.

  Fact list_has_dup_swap x y l : list_has_dup (x::y::l) -> list_has_dup (y::x::l).
  Proof. apply perm_list_has_dup; constructor. Qed.

  Fact list_has_dup_app_inv l m : list_has_dup (l++m) -> list_has_dup l 
                                                      \/ list_has_dup m 
                                                      \/ exists x, In x l /\ In x m. 
  Proof.
    induction l as [ | x l IHl ]; simpl; intros H; auto.
    apply list_hd_cons_inv in H.
    + destruct H as [ H | H ].
      * apply in_app_or in H; destruct H as [ H | H ].
        - left; constructor; auto.
        - do 2 right; exists x; simpl; auto.
      * destruct (IHl H) as [ H1 | [ H1 | (y & H1 & H2) ] ]; auto.
        - left; constructor 2; auto.
        - do 2 right; exists y; simpl; auto.
  Qed.

  Fact list_has_dup_eq_duplicates m: list_has_dup m <-> exists x aa bb cc, m = aa++x::bb++x::cc.
  Proof.
    split.
    + induction 1 as [ m x Hm | m x _ IHm ].
      - apply in_split in Hm.
        destruct Hm as (bb & cc & Hm).
        exists x, nil, bb, cc; subst; auto.
      - destruct IHm as (y & aa & bb & cc & IHm).
        exists y, (x::aa), bb, cc; subst; auto.
    + intros (x & aa & bb & cc & Hm).
      subst m.
      apply list_has_dup_app_left.
      constructor 1; apply in_or_app; right.
      constructor 1; reflexivity.
  Qed.

  Definition list_has_dup_equiv := list_has_dup_eq_duplicates.

  Fact repeat_choice_two x m : Forall (eq x) m -> (exists m', m = x::x::m') \/ m = nil \/ m = x::nil.
  Proof.
    intros H.
    destruct m as [ | a [ | b m ] ]; auto.
    + inversion H; subst; auto.
    + rewrite Forall_forall in H.
      rewrite <- (H a), <- (H b); simpl; auto; left; exists m; auto.
  Qed.

  (* If m in included in x::l then 
       a) either m is included in l
       b) or m has a duplicate (x but that does not matter here)
       c) or m is permutable with x::m' with m' included in l
   *)

  Fact incl_right_cons_incl_or_lhd_or_perm m x l : 
       incl m (x::l) -> incl m l 
                     \/ list_has_dup m 
                     \/ exists m', m ~p x::m' /\ incl m' l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    destruct (repeat_choice_two H2) as [ (?&?) | [|] ]; 
      subst m1; simpl in H1; clear H2.
    + right; left; apply perm_list_has_dup with (1 := Permutation_sym H1), in_list_hd0; left; auto.
    + left; revert H1 H3; apply perm_incl_left.
    + firstorder.
  Qed.

  Fact incl_left_right_php x l y m : incl (y::m) (x::l) -> list_has_dup (y::m)
                                                        \/ x = y  /\ incl m l
                                                        \/ In y l /\ incl m l
                                                        \/ In y l /\ exists m', m ~p x::m' /\ incl m' l.
  Proof.
    intros H; apply incl_left_right_cons in H.
    destruct H as [ (? & ?) | [ (? & ?) | (H1 & H2) ] ]; subst; auto.
    + left; apply in_list_hd0; auto.
    + apply incl_right_cons_incl_or_lhd_or_perm in H2; firstorder.
      left; apply in_list_hd1; auto.
  Qed.

  (* length_le_and_incl_implies_dup_or_perm is a generalisation of the PHP
      for which the inductive case works w/o needing decidable equality  

      A shorter proof

      The proof is by induction on l
   *)

  (* ** Generalized statement *)

  Lemma length_le_and_incl_implies_dup_or_perm l m :  
            length l <= length m 
         -> incl m l 
         -> list_has_dup m \/ m ~p l.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros m; simpl; intros H1 H2; auto.
    + destruct m as [ | y ]; auto; destruct (H2 y); simpl; auto.
    + destruct incl_right_cons_incl_or_lhd_or_perm with (1 := H2)
        as [ H3 | [ H3 | (m' & H3 & H4) ] ]; auto.
      * destruct IHl with (2 := H3) as [ | H ]; try lia; auto.
        apply Permutation_length in H; lia.
      * destruct IHl with (2 := H4) as [ H | H ]; try (simpl; lia).
        - apply Permutation_length in H3; simpl in H3; lia.
        - left; apply perm_list_has_dup with (1 := Permutation_sym H3).
          constructor 2; auto.
        - right; apply perm_trans with (1 := H3); auto.
  Qed. 

  (* If  m is strictly longer than l 
      and m is (set) included in l
      then it has a duplicate 

      This proof does not require weakly decidable equality
      and it does not find where is the duplicate
    *)

  Theorem finite_php_dup l m : length l < length m
                            -> incl m l 
                            -> list_has_dup m.
  Proof.
    intros H1 H2.
    destruct (@length_le_and_incl_implies_dup_or_perm l m) as [ | H3 ]; auto; try lia.
    apply Permutation_length in H3; lia.
  Qed. 

  (* ** The Finite PHP on lists of the same type *)

  Theorem finite_pigeon_hole l m :
         length l < length m 
      -> incl m l 
      -> exists x aa bb cc, m = aa++x::bb++x::cc.
  Proof.
    intros; apply list_has_dup_eq_duplicates, finite_php_dup with l; auto.
  Qed.

  Theorem partition_intersection l m k :
           length k < length (l++m)
        -> incl (l++m) k
        -> list_has_dup l 
        \/ list_has_dup m 
        \/ exists x, In x l /\ In x m. 
  Proof.
    intros H1 H2.
    apply list_has_dup_app_inv, list_has_dup_eq_duplicates.
    revert H1 H2; apply finite_pigeon_hole.
  Qed.

End pigeon_list.

Fact not_list_has_dup_an a n : ~ list_has_dup (list_an a n).
Proof.
  revert a; induction n as [ | n IHn ]; simpl; intros a H.
  + inversion H.
  + apply list_hd_cons_inv in H.
    rewrite list_an_spec in H.
    destruct H as [ | H ]; try lia.
    revert H; apply IHn.
Qed.

Fact list_has_dup_map_inv X Y (f : X -> Y) l : 
           (forall x y, In x l -> In y l -> f x = f y -> x = y) 
        -> list_has_dup (map f l) 
        -> list_has_dup l.
Proof.
  intros H; do 2 rewrite list_has_dup_eq_duplicates.
  intros (y & m1 & m2 & m3 & E).
  apply map_app_inv in E; destruct E as (l1 & l10 & H1 & H2 & H3); symmetry in H3.
  apply map_cons_inv in H3; destruct H3 as (x1 & l11 & H3 & H4 & H5).
  apply map_app_inv in H5; destruct H5 as (l2 & l12 & H5 & H6 & H7); symmetry in H7.
  apply map_cons_inv in H7; destruct H7 as (x2 & l3 & H7 & H8 & H9); subst.
  apply H in H8; subst.
  + exists x1, l1, l2, l3; auto.
  + apply in_or_app; right; right; simpl.
    apply in_or_app; simpl; auto.
  + apply in_or_app; simpl; auto.
Qed.

Fact not_list_an_has_dup a n : ~ list_has_dup (list_an a n).
Proof.
  revert a; induction n as  [ | n IHn ]; simpl; intros a H.
  + inversion H.
  + apply list_hd_cons_inv in H.
    rewrite list_an_spec in H.
    destruct H as [ | H ]; try lia.
    revert H; apply IHn.
Qed.

Fact list_exists X Y (R : X -> Y -> Prop) l : (forall x, In x l -> exists y, R x y) -> exists ll, Forall2 R l ll.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  exists nil; constructor.
  destruct (Hl x) as (y & Hy).
  left; auto.
  destruct IHl as (ll & Hll).
  intros; apply Hl; right; auto.
  exists (y::ll); constructor; auto.
Qed.

Fact Forall2_conj X Y (R S : X -> Y -> Prop) ll mm : Forall2 (fun x y => R x y /\ S x y) ll mm <-> Forall2 R ll mm /\ Forall2 S ll mm.
Proof.
  split.
  induction 1; split; constructor; tauto.
  intros [H1 H2]; revert H1 H2.
  induction 1 as [ | x ll y mm H1 H2 IH ]; intros H; auto.
  apply Forall2_cons_inv in H; constructor; tauto.
Qed.

Fact Forall2_length X Y (R : X -> Y -> Prop) l m : Forall2 R l m -> length l = length m.
Proof. induction 1; simpl; f_equal; auto. Qed.

Fact Forall2_impl X Y (R S : X -> Y -> Prop) : 
     (forall x y, R x y -> S x y) -> forall l m, Forall2 R l m -> Forall2 S l m.
Proof. induction 2; constructor; auto. Qed.

Fact Forall2_right_Forall X Y (P : Y -> Prop) lx ly : Forall2 (fun (_ : X) y => P y) lx ly <-> Forall P ly /\ length lx = length ly.
Proof.
  split.
  intros H; split.
  induction H; constructor; auto.
  revert H; apply Forall2_length.
  intros (H1 & H2); revert lx H2.
  induction H1; intros [ | ] H2; try discriminate H2; constructor; auto.
Qed.

Fact Forall2_app_inv_r X Y R l m1 m2 : 
       @Forall2 X Y R l (m1++m2) 
    -> { l1 : _ & { l2 | Forall2 R l1 m1 /\ Forall2 R l2 m2 /\ l = l1++l2 } }.
Proof.
  revert m2 l;
  induction m1 as [ | y m1 IH ]; simpl; intros m2 l H.
  exists nil, l; repeat split; auto.
  destruct l as [ | x l ].
  apply Forall2_nil_inv_l in H; discriminate H.
  apply Forall2_cons_inv in H; destruct H as [ H1 H2 ].
  apply IH in H2.
  destruct H2 as (l1 & l2 & H2 & H3 & H4); subst l.
  exists (x::l1), l2; repeat split; auto.
Qed.

Section PHP_rel.
  
  Variable (U V : Type) (R : U -> V -> Prop) (l : list U) (m : list V) 
                        (HR : forall x, In x l -> exists y, In y m /\ R x y).
                          
  Let image_R_l : exists Rl, incl Rl m /\ Forall2 R l Rl.
  Proof.
    destruct (list_exists _ l HR) as (Rl & HRl).
    exists Rl; split.
    + clear HR.
      rewrite Forall2_conj in HRl.
      apply proj1, Forall2_right_Forall, proj1 in HRl.
      rewrite Forall_forall in HRl; auto.
    + revert HRl; apply Forall2_impl; tauto.
  Qed.

  Hypothesis (Hlm : length m < length l).

  (* ** The finite relational PHP *)
                          
  Theorem PHP_rel : exists a x b y c v, l = a++x::b++y::c
                                       /\ In v m /\ R x v /\ R y v.
  Proof using Hlm image_R_l.
    destruct image_R_l as (Rl & H1 & H2).
    destruct finite_pigeon_hole with (2 := H1) as (v & x & y & z & H).
    + apply Forall2_length in H2; lia.
    + subst Rl.
      apply Forall2_app_inv_r in H2; destruct H2 as (x' & l1 & H3 & H2 & ?); subst.
      apply Forall2_cons_inv_r in H2; destruct H2 as (v' & l2 & H4 & ? & H2); subst.
      apply Forall2_app_inv_r in H2; destruct H2 as (y' & l3 & H5 & H2 & ?); subst.
      apply Forall2_cons_inv_r in H2; destruct H2 as (v'' & l4 & H6 & ? & H2); subst.
      exists x', v', y', v'', l4, v; repeat (split; auto).
      apply H1, in_or_app; simpl; auto.
  Qed.

End PHP_rel.

Section php_upto.

  (* If R is a partial equivalence relation, l is a
      list contained in the list m (upto R), and m is 
      shorter than l, then l contains a duplicate upto R *)

  Theorem php_upto X (R : X -> X -> Prop) (l m : list X) :
            symmetric _ R -> transitive _ R                  (* PER *)
         -> (forall x, In x l -> exists y, In y m /\ R x y)  (* l contained in m *)
         -> length m < length l                              (* shorter *)
         -> exists a x b y c, l = a++x::b++y::c /\ R x y.    (* duplicate *)
  Proof.
    intros HR1 HR2 H1 H2.
    destruct PHP_rel with (R := R) (2 := H2)
      as (a & x & b & y & c & z & G1 & G2 & G3 & G4); auto.
    exists a, x, b, y, c; split; auto.
    apply (HR2 _ z); auto.
  Qed.

End php_upto.


