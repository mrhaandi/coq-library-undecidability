(* ** Abstract Reduction Systems *)
(* from Semantics Lecture at Programming Systems Lab, https://www.ps.uni-saarland.de/courses/sem-ws13/ *)

Require Export Undecidability.Shared.Libs.PSL.Base.
From Stdlib Require Export Lia Arith.

Module ARSNotations.
  Notation "p '<=1' q" := (forall x, p x -> q x) (at level 70).
  Notation "p '=1' q" := (forall x, p x <-> q x) (at level 70).
  Notation "R '<=2' S" := (forall x y, R x y -> S x y) (at level 70).
  Notation "R '=2' S"  := (forall x y, R x y <-> S x y) (at level 70).
End ARSNotations.

Import ARSNotations.

(* Relational composition *)

Definition rcomp X Y Z (R : X -> Y -> Prop) (S : Y -> Z -> Prop) 
: X -> Z -> Prop :=
  fun x z => exists y, R x y /\ S y z.

(* Power predicates *)

From Stdlib Require Import Arith Relations.
Definition pow X R n : X -> X -> Prop := it (rcomp R) n eq.

Definition functional {X Y} (R: X -> Y -> Prop) := forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.
Definition terminal {X Y} (R: X -> Y -> Prop) x:= forall y, ~ R x y.

Section FixX.
  Variable X : Type.
  Implicit Types R S : X -> X -> Prop.
  Implicit Types x y z : X.

  Definition reflexive R := forall x, R x x.
  Definition symmetric R := forall x y, R x y -> R y x.
  Definition transitive R := forall x y z, R x y -> R y z -> R x z.

  (* Reflexive transitive closure *)

  Inductive star R : X -> X -> Prop :=
  | starR x : star R x x
  | starC x y z : R x y -> star R y z -> star R x z.

  Definition evaluates R x y := star R x y /\ terminal R y.

  (* Making first argument a non-uniform parameter doesn't simplify the induction principle. *)

  Lemma star_simpl_ind R (p : X -> Prop) y :
    p y ->
    (forall x x', R x x' -> star R x' y -> p x' -> p x) -> 
    forall x, star R x y -> p x.
  Proof.
    intros A B. induction 1; eauto.
  Qed.

  Lemma star_trans R:
    transitive (star R).
  Proof.
    induction 1; eauto using star.
  Qed.

  Lemma R_star R: R <=2 star R.
  Proof.
    eauto using star.
  Qed.

  Instance star_PO R: PreOrder (star R).
  Proof.
    constructor;repeat intro;try eapply star_trans;  now eauto using star.
  Qed.
  
  (* Power characterization *)

  Lemma star_pow R x y :
    star R x y <-> exists n, pow R n x y.
  Proof.
    split; intros A.
    - induction A as [|x x' y B _ [n IH]].
      + exists 0. reflexivity.
               + exists (S n), x'. auto.
               - destruct A as [n A].
                 revert x A. induction n; intros x A.
                 + destruct A. constructor.
                 + destruct A as [x' [A B]]. econstructor; eauto.
  Qed.

  Lemma pow_star R x y n:
    pow R n x y -> star R x y.
  Proof.
    intros A. erewrite star_pow. eauto.
  Qed.

  Lemma star_clos_rt_iff R x y : star R x y <-> clos_refl_trans _ R x y.
  Proof.
    split.
    - intros H; induction H; eauto using clos_refl_trans.
    - intros H%clos_rt_rt1n_iff. induction H; eauto using star.
  Qed.

  (* Equivalence closure *)

  Inductive ecl R : X -> X -> Prop :=
  | eclR x : ecl R x x
  | eclC x y z : R x y -> ecl R y z -> ecl R x z
  | eclS x y z : R y x -> ecl R y z -> ecl R x z.

  Lemma ecl_trans R :
    transitive (ecl R).
  Proof.
    induction 1; eauto using ecl.
  Qed.

  Lemma ecl_sym R :
    symmetric (ecl R).
  Proof.
    pose proof (@ecl_trans R).
    induction 1; eauto using ecl.
  Qed.

  Lemma star_ecl R :
    star R <=2 ecl R.
  Proof.
    induction 1; eauto using ecl.
  Qed.

  (* Diamond, confluence, Church-Rosser *)

  Definition joinable R x y :=
    exists z, R x z /\ R y z.

  Definition diamond R :=
    forall x y z, R x y -> R x z -> joinable R y z.

  Definition confluent R := diamond (star R).

  Definition semi_confluent R :=
    forall x y z, R x y -> star R x z -> joinable (star R) y z.

  Definition church_rosser R :=
    ecl R <=2 joinable (star R).

  Goal forall R, diamond R -> semi_confluent R.
  Proof.
    intros R A x y z B C.
    revert x C y B.
    refine (star_simpl_ind _ _).
    - intros y C. exists y. eauto using star.
    - intros x x' C D IH y E.
      destruct (A _ _ _ C E) as [v [F G]].
      destruct (IH _ F) as [u [H I]].
      assert (J:= starC G H).
      exists u. eauto using star.
  Qed.

  Lemma diamond_to_semi_confluent R :
    diamond R -> semi_confluent R.
  Proof.
    intros A x y z B C. revert y B.
    induction C as [|x x' z D _ IH]; intros y B.
    - exists y. eauto using star.
             - destruct (A _ _ _ B D) as [v [E F]].
               destruct (IH _ F) as [u [G H]].
               exists u. eauto using star.
  Qed.

  Lemma semi_confluent_confluent R :
    semi_confluent R <-> confluent R.
  Proof.
    split; intros A x y z B C.
    - revert y B.
      induction C as [|x x' z D _ IH]; intros y B.
      + exists y. eauto using star.
               + destruct (A _ _ _ D B) as [v [E F]].
                 destruct (IH _ E) as [u [G H]].
                 exists u.
                 pose proof (@star_trans R).
                 eauto.
               - apply (A x y z); eauto using star.
  Qed.

  Lemma diamond_to_confluent R :
    diamond R -> confluent R.
  Proof.
    intros A. apply semi_confluent_confluent, diamond_to_semi_confluent, A.
  Qed.

  Lemma confluent_CR R :
    church_rosser R <-> confluent R.
  Proof.
    split; intros A.
    - intros x y z B C. apply A.
      pose proof (@ecl_trans R).
      pose proof (@ecl_sym R).
      eauto using star_ecl.
    - intros x y B. apply semi_confluent_confluent in A.
      induction B as [x|x x' y C B IH|x x' y C B IH].
      + exists x. eauto using star.
               + destruct IH as [z [D E]]. exists z. eauto using star.
               + destruct IH as [u [D E]].
                 destruct (A _ _ _ C D) as [z [F G]].
                 exists z. pose proof (@star_trans R). eauto.
  Qed.


  (* End Semantics Library *)


  (* Uniform confluence and parametrized confluence *)

  Definition uniform_confluent (R : X -> X -> Prop ) := forall s t1 t2, R s t1 -> R s t2 -> t1 = t2 \/ exists u, R t1 u /\ R t2 u.

  Lemma pow_add R n m (s t : X) : pow R (n + m) s t <-> rcomp (pow R n) (pow R m) s t.
  Proof.
    revert m s t; induction n; intros m s t.
    - simpl. split; intros. econstructor. split. unfold pow. simpl. reflexivity. eassumption.
      destruct H as [u [H1 H2]]. unfold pow in H1. simpl in *. subst s. eassumption.
    - simpl in *; split; intros.
      + destruct H as [u [H1 H2]].
        change (it (rcomp R) (n + m) eq) with (pow R (n+m)) in H2.
        rewrite IHn in H2.
        destruct H2 as [u' [A B]]. unfold pow in A.
        econstructor. 
        split. econstructor. repeat split; repeat eassumption. eassumption.
      + destruct H as [u [H1 H2]].
        destruct H1 as [u' [A B]].
        econstructor.  split. eassumption. change (it (rcomp R) (n + m) eq) with (pow R (n + m)).
        rewrite IHn. econstructor. split; eassumption.
  Qed.
  
  Lemma eq_ref : forall (R : X -> X -> Prop), R =2 R.
  Proof.
    split; tauto.
  Qed.
   
  Lemma parametrized_semi_confluence (R : X -> X -> Prop) (m : nat) (s t1 t2 : X) :
    uniform_confluent R ->
    pow R m s t1 ->
    R s t2 ->
    exists k l u,
      k <= 1 /\ l <= m /\ pow R k t1 u /\ pow R l t2 u /\ m + k = S l.
  Proof.
    intros unifConfR; revert s t1 t2; induction m; intros s t1 t2 s_to_t1 s_to_t2.
    - unfold pow in s_to_t1. simpl in *. subst s.
      exists 1, 0, t2.
      repeat split; try lia.
      econstructor. split; try eassumption; econstructor.
    - destruct s_to_t1 as [v [s_to_v v_to_t1]].
      destruct (unifConfR _ _ _ s_to_v s_to_t2) as [H | [u [v_to_u t2_to_u]]].
      + subst v. eexists 0, m, t1; repeat split; try lia; eassumption.
      + destruct (IHm _ _ _ v_to_t1 v_to_u) as [k [l [u' H]]].
        eexists k, (S l), u'; repeat split; try lia; try tauto.
        econstructor. split. eassumption. tauto.
  Qed.
  
  Lemma parametrized_confluence (R : X -> X -> Prop) (m n : nat) (s t1 t2 : X) : 
    uniform_confluent R ->
    pow R m s t1 -> 
    pow R n s t2 -> 
    exists k l u,
      k <= n /\ l <= m /\ pow R k t1 u /\ pow R l t2 u /\ m + k = n + l.
  Proof.
    revert n s t1 t2; induction m; intros n s t1 t2 unifConR s_to_t1 s_to_t2.
    - unfold pow in s_to_t1. simpl in s_to_t1. subst s.
      exists n, 0, t2. repeat split; try now lia. eassumption.
    - unfold pow in s_to_t1. simpl in *.
      destruct s_to_t1 as [v [s_to_v v_to_t1]].
      destruct (parametrized_semi_confluence unifConR s_to_t2 s_to_v) as
          [k [l [u [k_lt_1 [l_lt_n [t2_to_u [v_to_u H]]]]]]].
      destruct (IHm _ _ _ _ unifConR v_to_t1 v_to_u) as
          [l'[k'[u'[l'_lt_l [k'_lt_m [t1_to_u' [u_to_u' H2]]]]]]].
      exists l', (k + k'), u'.
      repeat split; try lia. eassumption.
      rewrite pow_add.
      econstructor; split; eassumption.
  Qed.

End FixX.
