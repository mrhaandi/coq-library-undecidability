Require Import Undecidability.L.L.

Require Import Undecidability.Synthetic.Definitions.
Require Import PeanoNat Lia ssreflect ssrbool ssrfun.

Section Argument.

Definition omega :=
  app (lam (app (var 0) (var 0))) (lam (app (var 0) (var 0))).

Fixpoint close k t :=
  match t with
  | var n => if Nat.leb k n then omega else var n
  | app s t => app (close k s) (close k t)
  | lam s => lam (close (S k) s)
  end.

(*
Lemma close_subst k s t : close k (subst s k (close 0 t)) = subst (close (S k) s) k (close 0 t).
Proof.
  elim: s k.
  - admit.
  - admit.
  - move=> ? IH ? /=. rewrite IH.
Admitted.

Lemma close_subst' k s t : close k (subst s k (close k t)) = subst (close (S k) s) k (close 0 t).
Proof.
  elim: s k.
  - admit.
  - admit.
  - move=> ? IH ? /=. rewrite IH.
Admitted.

  - move=> n k. have -> /= : S k = k + 1 by lia.
    case E: (Nat.eqb n k); move: (E) => /Nat.eqb_spec H.
    + case H': (Nat.leb (k + 1) n); move=> /Nat.leb_spec0 in H'.
      * lia.
      * by rewrite /= E.
    + case E': (Nat.leb (k + 1) n); move=> /Nat.leb_spec0 in E'.
      * move=> /=. case E'': (Nat.leb k n); move=> /Nat.leb_spec0 in E''; [done|lia].
      * rewrite /= E. case E'': (Nat.leb k n); move=> /Nat.leb_spec0 in E''; [lia|done].
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH ? /=. rewrite IH.
      move=> /PeanoNat.Nat.eqb_spec in E.
    done.

Lemma close_subst s t : close 0 (subst s 0 t) = subst (close 1 s) 0 (close 0 t).
Proof.
  elim: s t.
  - by case.
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH ? /=.
  move=> [|n] t /=.
Admitted.

(*
Lemma close_subst k s t : close k (subst s k t) = subst (close (S k) s) k (close k t).
Proof.
  elim: s k.
  - move=> n k. have -> /= : S k = k + 1 by lia.
    case E: (Nat.eqb n k); move: (E) => /Nat.eqb_spec H.
    + case H': (Nat.leb (k + 1) n); move=> /Nat.leb_spec0 in H'.
      * lia.
      * by rewrite /= E.
    + case E': (Nat.leb (k + 1) n); move=> /Nat.leb_spec0 in E'.
      * move=> /=. case E'': (Nat.leb k n); move=> /Nat.leb_spec0 in E''; [done|lia].
      * rewrite /= E. case E'': (Nat.leb k n); move=> /Nat.leb_spec0 in E''; [lia|done].
  - move=> ? IH1 ? IH2 ? /=. by rewrite IH1 IH2.
  - move=> ? IH ? /=. rewrite IH.
      move=> /PeanoNat.Nat.eqb_spec in E.
    done.

Admitted.
*)
Lemma close_subst s t : close 0 (subst s 0 t) = subst (close 1 s) 0 (close 0 t).
Proof.
Admitted.
*)

(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

Arguments funcomp {X Y Z} (g f) /.

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

(* parallel term renaming *)
Fixpoint ren (xi : nat -> nat) (t : term) : term  :=
  match t with
  | var x => var (xi x)
  | app s t => app (ren xi s) (ren xi t)
  | lam t => lam (ren (scons 0 (funcomp S xi)) t)
  end.

Lemma asd s t : L.eval s t -> L.eval (close 0 s) (close 0 t).
Proof.
  elim; clear s t. { move=> ?. by apply: eval_abs. }
  move=> s u t t' v.
  move=> /= *.
  apply: eval_app; [eassumption|eassumption|].
  by rewrite -close_subst.
Qed.


Lemma asd s t : L.eval s t -> forall xi, L.eval (ren xi s) (ren xi t).
Proof.
  elim; clear s t. { move=> ??. by apply: eval_abs. }
  move=> s u t t' v.
  move=> /= ? IH1 ? IH2 ? IH3 xi.
  apply: eval_app.
  - by apply: IH1.
  - by apply: IH2.
  - have := IH3 xi.
  [eassumption|eassumption|].
  by rewrite -close_subst.
Qed.



Theorem reduction : HaltL ⪯ HaltLclosed.
Proof.
Admitted.