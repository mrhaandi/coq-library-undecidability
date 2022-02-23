From Undecidability Require L.L.
Require Import List Lia.
Import L.
From Undecidability Require Import L.Util.L_facts.
Require Import Relations.
Require Import ssreflect ssrbool ssrfun.

(* left-most outer-most weak reduction *)
Inductive step : term -> term -> Prop :=
  | step_lam s t : step (app (lam s) t) (subst s 0 t)
  | step_app s s' t : step s s' -> step (app s t) (app s' t).

Lemma step_app_app s1 s2 u t : step (app s1 s2) u -> step (app (app s1 s2) t) (app u t).
Proof. move=> ?. by apply: step_app. Qed. 
Arguments clos_refl_trans {A}.
Definition steps := clos_refl_trans step.

Ltac do_step := cbn; apply: rt_trans; [apply: rt_step; do ? apply: step_app_app; by apply: step_lam|].

Lemma steps_app s s' t : steps s s' -> steps (app s t) (app s' t).
Proof.
  elim.
  - move=> > ?. apply: rt_step. by apply: step_app.
  - move=> *. apply: rt_refl.
  - move=> *. by apply: rt_trans; eassumption.
Qed.

Definition mk_O := lam (lam (var 1)).
Definition mk_S (n : term) := lam (lam (app (var 0) n)).
Fixpoint enc_nat (n : nat) : term :=
  match n with
  | 0 => mk_O
  | (S n) => mk_S (enc_nat n)
  end.

Lemma enc_nat_closed n : closed (enc_nat n).
Proof.
  elim: n; first done.
  move=> n IH m t /=. by rewrite IH.
Qed.

Lemma enc_nat_spec n f g : 
  closed f -> closed (lam g) ->
  steps (app (app (enc_nat n) f) (lam g)) (
    match n with
    | 0 => f
    | S n => subst g 0 (enc_nat n)
    end).
Proof.
  move=> Hf Hg.
  have H'g : forall n t, subst g (S n) t = g.
  { move=> n' t' /=. by have [] := Hg n' t'. }
  case: n.
  - do ? do_step. rewrite Hf. apply: rt_refl.
  - move=> ? /=. do ? do_step. rewrite !enc_nat_closed. by apply: rt_refl.
Qed.

Opaque enc_nat.

Definition rho (s : term) := 
  let C := lam (lam (app (var 0) (lam (app (app (app (var 2) (var 2)) (var 1)) (var 0))))) in
  lam (app (app (app C C) s) (var 0)).

Lemma rho_closed s : closed s -> closed (rho s).
Proof. move=> Hs ?? /=. by rewrite Hs. Qed.

Lemma rho_spec s t : L_facts.closed s -> steps (app (rho s) (lam t)) (app (app s (rho s)) (lam t)).
Proof.
  move=> Hs. rewrite /rho. do ? do_step.
  rewrite /= (Hs 0). by apply: rt_refl.
Qed.

Opaque rho.

Definition many_app (s : term) (ts : list term) :=
  fold_left (fun s' t => app s' t) ts s.

(* given n m, if m = n then s else t *)
Definition nat_beq s t := rho (lam (lam (lam (
  (* [m n nat_beq] *) many_app (var 1) [
      many_app (var 0) [s; lam t];
      lam (many_app (var 1) [t; lam (app (app (var 4) (var 1)) (var 0))])
  ])))).

Lemma nat_beq_closed {s t} : closed s -> closed t -> closed (nat_beq s t).
Proof. move=> Hs Ht. apply: rho_closed. move=> ?? /=. by rewrite !Hs !Ht. Qed. 

(*
Lemma subst_nat_beq {s t} n u : subst (nat_beq s t) n u = nat_beq (subst s n u) (subst t n u).
Proof.
  rewrite /nat_beq /=.
*)

Lemma nat_beq_spec s t n m : closed s -> closed t ->
  steps (app (app (nat_beq s t) (enc_nat n)) (enc_nat m))
  (if Nat.eqb n m then s else t).
Proof.
  move=> Hs Ht. elim: n m.
  - move=> [|m] /=.
    + rewrite /nat_beq /=.
      apply: rt_trans. { apply: steps_app. apply: rho_spec. move=> ?? /=. by rewrite Hs Ht /=. }
      do 5 do_step. rewrite /=.
      do ? do_step. rewrite /= !Hs. by apply: rt_refl.
    + rewrite /nat_beq /=.
      apply: rt_trans. { apply: steps_app. apply: rho_spec. move=> ?? /=. by rewrite Hs Ht /=. }
      do ? do_step. rewrite /= !Ht. by apply: rt_refl.
  - move=> n IH [|m] /=.
    + rewrite /nat_beq /=.
      apply: rt_trans. { apply: steps_app. apply: rho_spec. move=> ?? /=. by rewrite Hs Ht /=. }
      do ? do_step. rewrite /= !Ht. by apply: rt_refl.
    + rewrite /nat_beq /=.
      apply: rt_trans. { apply: steps_app. apply: rho_spec. move=> ?? /=. by rewrite Hs Ht /=. }
      apply: rt_trans; last by apply: IH.
      rewrite -/(nat_beq _ _). move Eu: (nat_beq s t) => u.
      do ? do_step. rewrite /= !enc_nat_closed.
      rewrite -Eu !(nat_beq_closed Hs Ht). by apply: rt_refl.
Qed.

Opaque nat_beq.

Definition mk_var (n : term) := lam (lam (lam (app (var 2) n))).
Definition mk_app (s t : term) := lam (lam (lam (app (app (var 1) s) t))).
Definition mk_lam (s : term) := lam (lam (lam (app (var 0) s))).

Fixpoint enc_term (s : term) : term :=
  match s with
  | var n => mk_var (enc_nat n)
  | app s t => mk_app (enc_term s) (enc_term t)
  | lam s => mk_lam (enc_term s)
  end.

Lemma enc_term_closed s : closed (enc_term s).
Proof.
  elim: s.
  - move=> ??? /=. by rewrite enc_nat_closed.
  - move=> s IHs t IHt ?? /=. by rewrite IHs IHt.
  - move=> s IH ?? /=. by rewrite IH.
Qed.


Lemma enc_term_spec (s : term) (f g h : term) :
  closed (lam f) -> closed (lam (lam g)) -> closed (lam h) ->
  steps (app (app (app (enc_term s) (lam f)) (lam (lam g))) (lam h)) (
    match s with
    | var n => subst f 0 (enc_nat n)
    | app s' t' => subst (subst g 1 (enc_term s')) 0 (enc_term t')
    | lam s' => subst h 0 (enc_term s')
    end).
Proof.
  move=> Hf Hg Hh.
  have H'f : forall n t, subst f (S n) t = f.
  { move=> n t. by have [] := Hf n t. }
  have H'g : forall n t, subst g (S (S n)) t = g.
  { move=> n t. by have [] := Hg n t. }
  have H'h : forall n t, subst h (S n) t = h.
  { move=> n t. by have [] := Hh n t. }
  case: s.
  - move=> n. do ? do_step. rewrite /= !enc_nat_closed !H'f.
    by apply: rt_refl.
  - move=> ? ?. do ? do_step. rewrite /= !enc_term_closed !H'g.
    by apply: rt_refl.
  - move=> ?. do ? do_step. rewrite !enc_term_closed.
    by apply: rt_refl.
Qed.

Opaque enc_term.

Definition mk_None := lam (lam (var 0)).
Definition mk_Some (s : term) := lam (lam (app (var 1) s)).

Definition normalizer : term.
Admitted.

Lemma normalizer_closed : closed normalizer.
Admitted.

Lemma normalizer_spec s t : eval s t -> steps (app normalizer (enc_term s)) (mk_Some (enc_term t)).
Proof.
Admitted.

Lemma normalizer_spec s t : eval s t -> steps (app normalizer (enc_term s)) (mk_Some (enc_term t)).
Proof.
  
Admitted.

  (*
Lemma enc_option_closed o : closed (enc_option o).
Proof.
  case: o => [s|].
  - move=> ?? /=. by rewrite enc_term_closed.
  - done.
Qed.
*)




(*
Fixpoint step' (n : nat) (s : term) : term :=
  match n with
  | 0 => s
  | S n => 
      match s with
      | app (lam s') t' => step' n (subst s' 0 t')
      | app s' t' => step 
*)




(* left-most outer-most weak step-indexed reduction *)
Fixpoint sred (n : nat) (s : term) : option term :=
  match n with
  | 0 => None
  | S n =>
      match s with
      | var _ => None
      | app s' t' =>
          match sred n s' with
          | Some (lam s'') => sred n (subst s'' 0 t')
          | _ => None
          end
      | _ => Some s
      end
  end.

(*
Tactic Notation "do_step" tactic(tac) := (tac; apply: rt_trans; [apply: rt_step; do ? apply: step_app_app; by apply: step_lam|]).
*)
(* substitute s n t *)
Definition substituter t := rho (lam (lam (lam (
    (* [n s substituter] *) 
  many_app (var 2) [
    (* case s = var n *)     lam (app (app (nat_beq (var 0) (var 2)) (var 1)) t);
    (* case s = app s' t' *) (lam (lam (mk_app 
      (app (app (app (var 4) (var 3)) (var 2)) (var 1))
      (app (app (app (var 4) (var 3)) (var 2)) (var 0)))));
    (* case s = lam s' *) (lam (mk_lam
      (app (app (app (var 3) (var 2)) (mk_S (var 1))) (var 0))
    ))])))).
  
Lemma substituter_closed t : closed t -> closed (substituter t).
Proof.
  move=> Ht. apply: rho_closed. move=> ?? /=. rewrite !Ht.
  
  rewrite !nat_beq_closed.
Definition normalizer := rho (lam (lam (
  (* [s eval] *)
  many_app (var 0) [
    (* case s = var n *)     lam (enc_option None);
    (* case s = app s' t' *) lam (lam (
      (* [t' s' s eval] *) many_app (app (var 3) (var 1)) [
          (* case eval s' = var n *) lam (enc_option None);
          (* case eval s' = app s'' t'' *) lam (enc_option None);
          (* case eval s' = lam s'' *) lam ( 
            (* [s'' t' s' s eval] *) app (var 0) (enc_subst s'' 0 t')
          )
      ]));
    (* case s = lam s' *)    lam (enc_option (Some (var 1)))
  ]))).

  app (var)

))
