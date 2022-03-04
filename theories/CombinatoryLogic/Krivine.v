(*
  Krivine Machine
  https://en.wikipedia.org/wiki/Krivine_machine

  Closure-based left-most-outer-most lambda-term evaluation

  Further details in L_CBN_Interpreter
*)

From Undecidability Require L.L.
Require Import List Lia.
Import L.
From Undecidability Require Import L.Util.L_facts.
From Undecidability Require L.Computability.Seval.
Require Import Relations.
Require Import ssreflect ssrbool ssrfun.

Unset Implicit Arguments.

Inductive eterm := closure : list eterm -> term -> eterm.

(* actual krivine machine
https://en.wikipedia.org/wiki/Krivine_machine *)
Inductive halt_cbn : list eterm -> list eterm -> term -> Prop :=
  | halt_var_0 ts ctx t ctx' :
      halt_cbn ts ctx t ->
      halt_cbn ts ((closure ctx t)::ctx') (var 0)
  | halt_var_S ts ctx n t :
      halt_cbn ts ctx (var n) ->
      halt_cbn ts (t::ctx) (var (S n))
  | halt_app ts ctx s t :
      halt_cbn ((closure ctx t)::ts) ctx s ->
      halt_cbn ts ctx (app s t)
  | halt_lam_ts t ts ctx s :
      halt_cbn ts (t::ctx) s ->
      halt_cbn (t::ts) ctx (lam s)
  | halt_lam ctx s :
      halt_cbn [] ctx (lam s).

Fixpoint eclosed (u : eterm) : Prop :=
  let '(closure ctx t) := u in bound (length ctx) t /\ Forall id (map eclosed ctx).


Lemma Forall2_consE {X : Type} {P : X -> X -> Prop} {x1 l1 x2 l2} : 
  Forall2 P (x1::l1) (x2::l2) -> P x1 x2 /\ Forall2 P l1 l2.
Proof. move=> H. by inversion H. Qed.


Lemma halt_cbn_ren_S {ts ctx u s} :
  halt_cbn ts ctx s ->
  halt_cbn ts (u::ctx) (ren S s).
Proof.
  move=> /halt_cbn_flatten_iff. apply; first done.
  - by rewrite /= /many_subst !simpl_term.
Qed.


Fixpoint stepf (s : term) : option term :=
  match s with
  | app s' t =>
      match s' with
      | lam s'' => Some (subst (scons t var) s'')
      | _ => 
          match stepf s' with
          | Some s'' => Some (app s'' t)
          | None => None
          end
      end
  | _ => None
  end.

Lemma step_stepf s t : step s t -> stepf s = Some t.
Proof.
  elim; first done.
  case; [done| |done].
  by move=> > /= ? ->.
Qed.

Lemma stepf_step s t : stepf s = Some t -> step s t.
Proof.
  elim: s t; [done| |done].
  case; [done| |].
  - move=> s1 s2 IH1 s3 IH2 t.
    move: IH1. case E': (stepf (app s1 s2)) => [t'|].
    + move=> /(_ t' erefl) ?.
      move: E' => /= -> [<-]. by apply: stepApp.
    + by move: E' => /= ->.
  - move=> > ? > ?? /= [<-]. by apply: stepLam.
Qed.

Definition stepsf n s := Nat.iter n (obind stepf) (Some s).

Lemma iter_plus {X} (f : X -> X) (x : X) n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
  elim: m; first by rewrite Nat.add_0_r.
  move=> m /= <-. by have ->: n + S m = S n + m by lia.
Qed.

Lemma oiter_None {X : Type} (f : X -> option X) k : Nat.iter k (obind f) None = None.
Proof. elim: k; [done | by move=> /= ? ->]. Qed.

(*
Lemma oiter_plus {X : Type} (f : X -> option X) n m s :
  Nat.iter (n + m) (obind f) (Some s) = (Nat.iter m (obind f)) (Nat.iter n (obind f) (Some s)).
Proof.
  elim: m.
  - have -> : n + 0 = n by lia. by case: (stepsf n s).
  - move=> m IH /=.
    have -> : n + S m = S (n + m) by lia.
    rewrite /= IH. by case: (stepsf n s).
Qed.
*)

Lemma stepsf_plus n m s : stepsf (n + m) s = (obind (stepsf m)) (stepsf n s).
Proof.
  rewrite /stepsf iter_plus. case: (Nat.iter n _ _); [done|by rewrite oiter_None].
Qed.

Arguments stepsf : simpl never.

Arguments clos_refl_trans {A}.
Arguments clos_trans {A}.
(*
Inductive crt_length : nat -> term -> term -> Prop :=
  | crt_length_refl t : crt_length 0 t t
  | 
*)

(*
Lemma step_aux (P : term -> Prop) :
  (forall s, (forall u, clos_trans step s u -> P u) -> P s) -> 
  forall s t,
    clos_refl_trans step s t -> P t -> (forall u, not (clos_refl_trans step t u)) -> P s.
Proof.
  move=> IH ?? /(@clos_rt_rt1n term). elim; first done.
  move=> s s' t Hss' Hs't IH' Ht H't. apply: (IH).
  move=> u /(@clos_trans_t1n_iff term) Hsu.
  case: Hsu Hss'.
  + move=> ? /step_fun /[apply] ->. by apply: IH'.
  + move=> > + ?. move=> /step_fun /[apply] ?. subst.
    apply: (IH).
      case: Hs't IH H't Ht; clear t.
      * done.
      * move=> s'' t Hs's'' Hs''t IH1 IH2 Ht. apply: IH1; [done| |done].
        apply.
        admit.

Lemma step_aux s t (P : term -> Prop) : (forall u, not (clos_refl_trans step t u)) ->
  ((forall u, clos_trans step s u -> P u) -> P s) -> P t -> clos_refl_trans step s t -> P s.
Proof.
  move=> H1 H2 H3 /(@clos_rt_rt1n term) Hst.
  elim: Hst H1 H2 H3; clear s t.
  - done.
  - move=> s s' t Hss' Hs't IH H't IH' Ht. apply: IH'.
    move=> u /(@clos_trans_t1n_iff term) Hsu.
    case: Hsu Hss'.
    + move=> ? /step_fun /[apply] ->.
      case: Hs't IH H't Ht; clear t.
      * done.
      * move=> s'' t Hs's'' Hs''t IH1 IH2 Ht. apply: IH1; [done| |done].
        apply.
        admit.
    + move=> > + ?. move=> /step_fun /[apply] ?. subst.

        done. 
    apply: (IH).
    done. apply.  admit.  done.
    admit. admit.
  - done.
  -  
Admitted.

Lemma test s t : clos_refl_trans step s t -> False.
Proof.
  apply: step_aux.
  - admit.
  -  
  
*)

Lemma subst_closed {sigma t} : closed t -> subst sigma t = t.
Proof. Admitted.

Lemma many_subst_closed {ts t} : closed t -> many_subst ts t = t.
Proof. move=> /subst_closed. by apply. Qed.



(* maybe this is needed? 
Lemma halt_cbn_spec ts ctx s : halt_cbn ts ctx s ->
  exists t, clos_refl_trans term step (flatten (closure ctx s)) (lam t).
Proof.
  elim.
  - move=> > ? [t IH]. exists t.
    move: IH. by rewrite /= !simpl_term.
Admitted.
*)