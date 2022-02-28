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

Lemma halt_cbnE ts ctx u : halt_cbn ts ctx u ->
  match u with
  | var 0 =>
      match ctx with
      | [] => False
      | (closure ctx' t')::_ => halt_cbn ts ctx' t'
      end
  | var (S n) => 
      match ctx with
      | [] => False
      | _::ctx' => halt_cbn ts ctx' (var n)
      end
  | app s t => halt_cbn ((closure ctx t) :: ts) ctx s
  | lam s =>
      match ts with
      | [] => True
      | t'::ts' => halt_cbn ts' (t'::ctx) s
      end
  end.
Proof. by case. Qed.

Fixpoint term_size (t : term) : nat :=
  match t with
  | var n => n
  | app s t => 1 + term_size s + term_size t
  | lam s => 1 + term_size s
  end.

Fixpoint eterm_size (u : eterm) : nat :=
  let '(closure ctx t) := u in 1 + list_sum (map eterm_size ctx) + (term_size t).

Definition context_size (ctx : list eterm) : nat :=
  eterm_size (closure ctx (var 0)).

Fixpoint eclosed (u : eterm) : Prop :=
  let '(closure ctx t) := u in bound (length ctx) t /\ Forall id (map eclosed ctx).

Fixpoint subst_list k (ts : list term) (u : term) : term :=
  match u with
  | var n => nth n ((map var (seq 0 k)) ++ ts) (var n)
  | app s t => app (subst_list k ts s) (subst_list k ts t)
  | lam s => lam (subst_list (S k) ts s)
  end.

(* recursively substitute each local context *)
Fixpoint flatten (u : eterm) : term :=
  let '(closure ctx t) := u in subst_list 0 (map flatten ctx) t.

  
(* induction/recursion principle wrt. a decreasing measure f *)
(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
(forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Lemma flatten_var_S t ctx n :
  flatten (closure (t :: ctx) (var (S n))) = flatten (closure ctx (var n)).
Proof.
Admitted.

Lemma Forall2_consE {X : Type} {P : X -> X -> Prop} {x1 l1 x2 l2} : 
  Forall2 P (x1::l1) (x2::l2) -> P x1 x2 /\ Forall2 P l1 l2.
Proof. move=> H. by inversion H. Qed.

(* halt_cbn is invariant closure flattening *)
Lemma halt_cbn_flatten_iff ts1 ts2 ctx1 ctx2 s1 s2:
  halt_cbn ts1 ctx1 s1 ->
  Forall2 (fun t1 t2 => flatten t1 = flatten t2) ts1 ts2 ->
  flatten (closure ctx1 s1) = flatten (closure ctx2 s2) ->
  halt_cbn ts2 ctx2 s2.
Proof.
  move=> H. elim: H ts2 ctx2 s2; clear ts1 ctx1 s1.
  - move=> ts ctx t ctx' ? IH ts2 ctx2 s2.
    by move=> /IH /[apply].
  - move=> ts1 ctx1 n t ? IH ts2 ctx2 s2.
    rewrite flatten_var_S.
    by move=> /IH /[apply].
  - move=> ts1 ctx1 s t ? IH ts2 ctx2 s2.
    elim /(measure_rect context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * move=> /= ??. apply: halt_var_0. apply: IH' => //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ??. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + move=> ??? /= [] /IH {}IH ?.
      apply: halt_app. apply: IH => //=.
      by constructor.
    + done.
  - move=> t1 ts1 ctx1 s1 ? IH [|t2 ts2] ctx2 s2.
    { move=> H. by inversion H. }
    move=> /Forall2_consE [Ht1t2 ?].
    elim /(measure_rect context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * move=> /= ?. apply: halt_var_0. apply: IH'=> //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ?. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + done.
    + (* may still work with proper flatten (subst with shift, no var 0 as target because of shift) *) move=> ? [] /= ?.
      apply: halt_lam_ts. apply: IH => //=.
      rewrite Ht1t2.
      subst_list 1 (var 0) (var 1) =
      var 0 =
      subst_list 1 (var 0) (var 0)

      subst_list 0 (x :: (var 0)) (var 1)
      = var 0 <> x =
      subst_list 0 (x :: (var 0)) (var 0)
      admit. (* doublecheck, here is closedness! *)
  - move=> ctx1 s1 [|t2 ts2] ctx2 s2; first last.
    { move=> H. by inversion H. }
    move=> _.
    elim /(measure_rect context_size): ctx2 s2.
    move=> ctx2 IH' []. 
    + (* s2 is (var n) *)
      move: ctx2 IH' => [|[ctx'2 t'2] ctx2] IH'. { by case. }
      move=> [|n].
      * move=> /= ?. apply: halt_var_0. apply: IH'=> //=.
        rewrite /context_size /=. lia.
      * rewrite flatten_var_S.
        move=> /= ?. apply: halt_var_S. apply: IH' => //=.
        rewrite /context_size /=. lia.
    + done.
    + move=> *. by apply: halt_lam.


(* halt_cbn is invariant closure flattening *)
Lemma halt_cbn_flatten_iff ts1 ts2 ctx1 ctx2 s1 s2:
  halt_cbn ts1 ctx1 s1 ->
  Forall id (map eclosed ts1) ->
  Forall id (map eclosed ts2) ->
  Forall2 (fun t1 t2 => flatten t1 = flatten t2) ts1 ts2 ->
  eclosed (closure ctx1 s1) ->
  eclosed (closure ctx2 s2) ->
  flatten (closure ctx1 s1) = flatten (closure ctx2 s2) ->
  halt_cbn ts2 ctx2 s2.
Proof.
Admitted.