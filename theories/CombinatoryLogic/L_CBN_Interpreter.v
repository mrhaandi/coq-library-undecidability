From Undecidability Require L.L.
Require Import List Lia.
Import L.
From Undecidability Require Import L.Util.L_facts.
From Undecidability Require L.Computability.Seval.
Require Import Relations.
Require Import ssreflect ssrbool ssrfun.

(*
  k   : step index
  ts  : hanging arguments (evaluationg u v1 .. vn)
  ctx : context for deBruijn terms
  vs  : list of terms that need to evalue (necessary for call-by-value) 
  u term to reduce
  tail-recursive
  currently left-most outer-most call by value
*)

Inductive eterm := closure : list eterm -> term -> eterm.

(* eva k ts vs u *)
(* domain predicate 
advantages: 
+ all functionality (subst, eqb, ...) in halt_cbv
+ tail-recursive (halt_cbv .. -> halt_cbv ..)
+ easy to simulate by stack machine /minsky machine?
*)

(*
Definition step (x : (list eterm) * eterm) : option ((list eterm) * eterm) :=
  let '(ts, closure ctx s) := x in
    match s with
    (* context lookup *)
    | var n =>
      match ctx, n with
      | t'::ctx', 0 => Some (ts, t')
      | t'::ctx', S n' => Some (ts, closure ctx (var n'))
      | _, _ => None
      end
    (* push argument *)
    | app s t => Some ((closure ctx t) :: ts, closure ctx s)
    (* contract redex *)
    | lam s =>
        match ts with
        | [] => None
        | t'::ts' => Some (ts', closure (t'::ctx) s)
        end
    end.
*)
    (*
Inductive halt_cbn : list eterm -> eterm -> Prop :=
  | halt_cbn_step ts s ts' s' : step (ts, s) = Some (ts', s') -> halt_cbn ts' s' -> halt_cbn ts s
  | halt_cbn_lam ctx s : halt_cbn [] (closure ctx (lam s)).
*)

(* most easy to simulate halt_cbn 
halt_cbn [t1 .. tn] ctx t means that (t t1 .. tn) halts in context ctx (terms for free variables)
*)
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

(* left-most outer-most call-by-name *)
Inductive step : term -> term -> Prop :=
  | stepLam s t    : step (app (lam s) t) (subst s 0 t)
  | stepApp s s' t : step s s' -> step (app s t) (app s' t).

Fixpoint subst_list k (ctx : list term) (u : term) : term :=
  match ctx with
  | [] => u
  | t::ctx => subst_list (S k) ctx (subst u k t)
  end.

(* recursively substitute each local context *)
Fixpoint flatten (u : eterm) : term :=
  let '(closure ctx t) := u in subst_list 0 (map flatten ctx) t.

Lemma subst_list_app k ctx s t :
  subst_list k ctx (app s t) = app (subst_list k ctx s) (subst_list k ctx t).
Proof.
  elim: ctx k s t => /=; first done.
  move=> t ctx IH k s' t'. by rewrite IH.
Qed.

Lemma subst_list_lam k ctx s :
  subst_list k ctx (lam s) = lam (subst_list (S k) ctx s).
Proof.
  elim: ctx k s => /=; first done.
  move=> t ctx IH k s. by rewrite IH.
Qed.

(*
Forall (fun t => 
(exists t', t = closure (map (closure []) ctx) t') \/ 
(exists t', t = closure [] (subst_list 0 ctx t'))) ts ->
*)

Lemma Forall2_consE {X : Type} {P : X -> X -> Prop} {x1 l1 x2 l2} : 
  Forall2 P (x1::l1) (x2::l2) -> P x1 x2 /\ Forall2 P l1 l2.
Proof. move=> H. by inversion H. Qed.

Inductive ctx_size : nat -> list eterm -> Prop :=
  | ctx_size_nil : ctx_size 0 []
  | ctx_size_cons n ctx1 m ctx2 t :
      ctx_size n ctx1 -> ctx_size m ctx2 -> ctx_size (1+n+m) ((closure ctx1 t)::ctx2).

Inductive closureT (P : list eterm -> Type) : eterm -> Type :=
  | closureT_closure ctx t : P ctx -> closureT P (closure ctx t).

Inductive contextT (P : eterm -> Type) : list eterm -> Type :=
  | contextT_nil : contextT P []
  | contextT_cons u ctx : P u -> contextT P ctx -> contextT P (u::ctx).

Definition contextTI (P : eterm -> Type) : (forall u, P u) -> forall ctx, contextT P ctx.
Proof.
  move=> H. elim.
  - apply: contextT_nil.
  - move=> ???. apply: contextT_cons. apply: H. done.
Defined.

Inductive Plist {X : Type} (P : X -> Type) : list X -> Type :=
  | Plist_nil : Plist P []
  | Plist_cons x l : P x -> Plist P l -> Plist P (x::l).

Unset Implicit Arguments.

Definition Flist {X : Type} (P : X -> Type) (f : forall l, P l) (l : list X) : Plist P l.
Proof.
  elim: l.
  - apply: Plist_nil.
  - move=> x l IH. apply: Plist_cons.
    + apply: f.
    + apply: IH.
Defined.

Definition closureTI (P : eterm -> Type) : (forall ctx t, Plist P ctx -> P (closure ctx t)) -> forall u, P u :=
  fun H => fix f (u : eterm) : P u :=
  match u with
  | closure ctx t => H ctx t (Flist P f ctx)
  end.

(* using unary parametricity similar to rosetrees *)
Fixpoint closure_rect (P : eterm -> Type) (H : forall ctx t, Plist P ctx -> P (closure ctx t)) u : P u :=
  match u with
  | closure ctx t => H ctx t (Flist P (closure_rect P H) ctx)
  end.

Fixpoint term_size (t : term) : nat :=
  match t with
  | var n => n
  | app s t => 1 + term_size s + term_size t
  | lam s => 1 + term_size s
  end.

Definition eterm_size (u : eterm) : nat.
Proof.
  refine (closure_rect (fun=> nat) _ u).
  intros ?? H. induction H.
  - exact (term_size t).
  - exact (1 + p + IHPlist).
Defined.

Definition context_size (ctx : list eterm) : nat.
Proof.
  refine (closure_rect (fun=> nat) _ (closure ctx (var 0))).
  intros ?? H. induction H.
  - exact 0.
  - exact (1 + p + IHPlist).
Defined.

Lemma context_size_cons ctx1 t ctx2 :
  context_size ((closure ctx1 t)::ctx2) = 1 + (context_size ctx1) + (context_size ctx2).
Proof. done. Qed.


(* induction/recursion principle wrt. a decreasing measure f *)
(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.


Lemma ind_on_der ts1 ts2 ctx1 ctx2 s1 s2:
  Forall2 (fun t1 t2 => flatten t1 = flatten t2) ts1 ts2 ->
  flatten (closure ctx1 s1) = flatten (closure ctx2 s2) ->
  halt_cbn ts1 ctx1 s1 ->
  halt_cbn ts2 ctx2 s2.
Proof.
  move=> ++ H. elim: H ts2 ctx2 s2; clear ts1 ctx1 s1.
  - move=> ts ctx t ctx' ? IH ts2 ctx2 s2.
    move=> ? /= ?.
    have : flatten (closure ctx t) = flatten (closure ctx2 s2) by admit.
    move=> ?.
    by apply: (IH ts2 ctx2 s2).
  - move=> ts1 ctx1 n t ? IH ts2 ctx2 s2 ?.
    move=> /= ?.
    apply: (IH ts2 ctx2 s2).
    done.
    admit. (* by closedness *)
  - move=> ts1 ctx1 s t ? IH ts2 ctx2 s2 ?.
    move=> /=. rewrite subst_list_app.
    (* maybe here induction on ctx2 size for var elimination? *)
    case: s2.
    + move=> [|n]; last by admit.
      case: ctx2 => [|t2 ctx2]; first done.
      move=> /=.
      have ->: subst_list 1 (map flatten ctx2) (flatten t2) = flatten t2.
      admit.
      case: t2 => ctx' t2.
      have : exists t21 t22, t2 = app t21 t22 by admit.
      (* variable case problematic? needs more recursion? *)
      move=> [t21] [t22] -> /=.
      rewrite subst_list_app.
      move=> [??]. apply: halt_var_0. apply: halt_app.
      apply: IH.
      admit. admit. (* looks good *)
    + move=> ??.       rewrite subst_list_app.
    move=> [??].  apply: halt_app.
    apply: IH. admit. admit. (* looks good *)
    + admit.
  - move=> t1 ts1 ctx1 s1 ? IH ts2 ctx2 s2.
    case: ts2 => [|t2 ts2].
    { move=> H. inversion H. }
    move=> /Forall2_consE [??].
    case: s2.
    + move=> [|n]; last admit.
      move=> /=.
      case: ctx2 => [|[ctx2' t2'] ctx2]; first admit.
      move=> /= ?.
      apply: halt_var_0.
      have : exists t2'', t2' = lam t2'' by admit.
      move=> [? ->].
      apply: halt_lam_ts.
      apply: IH.
      done.
      admit. (* looks promising *)
    + admit.
    + move=> s2 /=. rewrite !subst_list_lam.
      move=> [?].       apply: halt_lam_ts.
      apply: IH. done.
      admit.
  - admit. (* similar *)



  elim /(measure_rect context_size): ctx1 s1 ts1 s2 ts2 ctx2.
  move=> ctx1 IH s1.
  elim: s1 ctx1 IH.
  - move=> [|n] [|[ctx' t'] ctx1].
    + by move=> ? > ?? /halt_cbnE.
    + move=> IH ts1 s2 ts2 ctx2 /= ??.
      move=> /halt_cbnE. apply: IH.
      * move=> /=. rewrite context_size_cons. lia.
      * done.
      * admit. (* doable *)
    + by move=> ? > ?? /halt_cbnE.
    + move=> IH ts1 s2 ts2 ctx2 /= ??.
      move=> /halt_cbnE. apply: IH.
      * move=> /=. rewrite context_size_cons. lia.
      * done.
      * admit. (* doable *)
  - move=> s'1 IH1. s'2 IH2 ts1 s2 ts2 ctx1 ctx2 /=.
    move=> Hts. rewrite subst_list_app.
    case: s2.
    + admit.
    + move=> s''1 s''2. rewrite subst_list_app.
      move=> [] /IH1 {}IH1 ?.
      move=> /halt_cbnE ?. apply: halt_app.
      apply: IH1; [|eassumption].
      by  constructor.
    + move=> ?. by rewrite subst_list_lam.
  - move=> s'1 IH ts1 s2 ts2 ctx1 ctx2 /=. case: s2.
    + admit.
    + move=> >. by rewrite subst_list_app subst_list_lam.
    + move=> s'2 Hts. rewrite !subst_list_lam.
      move=> [?].
      move: ts2 ts1 Hts => [|t1 ts1] [|t2 ts2].
      * move=> *. by apply: halt_lam.
      * move=> *. by apply: halt_lam.
      * move=> H. by inversion H.
      * move=> /Forall2_consE [? ?] /halt_cbnE H'. apply: halt_lam_ts.
        move: H'. apply: IH.
        ** done.
        ** move=> /=. admit. (* doable with well-formedness *)
*)

(* interpreter *)
Definition many_app s ts := fold_left app ts s.


Lemma halt_cbn_closed {ts ctx1 ctx2 s} : closed s -> halt_cbn ts ctx1 s -> halt_cbn ts ctx2 s.
Proof. Admitted.

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

Definition rho (s : term) := 
  let C := lam (lam (app (var 0) (lam (app (app (app (var 2) (var 2)) (var 1)) (var 0))))) in
  lam (app (app (app C C) s) (var 0)).

Lemma rho_spec s t ts : closed s -> 
  halt_cbn (t::ts) [] (app s (rho s)) ->
  halt_cbn (t::ts) [] (rho s).
Proof.
  move=> Hs. rewrite /rho.
  move=> /halt_cbnE H'.
  do ? constructor.
Admitted.

(* given n m, if m = n then s else t *)
Definition nat_beq s t := rho (lam (lam (lam (
  (* [m n nat_beq] *) many_app (var 1) [
      many_app (var 0) [s; lam t];
      lam (many_app (var 1) [t; lam (app (app (var 4) (var 1)) (var 0))])
  ])))).

Lemma nat_beq_closed {s t} : closed s -> closed t -> closed (nat_beq s t).
Proof. Admitted. 

(*
Lemma subst_nat_beq {s t} n u : subst (nat_beq s t) n u = nat_beq (subst s n u) (subst t n u).
Proof.
  rewrite /nat_beq /=.
*)

Lemma halt_cbn_app_closed_r {ts ctx s t} : 
  closed t ->
  halt_cbn ((closure [] t)::ts) ctx s ->
  halt_cbn ts ctx (app s t).
Proof. Admitted.

Lemma halt_cbn_app_var_r {ts ctx s t n} : 
  nth_error ctx n = Some t ->
  halt_cbn (t::ts) ctx s ->
  halt_cbn ts ctx (app s (var n)).
Proof. Admitted.

Arguments halt_cbn_app_var_r {ts ctx s t n} & _.

Lemma nat_beq_spec s t n m ts : closed s -> closed t ->
  halt_cbn ts [] (if Nat.eqb n m then s else t) ->
  halt_cbn ts [] (app (app (nat_beq s t) (enc_nat n)) (enc_nat m)).
Proof.
  move=> Hs Ht.
  elim: n m.
  - move=> [|m] /= H'.
    + do ? constructor. by apply: (halt_cbn_closed Hs H').
    + do ? constructor. by apply: (halt_cbn_closed Ht H').
  - move=> n IH [|m] /= H'.
    + do ? constructor. by apply: (halt_cbn_closed Ht H').
    + move: H' => /IH /halt_cbnE /halt_cbnE H'.
      do 2 constructor.
      apply: rho_spec. { move=> n' t' /=. by rewrite Hs Ht. }
      rewrite -/(nat_beq s t).
      move: (nat_beq s t) H' => ? H'.
      do ?
      first [
        apply: (halt_cbn_app_closed_r (enc_nat_closed _)) |
        apply: halt_cbn_app_var_r; [apply: erefl|] |
        constructor].
      done.
Qed.

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

(* substitute s n t *)
Definition substituter t := rho (lam (lam (lam (
    (* [n s substituter] *) 
  many_app (var 1) [
    (* case s = var n *)     lam (app (app (nat_beq (var 0) (var 2)) (var 1)) t);
    (* case s = app s' t' *) (lam (lam (mk_app 
      (app (app (app (var 4) (var 3)) (var 2)) (var 1))
      (app (app (app (var 4) (var 3)) (var 2)) (var 0)))));
    (* case s = lam s' *) (lam (mk_lam
      (app (app (app (var 3) (var 2)) (mk_S (var 1))) (var 0))
    ))])))).
  
Lemma substituter_spec s t n ts : closed t ->
  halt_cbn ts [] (enc_term (subst s n t)) ->
  halt_cbn ts [] (app (app (substituter t) (enc_term s)) (enc_nat n)).
Proof.
  move=> Ht.
  elim: s n.
  - move=> m n H'.
    do 2 constructor.
    apply: rho_spec. { move=> n' t' /=. by rewrite Ht. }
    rewrite -/(substituter t). move: (substituter _) => ?.
    Opaque nat_beq.
    do ?
    first [
      apply: (halt_cbn_app_closed_r (enc_nat_closed _)) |
      apply: halt_cbn_app_var_r; [apply: erefl|] |
      constructor].
    done.

  - move=> n IH [|m] /= H'.
    + do ? constructor. by apply: (halt_cbn_closed Ht H').
    + move: H' => /IH /halt_cbnE /halt_cbnE H'.
      do 2 constructor.
      apply: rho_spec. { move=> n' t' /=. by rewrite Hs Ht. }
      rewrite -/(nat_beq s t).
      move: (nat_beq s t) H' => ? H'.
      do ?
      first [
        apply: (halt_cbn_app_closed_r (enc_nat_closed _)) |
        apply: halt_cbn_app_var_r; [apply: erefl|] |
        constructor].
      done.

(* right direction, almost*
Lemma asd ts1 ts2 ctx1 ctx2 s1 s2:
  Forall2 (fun t1 t2 => flatten t1 = flatten t2) ts1 ts2 ->
  flatten (closure ctx1 s1) = flatten (closure ctx2 s2) ->
  halt_cbn ts1 ctx1 s1 ->
  halt_cbn ts2 ctx2 s2.
Proof.
  elim /(measure_rect context_size): ctx1 s1 ts1 s2 ts2 ctx2.
  move=> ctx1 IH s1.
  elim: s1 ctx1 IH.
  - move=> [|n] [|[ctx' t'] ctx1].
    + by move=> ? > ?? /halt_cbnE.
    + move=> IH ts1 s2 ts2 ctx2 /= ??.
      move=> /halt_cbnE. apply: IH.
      * move=> /=. rewrite context_size_cons. lia.
      * done.
      * admit. (* doable *)
    + by move=> ? > ?? /halt_cbnE.
    + move=> IH ts1 s2 ts2 ctx2 /= ??.
      move=> /halt_cbnE. apply: IH.
      * move=> /=. rewrite context_size_cons. lia.
      * done.
      * admit. (* doable *)
  - move=> s'1 IH1. s'2 IH2 ts1 s2 ts2 ctx1 ctx2 /=.
    move=> Hts. rewrite subst_list_app.
    case: s2.
    + admit.
    + move=> s''1 s''2. rewrite subst_list_app.
      move=> [] /IH1 {}IH1 ?.
      move=> /halt_cbnE ?. apply: halt_app.
      apply: IH1; [|eassumption].
      by  constructor.
    + move=> ?. by rewrite subst_list_lam.
  - move=> s'1 IH ts1 s2 ts2 ctx1 ctx2 /=. case: s2.
    + admit.
    + move=> >. by rewrite subst_list_app subst_list_lam.
    + move=> s'2 Hts. rewrite !subst_list_lam.
      move=> [?].
      move: ts2 ts1 Hts => [|t1 ts1] [|t2 ts2].
      * move=> *. by apply: halt_lam.
      * move=> *. by apply: halt_lam.
      * move=> H. by inversion H.
      * move=> /Forall2_consE [? ?] /halt_cbnE H'. apply: halt_lam_ts.
        move: H'. apply: IH.
        ** done.
        ** move=> /=. admit. (* doable with well-formedness *)
*)
(*
Lemma asd ts1 ts2 ctx1 ctx2 s1 s2:
  Forall2 (fun t1 t2 => flatten t1 = flatten t2) ts1 ts2 ->
  flatten (closure ctx1 s1) = flatten (closure ctx2 s2) ->
  halt_cbn ts1 ctx1 s1 ->
  halt_cbn ts2 ctx2 s2.
Proof.
  elim: s1 ts1 s2 ts2 ctx1 ctx2.
  - move=> + ts1 s2 ts2 ctx1 ctx2 Hts.
    admit.
  - move=> s'1 IH1 s'2 IH2 ts1 s2 ts2 ctx1 ctx2 /=.
    move=> Hts. rewrite subst_list_app.
    case: s2.
    + admit.
    + move=> s''1 s''2. rewrite subst_list_app.
      move=> [] /IH1 {}IH1 ?.
      move=> /halt_cbnE ?. apply: halt_app.
      apply: IH1; [|eassumption].
      by  constructor.
    + move=> ?. by rewrite subst_list_lam.
  - move=> s'1 IH ts1 s2 ts2 ctx1 ctx2 /=. case: s2.
    + admit.
    + move=> >. by rewrite subst_list_app subst_list_lam.
    + move=> s'2 Hts. rewrite !subst_list_lam.
      move=> [?].
      move: ts2 ts1 Hts => [|t1 ts1] [|t2 ts2].
      * move=> *. by apply: halt_lam.
      * move=> *. by apply: halt_lam.
      * move=> H. by inversion H.
      * move=> /Forall2_consE [? ?] /halt_cbnE H'. apply: halt_lam_ts.
        move: H'. apply: IH.
        ** done.
        ** move=> /=. admit. (* doable with well-formedness *)


(* same issue *)
Lemma asd ts s (ctx : list eterm) t:
  bound (S (length ctx)) s ->
  halt_cbn ts ctx (subst s (length ctx) (flatten t)) ->
  halt_cbn ts (ctx ++ [t]) s.
Proof.
  elim: s ts ctx t.
  - move=> [|n] ts ctx /=.
    + admit.
    + admit. (* closed *)
  - move=> s1 IH1 s2 IH2 ts ctx t Hs /=.
    move=> /halt_cbnE ?.
    apply: halt_app. apply: IH1. admit. (* easy *)

    have := (IH1 (s2 :: ts) (ctx1 ++ ctx2) ctx1 ctx2 erefl).
    rewrite -Hctx. apply. done.

(* still no *)
Lemma asd ts s (ctx : list term) ctx1 ctx2:
  ctx = ctx1 ++ ctx2 ->
  halt_cbn 
    (map (fun t => closure (map (closure []) ctx1) (subst_list (length ctx1) ctx2 t)) ts)
    (map (closure []) ctx1) (subst_list (length ctx1) ctx2 s) ->
  halt_cbn (map (closure (map (closure []) ctx)) ts) (map (closure []) ctx) s.
Proof.
  elim: s ts ctx ctx1 ctx2.
  - move=> [|n] ts ctx /=.
    + admit.
    + admit. (* closed *)
  - move=> s1 IH1 s2 IH2 ts ctx ctx1 ctx2 Hctx /=.
    rewrite subst_list_app.
    move=> /halt_cbnE ?.
    apply: halt_app.
    have := (IH1 (s2 :: ts) (ctx1 ++ ctx2) ctx1 ctx2 erefl).
    rewrite -Hctx. apply. done.
    (*
    move=> /halt_cbnE /IH1 {}IH1.
    apply: halt_app.

    admit. (* almost, needs subst in ts *)*)
  - move=> s IH [|t' ts'] ctx ctx1 ctx2 Hctx /=.
    + move=> *. apply: halt_lam.
    + rewrite subst_list_lam. move=> /halt_cbnE ?.
      apply: halt_lam_ts.
      apply: (IH ts' (t' :: ctx) (t'::ctx1) ctx2).
      * by rewrite Hctx.
      * done.

(* almost *)
Lemma asd ts s ctx ctx1 ctx2:
  ctx = ctx1 ++ ctx2 ->
  halt_cbn (map (closure []) ts) (map (closure []) ctx1) (subst_list (length ctx1) ctx2 s) ->
  halt_cbn (map (closure []) ts) (map (closure []) ctx) s.
Proof.
  elim: s ts ctx ctx1 ctx2.
  - move=> [|n] ts ctx /=.
    + admit.
    + admit. (* closed *)
  - move=> s1 IH1 s2 IH2 ts ctx ctx1 ctx2 Hctx /=.
    rewrite subst_list_app.
    move=> /halt_cbnE.
    admit.
    (*
    move=> /halt_cbnE /IH1 {}IH1.
    apply: halt_app.

    admit. (* almost, needs subst in ts *)*)
  - move=> s IH [|t' ts'] ctx ctx1 ctx2 Hctx /=.
    + move=> *. apply: halt_lam.
    + rewrite subst_list_lam. move=> /halt_cbnE ?.
      apply: halt_lam_ts.
      apply: (IH ts' (t' :: ctx) (t'::ctx1) ctx2).
      * by rewrite Hctx.
      * done.
*)
(* actually does not work because removing from ctx shifts indices and subst is plain *)
(*
Lemma asd ts s t ctx :
    halt_cbn (map (closure ctx) ts) ctx (subst s 0 t) ->
    halt_cbn (map (closure ctx) ts) ((closure ctx t)::ctx) s.
Proof.
  elim: s t ts ctx.
  - move=> [|n] t ts ctx /=.
    + move=> ?. by apply: halt_var_0.
    + admit. (* closed *)
  - move=> s1 IH1 s2 IH2 t ts ctx /=.
    move=> /halt_cbnE. move=> /(IH1 _ (_ :: _)) {}IH1.
    apply: halt_app.
    admit. (* almost, needs subst in ts *)
  - move=> s IH t [|t' ts'] ctx /=.
    + move=> *. apply: halt_lam.
    + move=> /halt_cbnE ?. apply: halt_lam_ts.
*)

(*
Lemma asd ts s t ctx :
    halt_cbn (map (closure ctx) ts) ctx (subst s 0 t) ->
    halt_cbn (map (closure ctx) ts) ((closure ctx t)::ctx) s.
Proof.
  move Ets': (map _ _) => ts'.
  move Hu: (subst s 0 t) => u H. elim: H s t ts Hu Ets'; clear ts' ctx u.
  - admit.
  - admit.
  - move=> ts ctx s t ? IH [].
    + move=> [|n]; [|done].
      move=> ? ts' /= -> ?. subst.
      apply: halt_var_0.
      apply: halt_app.
      have := IH (var 0) s (t::ts') erefl erefl.
      by move=> /halt_cbnE. (* this interchange is the right technique! *)
    + move=> s1 s2 t1 ts' /= [] /IH {}IH ??. subst.
      apply: halt_app.
      have := IH ((subst s2 0 t1)::ts') erefl.
      admit. (* closures in ts *)
    + done.
  - move=> t ts ctx s ? IH [] /=.
    + move=> [|?]; [|done].
      move=> t' [|t'' ts'']; [done|].
      move=> /= -> [? ?]. subst. apply: halt_var_0. by apply: halt_lam_ts.
    + done.
    + move=> s1 s2 [|t'' ts'']; [done|].
      move=> [?] [??]. subst.
      apply: halt_lam_ts.
      have := IH (var 0) (subst s1 1 s2) ts'' erefl.

      apply: IH.
    
      have := IH (var 0) s ts'' erefl erefl.

      
  - move=> ctx s [].
    + move=> [|n]; [|done].
      move=> ? ts /= -> ? ?. apply: halt_var_0. by apply: halt_lam.
    + done.
    + move=> *. by apply: halt_lam.
  
      apply: IH.


      apply: (IH s).
  move=> ts ctx t ctx' ? IH.
    move=> []; [|done|done].
    move=> [|n]; [|done].
    move=> t' ts' /= ->.
    move=> >. 
*)

(* take care that is works only for closed steps *)
Lemma step_halt_cbn s t ts ctx : step s t ->
  halt_cbn ts ctx s -> halt_cbn ts ctx t.
Proof.
  move=> Hst. elim: Hst ts ctx; clear s t.
  - move=> s t ts ctx /halt_cbnE /halt_cbnE.
    admit. (* needs closure resolution lemma *)
  - move=> s s' t ? IH ts ctx /halt_cbnE /IH ?.
    by apply: halt_app.
Admitted.

Lemma step_halt_cbn' s t ts ctx : step s t ->
  halt_cbn ts ctx t -> halt_cbn ts ctx s.
Proof.
  move=> Hst. elim: Hst ts ctx; clear s t.
  - move=> s t ts ctx H. apply: halt_app. apply: halt_lam_ts.
    admit. (* needs closure resolution lemma *)
  - move=> s s' t ? IH ts ctx /halt_cbnE /IH ?.
    by apply: halt_app.
Admitted.

Inductive eval_cbn : term -> term -> Prop :=
  | eval_lam s :
      eval_cbn (lam s) (lam s)
  | eval_app s u t v :
      eval_cbn s (lam u) -> eval_cbn (subst u 0 t) v -> eval_cbn (app s t) v.

Inductive halt_cbn : list eterm -> eterm -> Prop :=
  | halt_var_0 ts ctx t :
      halt_cbn ts t ->
      halt_cbn ts (closure (t::ctx) (var 0))
  | halt_var_S ts ctx n t :
      halt_cbn ts (closure ctx (var n)) ->
      halt_cbn ts (closure (t::ctx) (var (S n)))
  | halt_app ts ctx s t :
      halt_cbn ((closure ctx t) :: ts) (closure ctx s) ->
      halt_cbn ts (closure ctx (app s t))
  | halt_lam_ts t ts ctx s :
      halt_cbn ts (closure (t::ctx) s) ->
      halt_cbn (t::ts) (closure ctx (lam s))
  | halt_lam ctx s :
      halt_cbn [] (closure ctx (lam s)).

#[local] Notation "! t" := (closure [] t) (at level 50).

(*
Definition closed_equiv s1 s2 := 
  let '(closure ctx1 t1) := s1 in
  let '(closure ctx2 t2) := s2 in
  (* forall free variables x in s1 and s2 ctx1 x = ctx2 x *)
*)


Lemma halt_cbn_closed u ts ctx : halt_cbn ts (! u) -> closed u -> halt_cbn ts (closure ctx u).
Proof.
  move Eu': (! u) => u' Hu'. elim: Hu' ctx u Eu'.
  - by move=> > ?? > [].
  - by move=> > ?? > [].
  - move=> > ? IH > [] ??. subst.
    move=> /closed_app [] /IH {}IH ?.
    apply: halt_app.
Admitted.







Lemma halt_cbn_equiv ts u ts' u' :
  halt_cbn ts u ->
  Forall2 (fun t t' => flatten t = flatten t') ts ts' ->
  flatten u = flatten u' ->
  halt_cbn ts' u'.
Proof.
  move=> H. elim: H ts' u'; clear ts u.
  - move=> ts ctx t ? IH ts' u' /= ??.
    admit.
  - admit.
  - move=> ts ctx s t ? IH ts' u' /=.
    case: u' => ctx2 [].
    + admit. (* hard case *)
    + move=> t1 t2 /=. rewrite !subst_list_app.
      move=> H1 [Et1 Et2]. apply: halt_app.
      apply: IH.
      * by constructor.
      * done.
    + move=> t' /=. by rewrite subst_list_app subst_list_lam.
  - move=> t ts ctx s ? IH [|t'' ts'] u'.
    + move=> H. by inversion H.
    + admit.
  - admit. (* easy *) 
Admitted.
      
      H2.
      move=> [] /(IH ts' (closure ctx2 t1)).
       /IH.
    
    move=> [|n].
      * move=> /= ?. case: ctx2 => [|v2 ctx2].
        ** move=> /=. admit. (* easy *)
        ** move=> /= ?. apply: halt_var_0.


        apply: IH.



  move Ets': (map _ _) => ts'.
  move Eu': (closure [] _) => u' H'.
  elim: H' ts Ets' u Eu'; clear ts' u'. 
  - done.
  - done.
  - move=> > ? IH ?? [] ctx [].
    + move=> n [] ?. have ->: n = 0 by admit.
      subst. case: ctx; first done.
      move=> t' ctx' /= Ht'.

(*
Lemma halt_cbn_flatten u ts : halt_cbn (map (closure []) (map flatten ts)) (closure [] (flatten u)) -> halt_cbn ts u.
Proof.
  move Ets': (map _ _) => ts'.
  move Eu': (closure [] _) => u' H'.
  elim: H' ts Ets' u Eu'; clear ts' u'. 
  - done.
  - done.
  - move=> > ? IH ?? [] ctx [].
    + move=> n [] ?. have ->: n = 0 by admit.
      subst. case: ctx; first done.
      move=> t' ctx' /= Ht'.
      apply: halt_var_0.
      case: t' Ht' => ctx'' [].
      *  
Admitted.
*)

Definition steps n x := Nat.iter n (obind step) (Some x).

Definition rho (s : term) := 
  let C := lam (lam (app (var 0) (lam (app (app (app (var 2) (var 2)) (var 1)) (var 0))))) in
  lam (app (app (app C C) s) (var 0)).

Lemma rho_closed s : closed s -> closed (rho s).
Proof. move=> Hs ?? /=. by rewrite Hs. Qed.


Lemma rho_spec s t ts ctx : closed s ->
  halt_cbn ts (closure ctx (app (app s (rho s)) (lam t))) ->
  halt_cbn ts (closure ctx (app (rho s) (lam t))).
Proof.
  move=> Hs H. apply: halt_app. rewrite /rho.
  apply: halt_lam_ts.
  apply: halt_app.
  apply: halt_app.
  apply: halt_app.
  apply: halt_lam_ts.
  apply: halt_lam_ts.
  apply: halt_app.
  apply: halt_var_0.
  apply: halt_cbn_flatten. rewrite /=. rewrite !Hs.
  do ? rewrite !subst_list_lam !subst_list_app /=.
  rewrite -/(rho s).
Lemma rho_spec s t ts ctx : closed s ->
  steps 9 (ts, closure ctx (app (rho s) (lam t))) = 
  
  steps 2 (ts, closure ctx (app (app s (rho s)) (lam t))).
Proof.
  rewrite /rho.
  move=> Hs /=.
  have HH : closure 

steps (app (rho s) (lam t)) (app (app s (rho s)) (lam t)).
Proof.
  move=> Hs. rewrite /rho. do ? do_step.
  rewrite /= (Hs 0). by apply: rt_refl.
Qed.

Lemma rho_spec s t : closed s -> steps (app (rho s) (lam t)) (app (app s (rho s)) (lam t)).
Proof.
  move=> Hs. rewrite /rho. do ? do_step.
  rewrite /= (Hs 0). by apply: rt_refl.
Qed.
  
  Opaque rho.
