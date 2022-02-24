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
Inductive halt_cbn : list eterm -> list eterm -> term -> Prop :=
  | halt_var_0 ts ctx t ctx' :
      halt_cbn ts ctx t ->
      halt_cbn ts ((closure ctx t)::ctx') (var 0)
  | halt_var_S ts ctx n t :
      halt_cbn ts ctx (var n) ->
      halt_cbn ts (t::ctx) (var (S n))
  | halt_app ts ctx s t :
      halt_cbn ((closure ctx t) :: ts) ctx s ->
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
  | var (S n) => True
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


Lemma asd ts s ctx :
  Forall (fun t => 
    (exists t', t = closure (map (closure []) ctx) t') \/ 
    (exists t', t = closure [] (subst_list 0 ctx t'))) ts ->
  halt_cbn ts [] (subst_list 0 ctx s) ->
  halt_cbn ts (map (closure []) ctx) s.
Proof.
  elim: s ts ctx.
  - move=> [|n] ts ctx /=.
    + admit.
    + admit. (* closed *)
  - move=> s1 IH1 s2 IH2 ts ctx Hts /=.
    rewrite subst_list_app.
    move=> /halt_cbnE /IH1 {}IH1.
    apply: halt_app.

    admit. (* almost, needs subst in ts *)
  - move=> s IH [|t' ts'] ctx /=.
    + move=> *. apply: halt_lam.
    + rewrite subst_list_lam. move=> /halt_cbnE ?.
      apply: halt_lam_ts.
      apply: IH.

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



Definition many_app s ts := fold_left app ts s.



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
