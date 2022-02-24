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

(*
Notation eterm := ((list term)*term)%type.
*)

Fixpoint eva (k : nat) (ts : list eterm) (vs : list eterm) (u : eterm) : bool :=
  match k with
  | 0 => false
  | S k =>
    match u with
    | closure ctx (var n) => (* look up term in ctx *)
        match nth_error ctx n with
        | None => false
        | Some t => eva k ts vs t
        end
    | closure ctx (app s t) => (* push argument *)
        eva k ((closure ctx t) :: ts) vs (closure ctx s)
    | closure ctx (lam s) => (* terminate or push onto context *)
        match ts with
        | [] => 
            match vs with
            | [] => true
            | v'::vs' => eva k [] vs' v'
            end
        | t'::ts' => eva k ts' (t'::vs) (closure (t'::ctx) s)
        end
    end
  end.

(* eva k ts vs u *)
(* domain predicate 
advantages: 
+ all functionality (subst, eqb, ...) in halt_cbv
+ tail-recursive (halt_cbv .. -> halt_cbv ..)
+ easy to simulate by stack machine /minsky machine?
*)



Inductive halt_cbv : list eterm -> list eterm -> eterm -> Prop :=
  | halt_var_0 ts vs ctx t :
      halt_cbv ts vs t ->
      halt_cbv ts vs (closure (t::ctx) (var 0))
  | halt_var_S ts vs ctx n t :
      halt_cbv ts vs (closure ctx (var n)) ->
      halt_cbv ts vs (closure (t::ctx) (var (S n)))
  | halt_app ts vs ctx s t :
      halt_cbv ((closure ctx t) :: ts) vs (closure ctx s) ->
      halt_cbv ts vs (closure ctx (app s t))
  | halt_lam_ts t ts vs ctx s :
      halt_cbv ts (t::vs) (closure (t::ctx) s) ->
      halt_cbv (t::ts) vs (closure ctx (lam s))
  | halt_lam_vs v vs ctx s :
      halt_cbv [] vs v ->
      halt_cbv [] (v::vs) (closure ctx (lam s))
  | halt_lam ctx s :
      halt_cbv [] [] (closure ctx (lam s)).



Inductive eval_cbv : list eterm -> list eterm -> eterm -> eterm -> Prop :=
  | eval_cbv_var_0 ts vs ctx t u :
      eval_cbv ts vs t u ->
      eval_cbv ts vs (closure (t::ctx) (var 0)) u
  | eval_cbv_var_S ts vs ctx n t u :
      eval_cbv ts vs (closure ctx (var n)) u ->
      eval_cbv ts vs (closure (t::ctx) (var (S n))) u
  | eval_cbv_app ts vs ctx s t u :
      eval_cbv ((closure ctx t) :: ts) vs (closure ctx s) u ->
      eval_cbv ts vs (closure ctx (app s t)) u
  | eval_cbv_lam_ts t ts vs ctx s u :
      eval_cbv ts (t::vs) (closure (t::ctx) s) u ->
      eval_cbv (t::ts) vs (closure ctx (lam s)) u
  | eval_cbv_lam_vs v vs ctx s u :
      eval_cbv [] vs v u ->
      eval_cbv [] (v::vs) (closure ctx (lam s)) (closure ctx (lam s))
  | eval_cbv_lam ctx s :
      eval_cbv [] [] (closure ctx (lam s)) (closure ctx (lam s)).

Lemma halt_eval ts vs t : halt_cbv ts vs t -> exists t', eval_cbv ts vs t t'.
Proof.
  elim.
  - move=> > ? [??]. eexists. apply: eval_cbv_var_0; eassumption.
  - move=> > ? [??]. eexists. apply: eval_cbv_var_S; eassumption.
  - move=> > ? [??]. eexists. apply: eval_cbv_app; eassumption.
  - move=> > ? [??]. eexists. apply: eval_cbv_lam_ts; eassumption.
  - move=> > ? [??]. eexists. apply: eval_cbv_lam_vs; eassumption.
  - move=> >.  eexists. apply: eval_cbv_lam; eassumption.
Qed.

(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

Fixpoint ren (xi : nat -> nat) (t : term) : term  :=
  match t with
  | var x => var (xi x)
  | app s t => app (ren xi s) (ren xi t)
  | lam t => lam (ren (scons 0 (funcomp S xi)) t)
  end.

  (*
(* non-capturing substitution *)
(* actually capturing could suffice since each flatclosure is closed *)
Fixpoint subst (sigma : nat -> term) (t : term) : term :=
  match t with
  | var x => sigma x
  | app s t => app (subst sigma s) (subst sigma t)
  | lam t => lam (subst (scons (var 0) (funcomp (ren S) sigma)) t)
  end.
*)

(* concept of well-formed ctx : position n contains only variables from remaining list *)
Fixpoint closed_ctx (ctx : list term) :=
  match ctx with
  | [] => True
  | t::ctx => bound (length ctx) t /\ closed_ctx ctx
  end.

Arguments closed_ctx : simpl never.

Fixpoint subst_list k (ctx : list term) (u : term) : term :=
  match ctx with
  | [] => u
  | t::ctx => subst_list (S k) ctx (subst u k t)
  end.

(* recursively substitute each local context *)
Fixpoint flatten (u : eterm) : term :=
  let '(closure ctx t) := u in subst_list 0 (map flatten ctx) t.

Definition many_app s ts := fold_left app ts s.

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

Lemma inv_main1 ts vs s : halt_cbv ts vs s ->
  closed (flatten s) -> needs eclosed (everything is closed after flatten...)
  Forall closed (map flatten ts) ->
  Forall (fun v => exists v', L.eval (flatten v) v') vs /\
  exists t, L.eval (many_app (flatten s) (map flatten ts)) t.
Proof.
  elim; clear ts vs s.
  - move=> ts vs ctx t ? /= IH Ht Hts. split; first done.
    admit. (* doable by closedness *)
  - move=> ts vs ctx n t u ? [IH1 IH2] /=. split; first done.
    admit. (* doable by closedness *)
  - move=> ts vs ctx s t u ? /= [IH1 IH2]. split; first done.
    by rewrite subst_list_app.
  - move=> t ts vs ctx s u ? /= [IH1 IH2]. split.
    { by move: IH1 => /(@Forall_inv_tail eterm). }
    rewrite subst_list_lam.
    have ? : ts = [] by admit. subst ts.
    rewrite /=.
    move: IH1 => /(@Forall_inv eterm) => - [t' Ht'].
    apply: L.eval_app.
    + apply: L.eval_abs.
    + apply: Ht'.
    + move: IH2. cbn. (* maybe not completely WRONG just knowledge of evaluation means different normal forms! *)
     admit.
  - move=> v vs ctx s u ? /= [IH1 IH2]. split.
    + constructor; [eexists; eassumption|done].
    + rewrite subst_list_lam. apply: L.eval_abs.
  - move=> ctx s /=. split; first done.
    rewrite subst_list_lam. apply: L.eval_abs.



Lemma inv_main1 ts vs s t : eval_cbv ts vs s t -> 
  Forall (fun v => exists v', L.eval (flatten v) v') vs /\
  L.eval (many_app (flatten s) (map flatten ts)) (flatten t).
Proof.
  elim; clear ts vs s t.
  - move=> ts vs ctx t u ? [IH1 IH2] /=. split; first done.
    admit. (* doable by closedness *)
  - move=> ts vs ctx n t u ? [IH1 IH2] /=. split; first done.
    admit. (* doable by closedness *)
  - move=> ts vs ctx s t u ? /= [IH1 IH2]. split; first done.
    by rewrite subst_list_app.
  - move=> t ts vs ctx s u ? /= [IH1 IH2]. split.
    { by move: IH1 => /(@Forall_inv_tail eterm). }
    rewrite subst_list_lam.
    have ? : ts = [] by admit. subst ts.
    rewrite /=.
    move: IH1 => /(@Forall_inv eterm) => - [t' Ht'].
    apply: L.eval_app.
    + apply: L.eval_abs.
    + apply: Ht'.
    + move: IH2. cbn. (* maybe not completely WRONG just knowledge of evaluation means different normal forms! *)
     admit.
  - move=> v vs ctx s u ? /= [IH1 IH2]. split.
    + constructor; [eexists; eassumption|done].
    + rewrite subst_list_lam. apply: L.eval_abs.
  - move=> ctx s /=. split; first done.
    rewrite subst_list_lam. apply: L.eval_abs.

Lemma inv_main1 ts vs s t : eval_cbv ts vs s t -> 
  Forall (fun v => exists v', L.eval (flatten v) v') vs /\
  L.eval (many_app (flatten s) (map flatten ts)) (flatten t).
Proof.
  elim.
  - 

Lemma main1 s t : L.eval s t -> exists t', t = flatten t' /\ eval_cbv [] [] (closure [] s) t'.
Proof.
  elim; clear s t. 
  { move=> s. exists (closure [] (lam s)).
    split. done. apply: eval_cbv_lam. }
  move=> s u t t' v ? IH1 ? IH2 ? IH3.
  eexists. split. admit.
  apply: eval_cbv_app.
  apply: halt_app.










(*
  k   : step index
  ctx : context for term variables
  u term to reduce
  properties: does not need subst, Nat.eqb
*)
Fixpoint eva_cbv (k : nat) (ctx : list term) (u : term) : option term :=
  match k with
  | 0 => None
  | S k =>
    match u with
    | var n =>
        match skipn n ctx with
        | [] => None
        | t::ts => eva_cbv k ts t
        end
    | lam s => Some (lam s)
    | app s t =>
        match eva_cbv k ctx s, eva_cbv k ctx t with
        | Some (lam s'), Some t' => eva_cbv k (t'::ctx) s'
        | _, _ => None
        end
    end
  end.

(* cbv evaluation without substitution *)
(* actually wrong beause eval_cbv (t'::ctx) s' u does forget the larger ctx for u; needs pairs of ctx, term *)
Inductive eval_cbv (ctx : list term) : term -> term -> Prop :=
  | eval_var n t ctx' u :
      skipn n ctx = t::ctx' -> eval_cbv ctx' t u -> eval_cbv ctx (var n) u
  | eval_app s t s' t' u :
      eval_cbv ctx s (lam s') -> eval_cbv ctx t t' -> eval_cbv (t'::ctx) s' u -> eval_cbv ctx (app s t) u
  | eval_lam s :
      eval_cbv ctx (lam s) (lam s).

(* function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

(* stream cons *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with | 0 => x | S n => xi n end.

Fixpoint ren (xi : nat -> nat) (t : term) : term  :=
  match t with
  | var x => var (xi x)
  | app s t => app (ren xi s) (ren xi t)
  | lam t => lam (ren (scons 0 (funcomp S xi)) t)
  end.

(* non-capturing substitution *)
Fixpoint subst (sigma : nat -> term) (t : term) : term :=
  match t with
  | var x => sigma x
  | app s t => app (subst sigma s) (subst sigma t)
  | lam t => lam (subst (scons (var 0) (funcomp (ren S) sigma)) t)
  end.

(* concept of well-formed ctx : position n contains only variables from remaining list *)
Fixpoint closed_ctx (ctx : list term) :=
  match ctx with
  | [] => True
  | t::ctx => bound (length ctx) t /\ closed_ctx ctx
  end.

Arguments closed_ctx : simpl never.
Arguments skipn {A} !n !l /.

Fixpoint subst_ctx (ctx : list term) (u : term) : term :=
  match ctx with
  | [] => u
  | t::ctx => subst_ctx ctx (subst (scons t var) u)
  end.

Lemma aux1 u t ctx u' :
  eval_cbv ctx (subst (scons t var) u) u' -> eval_cbv (t::ctx) u u'.
Proof.
  move Ev: (subst _ u) => v Hu'.
  elim: Hu' u t Ev; clear ctx u' v.
  - move=> ctx n t' ctx' u.
    move=> Hctx' ? IH []; [|done|done].
    move=> [|m].
    + move=> /= t ?. subst t.
      apply: eval_var; [reflexivity|].
      by apply: eval_var; [eassumption|].
    + move=> /= t [->].
      by apply: eval_var; [eassumption|].
  - move=> ctx s t s' t' u.
    move=> ? IH1 ? IH2 ? IH3 [].
    + move=> [|n]; last done.
      move=> t'' /= ?. subst t''.
      apply: eval_var; [reflexivity|].
      by apply: eval_app; eassumption.
    + move=> s1' s2' t'' /= [].
      move=> /IH1 ? /IH2 ?.
      apply: eval_app; [eassumption|eassumption|].
      admit. (* something doesnt work, maybe needs closedness *)
    + done.
  - move=> ctx s [].
    + move=> [|?]; last done.
      move=> t /= ?. subst t.
      apply: eval_var; [reflexivity|].
      by apply: eval_lam.
    + done.
    + move=> s' t /= [<-].
      Admitted.

(*
Lemma aux1 u t ctx u' : closed_ctx (u::t::ctx) -> 
  eval_cbv ctx (subst (scons t var) u) u' -> eval_cbv (t::ctx) u u'.
Proof.
  move Ev: (subst _ u) => v Hctx Hu'.
  elim: Hu' u t Hctx Ev; clear ctx u' v.
  - move=> ctx n t' ctx' u.
    move=> Hctx' ? IH []; [|done|done].
    move=> [|m].
    + move=> /= t ??. subst t.
      apply: eval_var; [reflexivity|].
      by apply: eval_var; [eassumption|].
    + move=> /= t ? [->].
      by apply: eval_var; [eassumption|].
  - move=> ctx s t s' t' u.
    move=> ? IH1 ? IH2 ? IH3 [].
    + move=> [|n]; last done.
      move=> t'' Hctx /= ?. subst t''.
      apply: eval_var; [reflexivity|].
      by apply: eval_app; eassumption.
    + move=> s1' s2' t'' Hctx /= [].
      move /IH1.
      |eassumption|].
    s2 Hctx.
    

    admit. (* impossible *)
  - move=> ctx s'1 s'2 s'' t'' {}u.
    move=> ? IH1 ? IH2 ? IH3 [].
    + move=> [|n]; last by admit. (* doable *)
      move=> t /= -> ??.
      apply: eval_var; first reflexivity.
      apply: eval_app.
      * have : eval_cbv ctx s'1 (lam s'') by admit.
        apply.
      * have : eval_cbv ctx s'2 t'' by admit.
        apply.
      * admit. (* incorrect *)
    + move=> /= s1 s2 t [] /IH1 {}IH1 /IH2 {}IH2 ??.
      apply: eval_app.
      * apply: IH1. admit. admit.
      * apply: IH2. admit. admit.
      * 

Lemma aux1 s t u : eval_cbv [] (subst_ctx ctx u) u' -> eval_cbv [t] s u.
Proof.
  move Es': (subst s 0 t) => s' Hs Ht Hu.
  elim: Hu s t Es' Hs Ht.
  - move=> ctx n t' ctx' {}u.
    admit. (* impossible *)
  - move=> ctx s'1 s'2 s'' t'' {}u.
    move=> ? IH1 ? IH2 ? IH3 [].
    + move=> [|n]; last by admit. (* doable *)
      move=> t /= -> ??.
      apply: eval_var; first reflexivity.
      apply: eval_app.
      * have : eval_cbv ctx s'1 (lam s'') by admit.
        apply.
      * have : eval_cbv ctx s'2 t'' by admit.
        apply.
      * admit. (* incorrect *)
    + move=> /= s1 s2 t [] /IH1 {}IH1 /IH2 {}IH2 ??.
      apply: eval_app.
      * apply: IH1. admit. admit.
      * apply: IH2. admit. admit.
      * 
  -


Admitted.
*)

Lemma main1 s t : closed s -> L.eval s t -> eval_cbv [] s t.
Proof.
  move=> Hs Hst. elim: Hst Hs.
  - move=> *. by apply: eval_lam.
  - move=> > ? IH1 ? IH2 ? IH3 /closed_app [Hs Ht].
    move: (Hs) (Ht) => /IH1 {}IH1 /IH2 {}IH2.
    apply: eval_app.
    + by apply: IH1.
    + by apply: IH2.
    + apply: aux1.
      * admit. (* doable *)
      * admit. (* doable *)
      * apply: IH3. admit. (* doable *)
Admitted.



(* or which lemma? *)
Lemma asd t ctx u u' : eval_cbv (t::ctx) u u' ->
  eval_cbv ctx (subst u 0 t) u'.
Proof.
  rewrite [in eval_cbv ctx](erefl : ctx = tl (t :: ctx)).
  elim.
  - move=> [|t0 ctx0]; first by case.
    + move=> t' ctx' {}u /= [] _ ->.
  
  elim: k t ctx u; first done.
  move=> k IH t ctx [].
  - move=> [|n] /=.
    + move=> <-.  apply. done. by exists k.
    + case En: (skipn n ctx) => [|t' ctx'].
      * by exists 0.
      * admit. (*?*)
  - move=> s' t' /=.

Fixpoint subst_ctx ctx u :=
  match u with
  | var n =>
      match nth_error ctx n with
      | Some t => t
      | None => u
      end
  | app s t => app (subst_ctx ctx s) (subst_ctx ctx t)
  | lam s => lam (subst_ctx ((var 0) :: ctx) s)
  end.

(* step index monotonicity
Lemma eva_cbv_mono k ctx u u' : eva_cbv k ctx u = Some u' ->
  eva_cbv (S k) ctx u = Some u'.
Proof.
  elim: k ctx u u'; first done.
  move=> k IH ctx u u'. rewrite [eva_cbv (S k) _ _]/=.
  case: u.
  - 
 *)

Lemma asd k t ctx u u' : eva_cbv k (t::ctx) u = Some u' ->
  eva_cbv k ctx (subst u 0 t) = Some u'.
Proof.
  elim: k t ctx u; first done.
  move=> k IH t ctx [].
  - move=> [|n] /=.
    + move=> <-.  apply. done. by exists k.
    + case En: (skipn n ctx) => [|t' ctx'].
      * by exists 0.
      * admit. (*?*)
  - move=> s' t' /=.

      admit. (* actually wrong because of shift *)
      * by exists 0.
  - 
    rewrite -/(eva_cbv (S k)). case: t => /=.


Lemma main1 k ctx u' v : 
  closed u -> 
  Seval.eva k u = Some u' ->
  exists m v', eva_cbv m ctx v = Some v' /\ subst_ctx ctx v' = u'.
Proof.
  elim: k ctx u' v.
  { move=> ctx u' [] /=.
    - move=> n. case En: (nth_error ctx n) => [t|]; last done.
      case: t En; [done|done|].
      move=> s En [<-].
      exists 2, (lam s). rewrite /= En.
      admit. (* needs closedness *)
    - done.
    - move=> s [] <-. by exists 1, (lam s). }
  move=> k IH ctx u' [] /=.
  - move=> n. case En: (nth_error ctx n) => [t|]; last done.
    case: t En; [done| |].
    + move=> s t En.
      case Es: (Seval.eva k s) => [s'|]; last done.
      case: s' Es; [done|done|].
      move=> s' Hs.
      case Et: (Seval.eva k t) => [t'|]; last done.
      move=> Ht.

Lemma main1 k ctx u' v : Seval.eva k (subst_ctx ctx v) = Some u' ->
  exists m v', eva_cbv m ctx v = Some v' /\ subst_ctx ctx v' = u'.
Proof.
  elim: k ctx u' v.
  { move=> ctx u' [] /=.
    - move=> n. case En: (nth_error ctx n) => [t|]; last done.
      case: t En; [done|done|].
      move=> s En [<-].
      exists 2, (lam s). rewrite /= En.
      admit. (* needs closedness *)
    - done.
    - move=> s [] <-. by exists 1, (lam s). }
  move=> k IH ctx u' [] /=.
  - move=> n. case En: (nth_error ctx n) => [t|]; last done.
    case: t En; [done| |].
    + move=> s t En.
      case Es: (Seval.eva k s) => [s'|]; last done.
      case: s' Es; [done|done|].
      move=> s' Hs.
      case Et: (Seval.eva k t) => [t'|]; last done.
      move=> Ht.


      /IH.
    
    done.
    move=> > /=. }


(*
  k   : step index
  ts  : hanging arguments (evaluationg u v1 .. vn)
  ctx : context for deBruijn terms
  vs  : list of terms that need to evalue (necessary for call-by-value) 
  u term to reduce
  tail-recursive
  currently left-most outer-most call by value
*)
Fixpoint eva (k : nat) (ts : list term) (ctx : list term) (vs : list term) (u : term) : option term :=
  match k with
  | 0 => None
  | S k =>
    match u with
    | var n => (* look up term in ctx *)
        match nth_error ctx n with
        | None => None
        | Some t => eva k ts ctx vs t
        end
    | lam s => (* terminate or push onto context *)
        match ts with
        | [] => 
            match vs with
            | [] => Some u
            | v::vs => 
            end
        | t::ts => eva k ts (t::ctx) (t::vs) s
        end
    | app s t => (* push argument *)
        eva k (t :: ts) ctx s
    end
  end.

(*
(*
  k : step index
  ts : hanging arguments (evaluationg u v1 .. vn)
  ctx : context for deBruijn terms
  u term to reduce
  tail-recursive
  currently left-most outer-most call by name
*)
Fixpoint eva (k : nat) (ts : list term) (ctx : list term) (u : term) : option term :=
  match k with
  | 0 => None
  | S k =>
    match u with
    | var n => (* look up term in ctx *)
        match nth_error ctx n with
        | None => None
        | Some t => eva k ts ctx t
        end
    | lam s => (* terminate or push onto context *)
        match ts with
        | [] => Some u
        | t::ts => eva k ts (t::ctx) s
        end
    | app s t => (* push argument *)
        eva k (t :: ts) ctx s
    end
  end.
*)

(*
Fixpoint eva (k : nat) (ts : list term) (u : term) : option term :=
  match k with
  | 0 => None
  | S k =>
    match u with
    | var n => obind (eva k ts) (nth_error ts n)
    | lam s => Some (lam s)
    | app s t =>
        match eva k ts s with
        | Some (lam s) => eva k (t::ts) s
        | _ => None
        end
    end
  end.
*)
