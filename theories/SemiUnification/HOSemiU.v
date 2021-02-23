(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Problem(s):
    Higher-order Semi-unification (HOSemiU)
*)

Require Import List Relation_Operators.

Require Import Undecidability.SemiUnification.pts.

(* 
  terms (according to pure type systems) 
  P Q R ::= x | c | P Q | lambda (x : P). Q | Pi (x : P). Q 
  where x ranges over term variables and c ranges over term constants
*)

(* single step beta reduction relation *)
Inductive step : term -> term -> Prop :=
  | step_beta P Q R: step (app (lam P Q) R) (subst_term (scons R var) Q) 
  | step_appL P P' Q: step P P' -> step (app P Q) (app P' Q)
  | step_appR P Q Q': step Q Q' -> step (app P Q) (app P Q')
  | step_lamL P P' Q: step P P' -> step (lam P Q) (lam P' Q)
  | step_lamR P Q Q': step Q Q' -> step (lam P Q) (lam P Q')
  | step_PiL P P' Q: step P P' -> step (Pi P Q) (Pi P' Q)
  | step_PiR P Q Q': step Q Q' -> step (Pi P Q) (Pi P Q').

(* a term is normal (in normal form) if it is not reducible *)
Definition normal (P : term) : Prop :=
  forall Q, not (step P Q).

(* beta-equality is the reflexive, symmetric, transitive closure 
  of the single step beta reduction *)
Definition eq_beta := clos_refl_sym_trans term step.

Local Notation "P =β Q" := (eq_beta P Q) (at level 50).

(* a valuation assigns terms with property p to term variables *)
Definition valuation (p : term -> Prop) : Type := nat -> { P : term | p P }.

(* substitution function "subst_term" is defined in pts.v *)

(* replace free variables by assigned terms with property p *)
(* for example, p can be "normal_form" or "simple" *)
Definition substitute {p : term -> Prop} (φ : valuation p) (P : term) : term :=
  subst_term (fun x => proj1_sig (φ x)) P.

(* Higher-order Semi-unification Definition *)

(* inequality: s ≤ t *)
Definition inequality : Type := (term * term).

(* φ solves s ≤ t, if there is ψ such that ψ (φ (s)) =β φ (s) *)
(* property p in the range of φ is the same as in the range of ψ *)
Definition solution {p : term -> Prop} (φ : valuation p) : inequality -> Prop := 
  fun '(P, Q) => exists (ψ : valuation p), 
    substitute ψ (substitute φ P) =β substitute φ Q.

(* Higher-order Semi-unification *)
(* is there a normal valuation φ that solves all inequalities? *)
Definition HOSemiU (cs: list inequality) := 
  exists (φ: valuation normal), forall (c: inequality), In c cs -> solution φ c.

(* FACTS *)
Require Import PeanoNat Lia.
Require Import ssreflect ssrbool ssrfun.

(* TODO part of autosubst? *)
Lemma upRen_term_term_id x : upRen_term_term id x = x.
Proof. by case: x. Qed.

(* TODO autosubst? *)
Lemma shift_up_term_term sigma x : (shift >> up_term_term sigma) x = (sigma >> ren_term shift) x.
Proof. by case: x. Qed.

(*TODO part of autosubst? no funext *)
Lemma ren_term_id {P} : ren_term id P = P.
Proof.
  elim: P.
  - done.
  - done.
  - by move=> /= ? -> ? ->.
  - move=> /= ? -> ?.
    under [ren_term (upRen_term_term id) _]extRen_term => ? do 
      rewrite upRen_term_term_id.
    by move=> ->.
  - move=> /= ? -> ?.
    under [ren_term (upRen_term_term id) _]extRen_term => ? do 
      rewrite upRen_term_term_id.
    by move=> ->.
Qed.

(* TODO rinstId_term uses funext, which is bad *)
(* alternative: ren_term_id *)
Definition term_norm := (compRen_term, renRen_term, @ren_term_id, renComp_term).

(* such that simpl evaluates funcomp f g x *)
Arguments funcomp {X Y Z} _ _ _ /.
(* such that simpl evaluates id x*)
Arguments unscoped.id _ _/.

(* evaluates propositional predicate p on all free variables *)
Fixpoint allfv_term (p: nat -> Prop) (P: term) :=
  match P with
  | var x => p x
  | const _ => True 
  | app P Q => allfv_term p P /\ allfv_term p Q
  | lam P Q => allfv_term p P /\ allfv_term (scons True p) Q
  | Pi P Q => allfv_term p P /\ allfv_term (scons True p) Q
  end.

(* notion of a simple type represented by a term
  s, t ::= x | Pi x : s. t (where x is not free in t)
*)
Fixpoint simple (P: term) :=
  match P with
  | var _ => True
  | const _ => False 
  | app P Q => False
  | lam P Q => False
  | Pi P Q => (* Pi (x : P). Q is simple iff *)
      simple P /\ (* P is simple *)
      simple Q /\ (* Q is simple *)
      allfv_term (fun y => 0 <> y) Q (* x does not occur free in Q *) 
  end.

(* BEGIN term enumerability *)

(* bijection from nat * nat to nat *)
Definition encode_nat '(x, y) : nat := 
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(* bijection from nat to nat * nat *)
Definition decode_nat (n : nat) : nat * nat := 
  nat_rec _ (0, 0) (fun _ '(x, y) => if x is S x then (x, S y) else (S y, 0)) n.

Lemma encode_nat_non_decreasing (x y: nat) : x + y <= encode_nat (x, y).
Proof. elim: x=> [| x IH] /=; [| rewrite Nat.add_succ_r /=]; by lia. Qed.

Lemma encode_decode_nat {xy: nat * nat} : decode_nat (encode_nat xy) = xy.
Proof.
  move Hn: (encode_nat xy) => n. elim: n xy Hn.
  { by move=> [[|?] [|?]]. }
  move=> n IH [x [|y [H]]] /=.
  { move: x => [|x [H]] /=; first done.
    by rewrite (IH (0, x)) /= -?H ?PeanoNat.Nat.add_0_r. }
  by rewrite (IH (S x, y)) /= -?H ?PeanoNat.Nat.add_succ_r.
Qed.

Opaque encode_nat decode_nat.

(* injectively encode a term as a natural number *)
Fixpoint encode_term (P: term) : nat :=
  match P with
  | var x => encode_nat (0, x)
  | const c => encode_nat (1, c) 
  | app P Q => encode_nat (2, (encode_nat (encode_term P, encode_term Q))) 
  | lam P Q => encode_nat (3, (encode_nat (encode_term P, encode_term Q))) 
  | Pi P Q => encode_nat (4, (encode_nat (encode_term P, encode_term Q))) 
  end.

Fixpoint decode_term' (k n: nat) : term :=
  match k with
  | 0 => var 0
  | S k =>
    match decode_nat n with
    | (0, x) => var x
    | (1, c) => const c
    | (2, m) => let (m1, m2) := decode_nat m in
      app (decode_term' k m1) (decode_term' k m2)
    | (3, m) => let (m1, m2) := decode_nat m in
      lam (decode_term' k m1) (decode_term' k m2)
    | (4, m) => let (m1, m2) := decode_nat m in
      Pi (decode_term' k m1) (decode_term' k m2)
    | _ => var 0
    end
  end.

(* uniquely decode a term from a natural number *)
Definition decode_term (n: nat) := decode_term' (S n) n.

Lemma encode_decode_term (P: term) : decode_term (encode_term P) = P.
Proof.
  rewrite /decode_term. 
  suff : (forall k, encode_term P < k -> decode_term' k (encode_term P) = P) by apply.
  move=> k. elim: k P; first by lia.
  move=> k IH [] => /=.
  - move=> ?. by rewrite encode_decode_nat.
  - move=> ?. by rewrite encode_decode_nat.
  - move=> P Q ?.
    have ? := encode_nat_non_decreasing 2 (encode_nat (encode_term P, encode_term Q)).
    have ? := encode_nat_non_decreasing (encode_term P) (encode_term Q).
    rewrite ?encode_decode_nat. congr app; apply: IH; by lia.
  - move=> P Q ?.
    have ? := encode_nat_non_decreasing 3 (encode_nat (encode_term P, encode_term Q)).
    have ? := encode_nat_non_decreasing (encode_term P) (encode_term Q).
    rewrite ?encode_decode_nat. congr lam; apply: IH; by lia.
  - move=> P Q ?.
    have ? := encode_nat_non_decreasing 4 (encode_nat (encode_term P, encode_term Q)).
    have ? := encode_nat_non_decreasing (encode_term P) (encode_term Q).
    rewrite ?encode_decode_nat. congr Pi; apply: IH; by lia.
Qed.

Opaque encode_term decode_term.

(* END term enumerability *)

(* decidable equality on term *)
Lemma term_eq_dec (P Q: term) : {P = Q} + {P <> Q}.
Proof. by do 2 (decide equality). Qed. 

(* decidable allfv_term on decidable predicates *)
(* TODO move to autosubst? *)
Lemma allfv_term_dec p P : (forall x, {p x} + {not (p x)}) ->
  {allfv_term p P} + {not (allfv_term p P)}.
Proof.
  elim: P p.
  - move=> >. by apply.
  - move=> *. by left.
  - move=> P IHP Q IHQ p Hp /=.
    move: (IHP _ Hp) (IHQ _ Hp); clear; by firstorder done.
  - move=> P IHP Q IHQ p Hp /=.
    have H'p: forall x : nat, {(scons True p) x} + {not ((scons True p) x)} by (case; [left |]).
    move: (IHP _ Hp) (IHQ _ H'p); clear; by firstorder done.
  - move=> P IHP Q IHQ p Hp /=.
    have H'p: forall x : nat, {(scons True p) x} + {not ((scons True p) x)} by (case; [left |]).
    move: (IHP _ Hp) (IHQ _ H'p); clear; by firstorder done.
Qed.

Definition non_zero x := if x is 0 then False else True.

Definition non_zero_dec x : {non_zero x} + {not (non_zero x)} :=
  if x is 0 then right id else left I.

(* decides whether 0 does not occur free in P *)
Definition fresh_0 (P: term) := allfv_term_dec non_zero P non_zero_dec.

(* make a term simple, remember non-simpel subterms as variables *)
Fixpoint prune (xi: nat -> nat) (P: term) : term :=
  match P with
  | Pi P' Q' => 
      if fresh_0 Q' 
        then Pi (prune xi P') (ren_term shift (prune (scons 0 xi) Q'))
        else var (encode_term (ren_term xi P))
  | _ => var (encode_term (ren_term xi P))
  end.

(* remember non-simple subterms as distrinct variables 
wrong because de Bruijn in prune Q' shifts variable names and rename before prune is not structural
Fixpoint prune (P: term) :=
  match P with
  | Pi P' Q' => 
    if fresh_inb 0 Q' 
      then Pi (prune P') (ren_term S (prune Q')) 
      else var (encode_term P)
  | _ => var (encode_term P)
  end.
*)


(* TODO could be generated by autosubst *)
(* allfv on trivial predicate *)
Lemma allfv_term_triv {p: nat -> Prop} {P}: 
  (forall x, p x) -> allfv_term p P.
Proof.
  elim: P p.
  - move=> >. by apply.
  - done.
  - move=> P IHP Q IHQ p ? /=. 
    constructor; [by apply: IHP | by apply: IHQ].
  - move=> P IHP Q IHQ p ? /=. constructor; [by apply: IHP |].
    apply: IHQ. by case.
  - move=> P IHP Q IHQ p ? /=. constructor; [by apply: IHP |].
    apply: IHQ. by case.
Qed.

(* TODO could be generated by autosubst *)
(* allfv monotonicity *)
Lemma allfv_term_impl {p1 p2: nat -> Prop} {P}: 
  (forall x, p1 x -> p2 x) -> allfv_term p1 P -> allfv_term p2 P.
Proof.
  elim: P p1 p2.
  - move=> >. by apply.
  - done.
  - by move=> P IHP Q IHQ p1 p2 H /= [/(IHP _ _ H) ? /(IHQ _ _ H) ?].
  - move=> P IHP Q IHQ p1 p2 H /= [/IHP {}IHP /IHQ {}IHQ].
    constructor; first by apply: IHP.
    apply: IHQ. by case.
  - move=> P IHP Q IHQ p1 p2 H /= [/IHP {}IHP /IHQ {}IHQ].
    constructor; first by apply: IHP.
    apply: IHQ. by case.
Qed.

(* TODO could be generated by autosubst *)
(* extensionality principle on allfv_term *)
Lemma ext_allfv_term {p1 p2 P}: (forall x, p1 x <-> p2 x) -> allfv_term p1 P <-> allfv_term p2 P.
Proof. move=> H. by constructor; apply: allfv_term_impl; move=> ? /H. Qed.

(* TODO could be generated by autosubst *)
(* allfv ren interaction  *)
Lemma allfv_ren_term {p xi P} : allfv_term p (ren_term xi P) <-> allfv_term (fun x => p (xi x)) P .
Proof.
  elim: P p xi.
  - done.
  - done.
  - move=> P IHP Q IHQ p xi /=. by rewrite IHP IHQ.
  - move=> P IHP Q IHQ p xi /=. rewrite IHP IHQ.
    set H1Q := (allfv_term _ Q). set H2Q := (allfv_term _ Q).
    suff : H1Q <-> H2Q by move=> ->.
    subst H1Q H2Q. apply: ext_allfv_term. by case.
  - move=> P IHP Q IHQ p xi /=. rewrite IHP IHQ.
    set H1Q := (allfv_term _ Q). set H2Q := (allfv_term _ Q).
    suff : H1Q <-> H2Q by move=> ->.
    subst H1Q H2Q. apply: ext_allfv_term. by case.
Qed.

(* TODO could be generated by autosubst *)
(* allfv subst interaction  *)
Lemma allfv_subst_term {p sigma P} : 
  allfv_term p (subst_term sigma P) <-> (allfv_term (funcomp (allfv_term p) sigma) P).
Proof.
  elim: P p sigma.
  - done.
  - done.
  - move=> P IHP Q IHQ p sigma /=. by rewrite IHP IHQ.
  - move=> P IHP Q IHQ p sigma /=. rewrite IHP IHQ.
    set H1Q := (allfv_term _ Q). set H2Q := (allfv_term _ Q).
    suff : H1Q <-> H2Q by move=> ->.
    subst H1Q H2Q. apply: ext_allfv_term.
    case; first done.
    move=> ? /=. by rewrite allfv_ren_term.
  - move=> P IHP Q IHQ p sigma /=. rewrite IHP IHQ.
    set H1Q := (allfv_term _ Q). set H2Q := (allfv_term _ Q).
    suff : H1Q <-> H2Q by move=> ->.
    subst H1Q H2Q. apply: ext_allfv_term.
    case; first done.
    move=> ? /=. by rewrite allfv_ren_term.
Qed.

(* TODO could be generated by autosubst *)
(* extensionality of ren_term wrt. allfv *)
Lemma ext_allfv_ren_term {xi zeta P} : allfv_term (fun x => xi x = zeta x) P -> 
  ren_term xi P = ren_term zeta P.
Proof.
  elim: P xi zeta.
  - by move=> > /= ->.
  - done.
  - by move=> P IHP Q IHQ ? ? /= [/IHP -> /IHQ ->].
  - move=> P IHP Q IHQ ? ? /= [/IHP -> HQ]. congr lam.
    apply: IHQ. apply: allfv_term_impl HQ. 
    case; [done | by move=> ? /= ->].
  - move=> P IHP Q IHQ ? ? /= [/IHP -> HQ]. congr Pi.
    apply: IHQ. apply: allfv_term_impl HQ. 
    case; [done | by move=> ? /= ->].
Qed.

(* TODO could be generated by autosubst *)
(* extensionality of subst_term wrt. allfv *)
Lemma ext_allfv_subst_term {sigma tau P} : allfv_term (fun x => sigma x = tau x) P -> 
  subst_term sigma P = subst_term tau P.
Proof.
  elim: P sigma tau.
  - done.
  - done.
  - by move=> P IHP Q IHQ ? ? /= [/IHP -> /IHQ ->].
  - move=> P IHP Q IHQ ? ? /= [/IHP -> HQ]. congr lam.
    apply: IHQ. apply: allfv_term_impl HQ. 
    case; [done | by move=> ? /= ->].
  - move=> P IHP Q IHQ ? ? /= [/IHP -> HQ]. congr Pi.
    apply: IHQ. apply: allfv_term_impl HQ. 
    case; [done | by move=> ? /= ->].
Qed.

(* renamings transport simple *)
Lemma simple_ren_term {xi P} : simple P -> simple (ren_term xi P).
Proof.
  elim: P xi => //=.
  move=> P IHP Q IHQ xi [HP] [H1Q H2Q].
  constructor; first by apply: IHP.
  constructor; first by apply: IHQ.
  apply /allfv_ren_term. apply: allfv_term_impl H2Q.
  by case.
Qed.

(* prune establishes simple *)
Lemma simple_prune xi P : simple (prune xi P).
Proof.
  elim: P xi => //=.
  move=> P IHP Q IHQ xi.
  case: (fresh_0 Q) => ?; last done.
  constructor; [done | constructor].
  - by apply: simple_ren_term.
  - apply /allfv_ren_term. 
    by apply: allfv_term_triv.
Qed.

(* extensionality principle for prune wrt. allfv_term *)
Lemma ext_allfv_prune_term {zeta xi P} : 
  allfv_term (fun x => xi x = zeta x) P -> prune xi P = prune zeta P.
Proof.
  elim: P xi zeta.
  - by move=> /= > ->.
  - done.
  - move=> P IHP Q IHQ > /= [HP HQ].
    congr (var (encode_term (app _ _))); by apply: ext_allfv_ren_term.
  - move=> P IHP Q IHQ > /= [HP HQ].
    congr (var (encode_term (lam _ _))); first by apply: ext_allfv_ren_term.
    apply: ext_allfv_ren_term. apply: allfv_term_impl HQ.
    case; [done | by move=> ? /= ->].
  - move=> P IHP Q IHQ > /= [HP HQ].
    case: (fresh_0 Q) => ? /=.
    + congr Pi; first by apply: IHP.
      congr ren_term. apply: IHQ.
      apply: allfv_term_impl HQ. by case.
    + congr (var (encode_term (Pi _ _))); first by apply: ext_allfv_ren_term.
      apply: ext_allfv_ren_term. apply: allfv_term_impl HQ.
      case; [done | by move=> ? /= ->].
Qed.


Lemma normalE {P} : normal P ->
  match P with
  | var _ => True
  | const _ => True 
  | app (lam _ _) _ => False
  | app P Q => normal P /\ normal Q
  | lam P Q => normal P /\ normal Q
  | Pi P Q => normal P /\ normal Q
  end.
Proof.
Admitted.

Lemma prune_ren_term {xi zeta P} : prune xi (ren_term zeta P) = prune (funcomp xi zeta) P.
Proof.
  elim: P xi zeta.
  - done.
  - done.
  - move=> * /=. by rewrite ?term_norm.
  - move=> P IHP Q IHQ ? ? /=. congr (var (encode_term (lam _ _))).
    + by rewrite ?term_norm.
    + rewrite term_norm. apply: extRen_term. by case.
  - move=> P IHP Q IHQ ? ? /=.
    case: (fresh_0 Q) => H1Q; case: (fresh_0 _) => H'1Q.
    + congr Pi; first done.
      congr ren_term. rewrite IHQ. apply: ext_allfv_prune_term.
      apply: allfv_term_triv. by case.
    + exfalso. apply: H'1Q.
      apply /allfv_ren_term. apply: allfv_term_impl H1Q. by case.
    + exfalso. apply: H1Q.
      move: H'1Q => /allfv_ren_term.
      apply: allfv_term_impl. by case.
    + congr (var (encode_term (Pi _ _))); first by rewrite ?term_norm.
      rewrite term_norm. apply: extRen_term. by case.
Qed.


(* pruning an instance of a simple type can be internalized *)
(* "KEY LEMMA 1" *)
Lemma prune_subst_term {xi sigma P} : simple P -> prune xi (subst_term sigma P) = subst_term (funcomp (prune xi) sigma) P.
Proof.
  elim: P xi sigma => //=.
  move=> P IHP Q IHQ xi sigma.
  move=> [HP] [H1Q H2Q]. case: (fresh_0 _) => H3Q.
  - congr Pi; first by apply: IHP.
    rewrite (IHQ _ _ H1Q) term_norm.
    (* ext_term not applicable because substitutions are different on 0, which is absent *)
    apply: ext_allfv_subst_term.
    apply: allfv_term_impl H2Q.
    case; first done.
    move=> x _ /=. congr ren_term. by rewrite prune_ren_term.
  - exfalso. apply: H3Q.
    rewrite allfv_subst_term. apply: allfv_term_impl H2Q.
    move=> [|? _] /=; first done.
    apply /allfv_ren_term. by apply: allfv_term_triv.
Qed.


(* TODO autosubst? *)
Lemma ext_ren_term' {xi zeta P Q} : 
  (forall x, xi x = zeta x) -> P = Q -> ren_term xi P = ren_term zeta Q.
Proof. by move=> /extRen_term + ->. Qed.


(* TODO autosubst? sometimes more easy to use *)
Lemma up_ren_subst_term_term' xi sigma x:
  (upRen_term_term xi >> up_term_term sigma) x = up_term_term (xi >> sigma) x.
Proof. by apply: up_ren_subst_term_term. Qed.

Lemma up_term_term_funcomp {xi sigma x} : 
  up_term_term (xi >> sigma) x = (upRen_term_term xi >> up_term_term sigma) x.
Proof.
  by case: x.
Qed.

Fixpoint simple_map_term (f: term -> term) (P: term) : term :=
  match P with
  | Pi P' Q' => 
      if fresh_0 Q' 
        then Pi (simple_map_term f P') 
          (ren_term shift (simple_map_term ((ren_term (scons 0 id)) >> f) Q'))
        else f P
  | _ => f P
  end.

Lemma ext_simple_map_term {f g P} : (forall P', f P' = g P') -> 
  simple_map_term f P = simple_map_term g P.
Proof.
  elim: P f g.
  - move=> >. by apply.
  - move=> >. by apply.
  - move=> P IHP Q IHQ f g. by apply.
  - move=> P IHP Q IHQ f g. by apply.
  - move=> P IHP Q IHQ f g Hfg /=.
    case: (fresh_0 Q) => HQ /=; last done.
    congr Pi; first by apply IHP.
    congr ren_term. apply: IHQ. by move=> P' /=.
Qed.

Lemma ren_simple_map_term {xi f P} : 
  ren_term xi (simple_map_term f P) = simple_map_term (f >> ren_term xi) P.
Proof.
  elim: P xi f => //.
  move=> P IHP Q IHQ xi f /=.
  case: (fresh_0 Q) => HQ /=; last done.
  congr Pi; first done.
  rewrite term_norm ?IHQ. apply: ext_simple_map_term => ?.
  rewrite /= term_norm. apply: extRen_term.
  by case.
Qed.

(* TODO part of autosubst standard file *)
Lemma funcomp_assoc {X1 X2 X3 X4} {f : X1 -> X2} {g : X2 -> X3} {h : X3 -> X4} : 
  funcomp h (funcomp g f) = funcomp (funcomp h g) f.
Proof. reflexivity. Qed.

Lemma simple_map_ren_term {f xi P} : 
  simple_map_term f (ren_term xi P) = simple_map_term (ren_term xi >> f) P.
Proof.
  elim: P f xi => //.
  move=> P IHP Q IHQ f xi /=.
  case: (fresh_0 Q) => HQ /=.
  - case: (fresh_0 _) => H'Q /=; first last.
    { exfalso. apply: H'Q. rewrite allfv_ren_term.
      apply: allfv_term_impl HQ. by case. }
    congr Pi; first by apply: IHP.
    congr ren_term. rewrite IHQ.
    have /ext_simple_map_term -> : forall P', 
      (ren_term (upRen_term_term xi) >> (ren_term (scons 0 id) >> f)) P' = 
      (ren_term (upRen_term_term xi >> (scons 0 id)) >> f) P'.
    { move=> ? /=. by rewrite term_norm. }
    have /ext_simple_map_term -> : forall P',
      (ren_term (0 .: id) >> (ren_term xi >> f)) P' =
      (ren_term ((0 .: id) >> xi) >> f) P'.
    { move=> ? /=. by rewrite term_norm. }
    rewrite -?IHQ. congr simple_map_term.
    apply: ext_allfv_ren_term. apply: allfv_term_impl HQ. by case.
  - case: (fresh_0 _) => H'Q /=; last done.
    exfalso. apply: HQ. move: H'Q. rewrite allfv_ren_term.
    apply: allfv_term_impl. by case.
Qed.

(* pruning intanciated pruned instance (?) *)
(* "KEY LEMMA 2", tau is the resulting simple substitution *)
(* NOTE: fN is the relevant normalizer, xi3 = xi1 = id *)
(* ALTERNATIVE FORMULATION WITH "simple_map" *)
Lemma key2' {fN : term -> term} {sigma xi1 xi3 P} : 
  (* resulting simple valuation *)
  let tau := (fun x => ren_term xi3 (prune id (simple_map_term fN (subst_term sigma (decode_term x))))) in
  (* homomorphism *)
  subst_term tau (prune xi1 P) = ren_term xi3 (prune id (simple_map_term fN (subst_term (funcomp sigma xi1) P))).
Proof.
  move=> tau. subst tau.
  elim: P xi1 xi3 sigma.
  - move=> > /=. by rewrite encode_decode_term.
  - move=> > /=. by rewrite encode_decode_term.
  - move=> * /=. by rewrite encode_decode_term /= ?term_norm.
  - move=> P IHP Q IHQ xi1 xi3 sigma /=. rewrite encode_decode_term /= ?term_norm /=.
    congr (ren_term xi3 (prune id (simple_map_term fN (lam _ _)))). apply: ext_term. by case.
    (* case Pi P Q *)
  - move=> P IHP Q IHQ xi1 xi3 sigma /=.
    case: (fresh_0 Q) => HQ /=.
    (* case (var 0) does not occur in Q *)
    + case: (fresh_0 _) => H'Q /=; first last.
      { exfalso. apply: H'Q. rewrite allfv_subst_term.
        apply: allfv_term_impl HQ. 
        move=> [|x _ /=]; first done.
        rewrite allfv_ren_term. apply: allfv_term_triv. by case. }
      case: (fresh_0 _) => H''Q /=; first last.
      { exfalso. apply: H''Q. rewrite allfv_ren_term.
        apply: allfv_term_triv. by case. }
      congr Pi; first done.
      rewrite ?term_norm. rewrite prune_ren_term.
      have -> : (↑ >> (scons 0 id)) = id by done.
      under [subst_term _ (prune _ Q)]ext_term => ? do 
        rewrite shift_up_term_term /funcomp term_norm.
      rewrite IHQ. apply: ext_ren_term'; first by case.
      rewrite -simple_map_ren_term term_norm. congr (prune id (simple_map_term fN _)). 
      apply: ext_allfv_subst_term.
      apply: allfv_term_impl HQ => - [|? _ /=]; first done.
      by rewrite ?term_norm.
    (* case (var 0) occurs in Q *)
    + rewrite /= encode_decode_term /= ?term_norm.
      under [subst_term (up_term_term _) _]ext_term => ?
        do rewrite -up_ren_subst_term_term'.
      done.
Qed.

(* pruning intanciated pruned instance (?) *)
(* "KEY LEMMA 2", tau is the resulting simple substitution *)
(* NOTE: fN is the relevant normalizer *)
(* ALTERNATIVE FORMULATION WITH "simple_map" *)
Corollary key2'_final {fN : term -> term} {sigma P} : 
  (* resulting simple valuation *)
  let tau := (fun x => prune id (simple_map_term fN (subst_term sigma (decode_term x)))) in
  (* homomorphism *)
  subst_term tau (prune id P) = prune id (simple_map_term fN (subst_term sigma P)).
Proof. 
  have := @key2' fN sigma id id P.
  rewrite /= ?term_norm.
  move=> <-. apply: ext_term => ?. by rewrite ?term_norm.
Qed.

Definition red_beta := clos_refl_trans term step.



(* TODO part of autosubst? *)
(* all free variables are left unchanged by a renaming *)
Lemma ren_term_allfv_id {xi P} : allfv_term (fun x => xi x = x) P -> ren_term xi P = P.
Proof.
  move=> H. rewrite -[RHS]ren_term_id.
  by apply: ext_allfv_ren_term.
Qed.
 
Lemma simple_map_term_id {P} : 
  simple_map_term id P = P.
Proof.
  elim: P => //.
  move=> P IHP Q IHQ /=. case: (fresh_0 Q) => HQ /=; last done.
  congr Pi; first done.
  rewrite ren_simple_map_term.
  rewrite -simple_map_ren_term.
  have ->: ren_term shift = (ren_term shift) >> id by done.
  rewrite -simple_map_ren_term term_norm.
  rewrite ren_term_allfv_id; last done.
  apply: allfv_term_impl HQ. by case.
Qed.

Lemma simple_map_simple_map_term {f g P} :
  simple_map_term g (simple_map_term f P) = simple_map_term (f >> simple_map_term g) P.
Proof.
  elim: P f g => //.
  move=> P IHP Q IHQ f g /=.
  case: (fresh_0 Q) => HQ /=; last done.
  case: (fresh_0 _) => H'Q /=; first last.
  { exfalso. apply: H'Q. rewrite allfv_ren_term.
    apply: allfv_term_triv. by case. }
  congr Pi; first done.
  congr ren_term. rewrite simple_map_ren_term IHQ.
  apply: ext_simple_map_term => ? /=.
  apply: ext_simple_map_term => ? /=.
  by rewrite ?term_norm.
Qed.

Lemma red_beta_diamond {P Q1 Q2} : red_beta P Q1 -> red_beta P Q2 -> 
  { Q | red_beta Q1 Q /\ red_beta Q2 Q }.
Proof.
Admitted.

Definition rt_rt1n := Relations.Operators_Properties.clos_rt_rt1n_iff.
Arguments rt_step {A R x y}.

(* TODO move to red_beta facts *)
Lemma red_beta_appI P P' Q Q' : red_beta P P' -> red_beta Q Q' -> red_beta (app P Q) (app P' Q').
Proof.
  move=> /rt_rt1n H. elim: H Q Q'.
  - move=> >. elim => *.
    + apply: rt_step. by apply: step_appR.
    + by apply: rt_refl.
    + apply: rt_trans; by eassumption.
  - move=> > ? ? IH > /IH ?.
    apply: rt_trans; last by eassumption.
    apply: rt_step. by apply: step_appL.
Qed.

(* TODO move to red_beta facts *)
Lemma red_beta_lamI P P' Q Q' : red_beta P P' -> red_beta Q Q' -> red_beta (lam P Q) (lam P' Q').
Proof.
  move=> /rt_rt1n H. elim: H Q Q'.
  - move=> >. elim => *.
    + apply: rt_step. by apply: step_lamR.
    + by apply: rt_refl.
    + apply: rt_trans; by eassumption.
  - move=> > ? ? IH > /IH ?.
    apply: rt_trans; last by eassumption.
    apply: rt_step. by apply: step_lamL.
Qed.


(* TODO move to red_beta facts *)
Lemma red_beta_PiI P P' Q Q' : red_beta P P' -> red_beta Q Q' -> red_beta (Pi P Q) (Pi P' Q').
Proof.
  move=> /rt_rt1n H. elim: H Q Q'.
  - move=> >. elim => *.
    + apply: rt_step. by apply: step_PiR.
    + by apply: rt_refl.
    + apply: rt_trans; by eassumption.
  - move=> > ? ? IH > /IH ?.
    apply: rt_trans; last by eassumption.
    apply: rt_step. by apply: step_PiL.
Qed.

(* TODO move to beta facts *)
Lemma step_betaI {P Q R R'} : R' = (subst_term (scons R var) Q) -> step (app (lam P Q) R) R'.
Proof. move=> ->. by apply: step_beta. Qed.

(* TODO move to beta facts *)
Lemma step_ren_termI xi {P Q} : step P Q -> step (ren_term xi P) (ren_term xi Q).
Proof.
  move=> H. elim: H xi; [|by eauto using step with nocore ..].
  move=> > /=. apply: step_betaI. rewrite ?term_norm.
  apply: ext_term. by case.
Qed.

(* TODO move to beta facts *)
Lemma red_beta_ren_termI xi {P Q} : red_beta P Q -> red_beta (ren_term xi P) (ren_term xi Q).
Proof.
  elim.
  - move=> *. by apply /rt_step /step_ren_termI.
  - move=> *. by apply: rt_refl.
  - move=> *. apply: rt_trans; by eassumption.
Qed.

Lemma simple_map_term_red_beta_impl {f g P} : (forall P', red_beta (f P') (g P')) ->
  red_beta (simple_map_term f P) (simple_map_term g P).
Proof.
  elim: P f g.
  - move=> >. by apply.
  - move=> >. by apply.
  - move=> P IHP Q IHQ ? ?. by apply.
  - move=> P IHP Q IHQ ? ?. by apply.
  - move=> P IHP Q IHQ ? ? H /=.
    case: (fresh_0 Q) => HQ /=; last by apply: H.
    apply: red_beta_PiI; first by apply: IHP.
    apply: red_beta_ren_termI. apply: IHQ.
    move=> ?. by apply: H.
Qed.

Lemma step_allfv_term_impl {p P Q} : step P Q -> allfv_term p P -> allfv_term p Q.
Proof.
  move=> H. elim: H p; [| by firstorder done ..].
  move=> > /= [[_ +] ?]. rewrite allfv_subst_term.
  apply: allfv_term_impl. by case.
Qed.

Lemma red_beta_allfv_term_impl {p P Q} : red_beta P Q -> allfv_term p P -> allfv_term p Q.
Proof.
  elim.
  - move=> >. by apply: step_allfv_term_impl.
  - done.
  - by move=> > _ IH1 _ IH2 /IH1.
Qed.

(*
(* alternative formulation of red_beta *)
Inductive red_beta' : term -> term -> Prop :=
  | red_beta_refl P : red_beta' P P
  | red_beta_contract P P1 P2 Q Q': 
      red_beta' P (app (lam P1 P2) Q) -> red_beta' (subst_term (scons P2 var) Q) Q' -> red_beta' (app P Q) Q'
  | red_beta_app P P' Q Q': red_beta' P P' -> red_beta' Q Q' -> red_beta' (app P Q) (app P' Q')
  | red_beta_lam P P' Q Q': red_beta' P P' -> red_beta' Q Q' -> red_beta' (lam P Q) (lam P' Q')
  | red_beta_Pi P P' Q Q': red_beta' P P' -> red_beta' Q Q' -> red_beta' (Pi P Q) (Pi P' Q').
*)

(* TODO move to red_beta facts *)
Lemma red_beta_subst_termI {sigma tau P} : (forall x, red_beta (sigma x) (tau x)) -> 
  red_beta (subst_term sigma P) (subst_term tau P).
Proof.
  elim: P sigma tau.
  - move=> >. by apply.
  - move=> *. by apply: rt_refl.
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: red_beta_appI; [by apply: IHP | by apply: IHQ].
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: red_beta_lamI; first by apply IHP.
    apply: IHQ. case; first by apply: rt_refl.
    move=> x /=. by apply: red_beta_ren_termI.
  - move=> P IHP Q IHQ sigma tau H /=.
    apply: red_beta_PiI; first by apply IHP.
    apply: IHQ. case; first by apply: rt_refl.
    move=> x /=. by apply: red_beta_ren_termI.
Qed.

Lemma red_betaE {P Q} : red_beta P Q ->
  match P with
  | var _ => Q = P
  | const _ => Q = P
  | app P1 P2 => 
      (exists Q1 Q2, Q = app Q1 Q2 /\ red_beta P1 Q1 /\ red_beta P2 Q2) \/
      (exists P11 P12, red_beta P1 (lam P11 P12) /\ red_beta (subst_term (scons P2 var) P12) Q)
  | lam P1 P2 => exists Q1 Q2, Q = lam Q1 Q2 /\ red_beta P1 Q1 /\ red_beta P2 Q2
  | Pi P1 P2 => exists Q1 Q2, Q = Pi Q1 Q2 /\ red_beta P1 Q1 /\ red_beta P2 Q2
  end.
Proof.
  move=> /rt_rt1n. elim.
  - case.
    + done.
    + done.
    + move=> ? ?. left. 
      do 2 eexists. constructor; first by reflexivity.
      constructor; by apply: rt_refl.
    + move=> ? ?. 
      do 2 eexists. constructor; first by reflexivity.
      constructor; by apply: rt_refl.
    + move=> ? ?. 
      do 2 eexists. constructor; first by reflexivity.
      constructor; by apply: rt_refl.
  - move=> > [].
    + move=> > ? _. right. 
      do 2 eexists. constructor; first by apply: rt_refl.
      by apply /rt_rt1n.
    + move=> > ? _ [].
      * move=> [?] [?] [->] [? ?]. left.
        do 2 eexists. constructor; first by reflexivity.
        constructor; last done.
        apply: rt_trans; last by eassumption.
        by apply: rt_step.
      * move=> [?] [?] [?] ?. subst. right.
        do 2 eexists. constructor; last by eassumption.
        by apply: rt_trans; [apply: rt_step | by eassumption].
    + move=> > ? _ [].
      * move=> [?] [?] [->] [? ?]. left.
        do 2 eexists. constructor; first by reflexivity.
        constructor; first done.
        apply: rt_trans; last by eassumption.
        by apply: rt_step.
      * move=> [?] [?] [?] ?. subst. right.
        do 2 eexists. constructor; first by eassumption.
        apply: rt_trans; last by eassumption.
        apply: red_beta_subst_termI. case; first by apply: rt_step.
        move=> *. by apply: rt_refl.
    + move=> > /rt_step ? _ [?] [?] [->] [? ?].
      do 2 eexists. constructor; first by reflexivity.
      by constructor; first by (apply: rt_trans; eassumption).
    + move=> > /rt_step ? _ [?] [?] [->] [? ?].
      do 2 eexists. constructor; first by reflexivity.
      by constructor; last by (apply: rt_trans; eassumption).
    + move=> > /rt_step ? _ [?] [?] [->] [? ?].
      do 2 eexists. constructor; first by reflexivity.
      by constructor; first by (apply: rt_trans; eassumption).
    + move=> > /rt_step ? _ [?] [?] [->] [? ?].
      do 2 eexists. constructor; first by reflexivity.
      by constructor; last by (apply: rt_trans; eassumption).
Qed.


(* pruning intanciated pruned instance (?) *)
(* "KEY LEMMA 3", fN is the relevant normalizer *)
(* to use with "key2'_final" *)
Lemma construct_fN xi {P Q} : red_beta P Q -> 
  exists (fN : term -> term), 
    red_beta (ren_term xi Q) (simple_map_term fN (ren_term xi P)) /\
    (forall R, red_beta R (fN R)).
Proof.
  elim: P xi Q.
  - move=> x xi Q /red_betaE HQ. exists id. rewrite simple_map_term_id HQ.
     constructor => *; by apply: rt_refl.
  - move=> c xi Q /red_betaE HQ. exists id. rewrite simple_map_term_id HQ.
    constructor => *; by apply: rt_refl.
  - move=> P IHP Q IHQ xi R HR.
    exists (fun R' => if term_eq_dec R' (ren_term xi (app P Q)) then (ren_term xi R) else R').
    constructor.
    + move=> /=. case: (term_eq_dec _ _) => /=; last done.
      move=> _. by apply: rt_refl.
    + move=> ?. case: (term_eq_dec _ _).
      * move=> /= ->. rewrite -/(ren_term xi (app _ _)).
        by apply: red_beta_ren_termI.
      * move=> /= _. by apply: rt_refl.
    - move=> P IHP Q IHQ xi R HR.
      exists (fun R' => if term_eq_dec R' (ren_term xi (lam P Q)) then (ren_term xi R) else R').
      constructor.
      + move=> /=. case: (term_eq_dec _ _) => /=; last done.
        move=> _. by apply: rt_refl.
      + move=> ?. case: (term_eq_dec _ _).
        * move=> /= ->. rewrite -/(ren_term xi (lam _ _)).
          by apply: red_beta_ren_termI.
        * move=> /= _. by apply: rt_refl.
  - move=> P IHP Q IHQ xi R HR /=.
    case: (fresh_0 _) => HQ /=.
    + move: HR => /red_betaE - [P'] [Q'] [->] [HPP' HQQ'].
      have [fNP [H1fNP H2fNP]] := IHP xi _ HPP'.
      have [fNQ [H1fNQ H2fNQ]] := IHQ (scons 0 xi) _ HQQ'.
      exists (fun R' => sval (red_beta_diamond (H2fNP R') (H2fNQ R'))).
      constructor.
      * rewrite /=. apply: red_beta_PiI.
        ** apply: rt_trans; first by eassumption.
           apply: simple_map_term_red_beta_impl => R'.
           by move: (sval _) (svalP (red_beta_diamond (H2fNP R') (H2fNQ R'))) => ? [].
        ** have ->: ren_term (upRen_term_term xi) Q' = ren_term shift (ren_term (0 .: xi) Q').
           { rewrite term_norm. apply: ext_allfv_ren_term.
             apply: red_beta_allfv_term_impl; first by eassumption.
             move: HQ. rewrite allfv_ren_term.
             apply: allfv_term_impl. by case. }
            apply: red_beta_ren_termI.

            rewrite -simple_map_ren_term term_norm.
            have HH : forall x, (upRen_term_term xi >> (scons 0 id)) x = (scons 0 xi) x.
            by case.
            under [ren_term _ Q]extRen_term => ? do rewrite HH.

            apply: rt_trans; first by eassumption.
            apply: simple_map_term_red_beta_impl => R'.
            by move: (sval _) (svalP (red_beta_diamond (H2fNP R') (H2fNQ R'))) => ? [].
      * move=> R'.
        move: (sval _) (svalP (red_beta_diamond (H2fNP R') (H2fNQ R'))) => R'' [? _].
        apply: rt_trans; last by eassumption.
        by apply: H2fNP.
    + exists (fun R' => if term_eq_dec R' (ren_term xi (Pi P Q)) then (ren_term xi R) else R').
    constructor.
    * move=> /=. case: (term_eq_dec _ _) => /=; last done.
      move=> _. by apply: rt_refl.
    * move=> ?. case: (term_eq_dec _ _); last by (move=> *; apply: rt_refl).
      move=> /= ->. by apply: (red_beta_ren_termI xi HR).
Qed.

Corollary construct_fN' {P Q} : red_beta P Q -> normal Q ->
  exists (fN : term -> term), simple_map_term fN P = Q.
Proof.
  move=> /(construct_fN id) - [fN] [H1Q _] H2Q.
  exists fN. move: H1Q. rewrite /red_beta ?term_norm /=. 
  move: (simple_map_term _ _) => ? /rt_rt1n. case; first done.
  by move=> > /H2Q.
Qed.

Lemma stepE {P Q} : step P Q -> 
  match P with
  | var _ => False
  | const _ => False
  | app P1 P2 => 
    (exists P11 P12, P1 = lam P11 P12 /\ Q = subst_term (scons P2 var) P12) \/
    (exists Q1, Q = app Q1 P2 /\ step P1 Q1) \/
    (exists Q2, Q = app P1 Q2 /\ step P2 Q2)
  | lam P1 P2 => 
      (exists Q1, Q = lam Q1 P2 /\ step P1 Q1) \/
      (exists Q2, Q = lam P1 Q2 /\ step P2 Q2)
  | Pi P1 P2 => 
      (exists Q1, Q = Pi Q1 P2 /\ step P1 Q1) \/
      (exists Q2, Q = Pi P1 Q2 /\ step P2 Q2)
  end.
Proof. case; by eauto. Qed.

Lemma normal_PiI {P Q} : normal P -> normal Q -> normal (Pi P Q).
Proof. move=> HP HQ R /stepE. by case => - [?] [_] => [/HP | /HQ]. Qed.

Lemma normal_varI {x} : normal (var x).
Proof. by move=> ? /stepE. Qed. 

(* construct a valuation from a substitution sigma which pointwise satisfied predicate p *)
Definition valuationI (p: term -> Prop)
  (sigma: nat -> term) (H: forall x, p (sigma x)) : valuation p :=
  (fun x => exist _ _ (H x)).

Lemma normal_ren_termE xi {P} : normal (ren_term xi P) -> normal P.
Proof. by move=> HP Q /(step_ren_termI xi) /HP. Qed.

Lemma normal_simple_substituteI {φ: valuation normal} {P} : simple P -> normal (substitute φ P).
Proof.
  elim: P φ => //.
  - move=> x φ _. rewrite /substitute /=.
    by apply: svalP.
  - move=> P IHP Q IHQ φ /= [/IHP {}IHP] [/IHQ {}IHQ] HQ.
    rewrite /substitute /=. apply: normal_PiI; first by apply: IHP.
    set sigma := up_term_term (fun x => sval (φ x)).
    apply: (IHQ (valuationI normal sigma _)).
    move=> [|x]; first by apply: normal_varI.
    apply: (normal_ren_termE (scons 0 id)) => /=.
    rewrite ?term_norm. by apply: svalP.
Qed.

Definition rst_rst1n := Operators_Properties.clos_rst_rst1n_iff.

Lemma red_beta_normal {P Q} : red_beta P Q -> normal P -> P = Q.
Proof.
  case /rt_rt1n; first done.
  by move=> > + _ H => /H.
Qed.

Lemma eq_beta_normal {P Q} : normal Q -> P =β Q -> red_beta P Q.
Proof.
  move=> HQ /rst_rst1n HPQ. 
  elim: HPQ HQ; first by (move=> *; apply: rt_refl).
  move=> {}P R {}Q [|].
  - move=> /rt_step ? _ IH ?. 
    apply: rt_trans; [by eassumption | by apply: IH].
  - move=> /rt_step HRP _ IH HQ.
    have [Q' [HPQ' /red_beta_normal HQQ']] := red_beta_diamond HRP (IH HQ).
    by rewrite (HQQ' HQ).
Qed.

(* anny solution φ to a simple instance (P, Q) entails a simple solution sigma' *)
Lemma simple_solutionI {φ ψ: valuation normal} {P Q} : simple P -> simple Q -> 
  substitute ψ (substitute φ P) =β substitute φ Q ->
  let sigma' := (fun x => prune id (sval (φ x))) in
  exists tau', 
    (forall x, simple (tau' x)) /\
    subst_term tau' (subst_term sigma' P) = subst_term sigma' Q.
Proof.
  move=> H1P H1Q HPQ sigma'.
  have H2Q : normal (substitute φ Q).
  { by apply: normal_simple_substituteI. }

  have H'PQ : red_beta (substitute ψ (substitute φ P)) (substitute φ Q).
  { by apply: eq_beta_normal. }

  have [fN HfN] := construct_fN' H'PQ H2Q.
  exists (fun x => prune id (simple_map_term fN (substitute ψ (decode_term x)))).
  constructor.
  - move=> ?. by apply: simple_prune.
  - subst sigma'. rewrite /substitute in HfN.
    rewrite -(prune_subst_term H1P).
    rewrite -(prune_subst_term H1Q).
    rewrite -HfN.
    by rewrite -key2'_final.
Qed.

(* a list of simple inequalities has a solution iff it has a simple solution *)
Theorem simple_convervativity (cs: list inequality) : 
  (* every inequality is simple *)
  (Forall (fun '(P, Q) => simple P /\ simple Q) cs) -> 
  (* cs has a normal solution *)
  HOSemiU cs ->
  (* cs has a simple solution *)
  exists (φ: valuation simple), forall (c: inequality), In c cs -> solution φ c.
Proof.
  move=> Hcs [φ /Forall_forall Hφ].
  unshelve eexists (valuationI simple (fun x => prune id (sval (φ x))) _).
  - move=> ? /=. by apply: simple_prune.
  - apply /Forall_forall.
    apply: Forall_impl (Forall_and Hcs Hφ).
    move=> [P Q] [[HP HQ]] [ψ] /(simple_solutionI HP HQ) /=.
    move=> [tau'] [Htau' H].
    exists (valuationI _ _ Htau').
    rewrite /substitute /valuationI /= H.
    by apply: rst_refl.
Qed.

Print Assumptions simple_convervativity.

(* EXPERIMENTAL *)

(* EXPLICIT Pi-K APPROACH, arr is Pi P Q such that 0 is fresh in Q *)
(* NOT NEEDED ?*)
(*
(* store Pimple type information up to a term leaf *)
Inductive term' := 
  | atom : term -> term'
  | arr : term' -> term' -> term'.

Fixpoint simplify (xi: nat -> nat) (P: term) : term' :=
  match P with
  | Pi P' Q' => 
      if fresh_inb 0 Q' 
        then arr (simplify xi P') (simplify (scons 0 xi) Q')
        else atom P
  | _ => atom P
  end.

  TODO 
(* make a term simple, remember non-simpel subterms as variables *)
Fixpoint prune2 (P: term') : term' :=
  match P with
  | atom P' => atom (var ())
  | Pi P' Q' => 
      if fresh_inb 0 Q' 
        then SemiU.arr (prune2 xi P') (prune2 (scons 0 xi) Q')
        else SemiU.atom (encode_term (ren_term xi P))
  | _ => SemiU.atom (encode_term (ren_term xi P))
  end.
*)

   (*
normal form formulations

Lemma normal_formE {P} : normal_form P ->
  match P with
  | var _ => True
  | const _ => True 
  | app (lam _ _) _ => False
  | app P Q => normal_form P /\ normal_form Q
  | lam P Q => normal_form P /\ normal_form Q
  | Pi P Q => normal_form P /\ normal_form Q
  end.
Proof.
  elim: P.
  - done.
  - done.
  - case.
    + move=> x _ Q. 

  move HR: (P) => R.
  elim: P R HR.
  - by move=> x R <-.
  -


  move=> Q. case.

(* a term is in normal form if it contains no beta-redex (lambda x : P. Q) R *)
Fixpoint is_normal_form (P : term) : bool :=
  match P with
  | var _ => true
  | const _ => true
  | app (lam _ _) _ => false
  | app P Q => is_normal_form P && is_normal_form Q
  | lam P Q => is_normal_form P && is_normal_form Q
  | Pi P Q => is_normal_form P && is_normal_form Q
  end.



Lemma is_normal_formP {P} : reflect (normal_form P) (is_normal_form P).
Proof.
  elim: P => /=.
  - move=> x. constructor=> Q. move HP: (var x) => P HPQ.
    by case: HPQ HP.
  - move=> c. constructor=> Q. move HP: (const c) => P HPQ.
    by case: HPQ HP.
  - case => /=.
    + move=> x _ Q HQ. move HP: (app _ _) => P.
      apply : (iffP HQ).
    Search reflect.
    
    constructor.
*)