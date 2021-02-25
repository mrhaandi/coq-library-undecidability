(* 
  Autor(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List Relation_Operators.

Require Import Undecidability.SemiUnification.autosubst.pts.

(* following imports could be incorporated into autosubst *)
Require Import Undecidability.SemiUnification.autosubst.unscoped_more.
Require Import Undecidability.SemiUnification.autosubst.pts_more.
Require Import Undecidability.SemiUnification.autosubst.allfv_more.

Require Import Undecidability.SemiUnification.PTSUtil.step_facts.
Require Import Undecidability.SemiUnification.PTSUtil.red_beta_facts.
Require Import Undecidability.SemiUnification.PTSUtil.eq_beta_facts.
Require Import Undecidability.SemiUnification.PTSUtil.normal_facts.
Require Import Undecidability.SemiUnification.PTSUtil.term_enum.
Opaque encode_term decode_term.

Require Import Undecidability.SemiUnification.HOSemiU.

(* FACTS *)
Require Import PeanoNat Lia.
Require Import Relations.Relation_Operators Relations.Operators_Properties.
Require Import ssreflect ssrbool ssrfun.

(* such that transp step Q P evaluates step P Q *)
Arguments transp {_} _ _ _ /.

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

(* END term enumerability *)

(* decidable equality on term *)
Lemma term_eq_dec (P Q: term) : {P = Q} + {P <> Q}.
Proof. by do 2 (decide equality). Qed. 

Definition non_zero x := if x is 0 then False else True.

Definition non_zero_dec x : {non_zero x} + {not (non_zero x)} :=
  if x is 0 then right id else left I.

(* decides whether 0 does not occur free in P *)
Definition fresh_0 (P: term) := allfv_term_dec non_zero P non_zero_dec.

(* make a term simple, remember non-simple subterms as variables *)
Fixpoint prune (xi: nat -> nat) (P: term) : term :=
  match P with
  | Pi P' Q' => 
      if fresh_0 Q' 
        then Pi (prune xi P') (ren_term shift (prune (scons 0 xi) Q'))
        else var (encode_term (ren_term xi P))
  | _ => var (encode_term (ren_term xi P))
  end.

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

(* apply map "f" to non-simple subterms *)
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

(* construct a valuation from a substitution sigma which pointwise satisfied predicate p *)
Definition valuationI (p: term -> Prop)
  (sigma: nat -> term) (H: forall x, p (sigma x)) : valuation p :=
  (fun x => exist _ _ (H x)).

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

(* anny solution φ to a simple instance (P, Q) entails a simple solution sigma' *)
Lemma simple_solutionI {φ ψ: valuation normal} {P Q} : simple P -> simple Q -> 
  eq_beta (substitute ψ (substitute φ P)) (substitute φ Q) ->
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
  HOSemiU' cs ->
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

(* normal substitutions and normalizing substitutions are equivalent for 
  higher-order semi-unification *)
Theorem HOSemiU_iff_HOSemiU' {cs: list inequality} : HOSemiU cs <-> HOSemiU' cs.
Proof.
  constructor.
  - move=> [φ] /Forall_forall Hφ.
    exists (fun x => exist _ _ (proj1 (svalP (normalize (svalP (φ x)))))).
    apply /Forall_forall. apply: Forall_impl Hφ.
    move=> [P Q] /= [ψ Hψ].
    exists (fun x => exist _ _ (proj1 (svalP (normalize (svalP (ψ x)))))).
    rewrite /substitute /=.
    set ψ' := (ψ' in subst_term ψ' (subst_term _ _)).
    set φ' := (φ' in subst_term φ' Q). rewrite -/φ'.
    have Hφ' : forall P', eq_beta (substitute φ P') (subst_term φ' P').
    { rewrite /substitute /φ' => ?. apply: ext_eq_beta_subst_term => x /=.
      apply: clos_rt_clos_rst.
      exact: proj2 (svalP (normalize (svalP (φ x)))). }
    have Hψ' : forall P', eq_beta (substitute ψ P') (subst_term ψ' P').
    { rewrite /substitute /ψ' => ?. apply: ext_eq_beta_subst_term => x /=.
      apply: clos_rt_clos_rst.
      exact: proj2 (svalP (normalize (svalP (ψ x)))). }
    apply: rst_trans; last by apply: Hφ'.
    apply: rst_trans; last by apply: Hψ.
    apply: rst_sym. apply: rst_trans; first by apply: Hψ'.
    by apply: eq_beta_subst_termI.
  - move=> [φ'] /Forall_forall Hφ'.
    exists (fun x => exist _ _ (normalizing_normal (svalP (φ' x)))).
    apply /Forall_forall. apply: Forall_impl Hφ' => - [P Q] [ψ' Hψ'].
    by exists (fun x => exist _ _ (normalizing_normal (svalP (ψ' x)))).
Qed.
