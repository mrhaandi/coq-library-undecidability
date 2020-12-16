Require Import Undecidability.SystemF.SysF 
  Undecidability.SystemF.Autosubst.unscoped 
  Undecidability.SystemF.Autosubst.syntax.

Require Import ssreflect ssrbool ssrfun.

(* hide low-level details *)
Module Rules.
Local Arguments funcomp _ _ _ /.
Local Arguments fext_eq _ _ /.

Lemma eq_trans_sym [A : Type] [x y z : A] : z = y -> x = y -> x = z.
Proof. intros. subst. reflexivity. Qed.

Lemma scons_comp {X Y: Type} {x: X} {f: nat -> X} {g: X -> Y} {n: nat} :
  g (scons x f n) = scons (g x) (funcomp g f) n.
Proof. destruct n; reflexivity. Qed.

Lemma ext_scons {X: Type} {x y: X} {f g: nat -> X} {n: nat} : 
  x = y -> fext_eq f g -> scons x f n = scons y g n.
Proof.
  intros H1 H2. destruct n.
  - assumption.
  - exact (H2 n).
Qed.

Definition ren_ren_poly_type {xi : nat -> nat} {zeta: nat -> nat} {s : poly_type} : 
  ren_poly_type zeta (ren_poly_type xi s) = ren_poly_type (funcomp zeta xi) s :=
  renRen_poly_type xi zeta s.

Definition subst_poly_type_poly_var {sigma : nat -> poly_type} {Eqpoly_type : forall x, sigma x = poly_var x} {s : poly_type} : 
  subst_poly_type sigma s = s := 
  idSubst_poly_type sigma Eqpoly_type s.

Lemma ren_poly_type_id {xi : nat -> nat} {s : poly_type} : fext_eq xi id ->
  ren_poly_type xi s = s.
Proof.
  move=> /= H.
  rewrite (rinst_inst_poly_type _ poly_var).
  - move=> ? /=. by rewrite H.
  - by apply: subst_poly_type_poly_var.
Qed.

End Rules.

Import Rules.

(* note: simple refine is too buggy #13639 *)
(* proves s = t goals *)
Ltac eq_asimpl := 
  intro ||
  assumption ||
  (simple apply erefl) || 
  (simple apply (eq_trans scons_comp)) || simple apply (eq_trans_sym scons_comp) ||
  (simple apply (eq_trans ren_ren_poly_type)) || simple apply (eq_trans_sym ren_ren_poly_type) ||
  (simple apply ext_scons) ||
  (simple apply ren_poly_type_id) || (simple apply (eq_sym ren_poly_type_id)) ||
  (simple apply subst_poly_type_poly_var) || (simple apply (eq_sym subst_poly_type_poly_var)).  

Ltac eq_asimpl2 :=
  match goal with
  (* general rules *)
  | |- _ => intro || assumption || (simple apply erefl)
  (* extensionality rules *)
  | |- poly_var _ = poly_var _ => congr poly_var
  | |- poly_arr _ _ = poly_arr _ _ => congr poly_arr
  | |- poly_abs _ = poly_abs _ => congr poly_abs
  | |- scons ?x ?f ?n = scons ?y ?g ?n => refine (@ext_scons _ x y f g n _ _)
  | |- ren_poly_type ?xi ?s = ?s => refine (@ren_poly_type_id xi s _)
  | |- ren_poly_type ?xi ?s = ren_poly_type ?zeta ?s => refine (extRen_poly_type xi zeta _ s)
  | |- subst_poly_type ?sigma ?s = ?s => refine (@subst_poly_type_poly_var sigma _ s)
  | |- ?s = subst_poly_type ?sigma ?s => refine (eq_sym (@subst_poly_type_poly_var sigma _ s))
  | |- subst_poly_type ?sigma ?s = subst_poly_type ?tau ?s => refine (ext_poly_type sigma tau _ s)
  | |- subst_poly_type ?sigma ?s = ren_poly_type ?zeta ?s => refine (eq_sym (rinst_inst_poly_type zeta sigma _ s))
  | |- ren_poly_type ?zeta ?s = subst_poly_type ?sigma ?s => refine (rinst_inst_poly_type zeta sigma _ s)
  (* reduction rules *)
  | |- ?g (scons ?x ?f ?n) = ?t => refine (eq_trans (@scons_comp _ _ x f g n) _)
  | |- ?t = ?g (scons ?x ?f ?n) => refine (eq_trans _ (eq_sym (@scons_comp _ _ x f g n)))
  | |- ren_poly_type ?zeta (ren_poly_type ?xi ?s) = ?t => refine (eq_trans (@ren_ren_poly_type xi zeta s) _)
  | |- ?t = ren_poly_type ?zeta (ren_poly_type ?xi ?s) => refine (eq_trans _ (eq_sym (@ren_ren_poly_type xi zeta s)))
  | |- subst_poly_type ?sigma (ren_poly_type ?xi ?s) = ?t => refine (eq_trans (renComp_poly_type xi sigma s) _)
  | |- ?t = subst_poly_type ?sigma (ren_poly_type ?xi ?s) => refine (eq_trans _ (eq_sym (renComp_poly_type xi sigma s)))
  | |- subst_poly_type ?sigma (subst_poly_type ?tau ?s) = ?t => refine (eq_trans (compComp_poly_type tau sigma s) _)
  | |- ?t = subst_poly_type ?sigma (subst_poly_type ?tau ?s) => refine (eq_trans _ (eq_sym (compComp_poly_type tau sigma s)))
  end.
  