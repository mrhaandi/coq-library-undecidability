Require Export Undecidability.SemiUnification.unscoped.
Require Export Undecidability.SemiUnification.header_extensible.

(* added "->" as syntactic sugar, renamed "term_var" into "var" *)
Inductive term : Type :=
  | var : nat -> term
  | const : nat -> term
  | app : term -> term -> term
  | lam : term -> term -> term
  | pi : term -> term -> term.

Lemma congr_const {s0 : nat} {t0 : nat} (H0 : eq s0 t0) :
  eq (const s0) (const t0).
Proof.
exact (eq_trans eq_refl (ap (fun x => const x) H0)).
Qed.
Lemma congr_app {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : eq s0 t0) (H1 : eq s1 t1) : eq (app s0 s1) (app t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
                (ap (fun x => app t0 x) H1)).
Qed.
Lemma congr_lam {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : eq s0 t0) (H1 : eq s1 t1) : eq (lam s0 s1) (lam t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lam x s1) H0))
                (ap (fun x => lam t0 x) H1)).
Qed.
Lemma congr_pi {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : eq s0 t0) (H1 : eq s1 t1) : eq (pi s0 s1) (pi t0 t1).
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pi x s1) H0))
                (ap (fun x => pi t0 x) H1)).
Qed.
Definition upRen_term_term (xi : forall _ : nat, nat) :
  forall _ : nat, nat := up_ren xi.
Fixpoint ren_term (xi_term : forall _ : nat, nat) (s : term) : term :=
  match s with
  | var s0 => var (xi_term s0)
  | const s0 => const ((fun x => x) s0)
  | app s0 s1 => app (ren_term xi_term s0) (ren_term xi_term s1)
  | lam s0 s1 =>
      lam (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
  | pi s0 s1 =>
      pi (ren_term xi_term s0) (ren_term (upRen_term_term xi_term) s1)
  end.
Definition up_term_term (sigma : forall _ : nat, term) :
  forall _ : nat, term :=
  scons (var var_zero) (funcomp (ren_term shift) sigma).
Fixpoint subst_term (sigma_term : forall _ : nat, term) (s : term) : term :=
  match s with
  | var s0 => sigma_term s0
  | const s0 => const ((fun x => x) s0)
  | app s0 s1 => app (subst_term sigma_term s0) (subst_term sigma_term s1)
  | lam s0 s1 =>
      lam (subst_term sigma_term s0)
        (subst_term (up_term_term sigma_term) s1)
  | pi s0 s1 =>
      pi (subst_term sigma_term s0) (subst_term (up_term_term sigma_term) s1)
  end.
Definition upId_term_term (sigma : forall _ : nat, term)
  (Eq : forall x, eq (sigma x) (var x)) :
  forall x, eq (up_term_term sigma x) (var x) :=
  fun n =>
  match n with
  | S n' => ap (ren_term shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint idSubst_term (sigma_term : forall _ : nat, term)
(Eq_term : forall x, eq (sigma_term x) (var x)) (s : term) :
eq (subst_term sigma_term s) s :=
  match s with
  | var s0 => Eq_term s0
  | const s0 => congr_const ((fun x => eq_refl x) s0)
  | app s0 s1 =>
      congr_app (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  | lam s0 s1 =>
      congr_lam (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  | pi s0 s1 =>
      congr_pi (idSubst_term sigma_term Eq_term s0)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  end.
Definition upExtRen_term_term (xi : forall _ : nat, nat)
  (zeta : forall _ : nat, nat) (Eq : forall x, eq (xi x) (zeta x)) :
  forall x, eq (upRen_term_term xi x) (upRen_term_term zeta x) :=
  fun n => match n with
           | S n' => ap shift (Eq n')
           | O => eq_refl
           end.
Fixpoint extRen_term (xi_term : forall _ : nat, nat)
(zeta_term : forall _ : nat, nat)
(Eq_term : forall x, eq (xi_term x) (zeta_term x)) (s : term) :
eq (ren_term xi_term s) (ren_term zeta_term s) :=
  match s with
  | var s0 => ap var (Eq_term s0)
  | const s0 => congr_const ((fun x => eq_refl x) s0)
  | app s0 s1 =>
      congr_app (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  | lam s0 s1 =>
      congr_lam (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  | pi s0 s1 =>
      congr_pi (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  end.
Definition upExt_term_term (sigma : forall _ : nat, term)
  (tau : forall _ : nat, term) (Eq : forall x, eq (sigma x) (tau x)) :
  forall x, eq (up_term_term sigma x) (up_term_term tau x) :=
  fun n =>
  match n with
  | S n' => ap (ren_term shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint ext_term (sigma_term : forall _ : nat, term)
(tau_term : forall _ : nat, term)
(Eq_term : forall x, eq (sigma_term x) (tau_term x)) (s : term) :
eq (subst_term sigma_term s) (subst_term tau_term s) :=
  match s with
  | var s0 => Eq_term s0
  | const s0 => congr_const ((fun x => eq_refl x) s0)
  | app s0 s1 =>
      congr_app (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  | lam s0 s1 =>
      congr_lam (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  | pi s0 s1 =>
      congr_pi (ext_term sigma_term tau_term Eq_term s0)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  end.
Definition up_ren_ren_term_term (xi : forall _ : nat, nat)
  (zeta : forall _ : nat, nat) (rho : forall _ : nat, nat)
  (Eq : forall x, eq (funcomp zeta xi x) (rho x)) :
  forall x,
  eq (funcomp (upRen_term_term zeta) (upRen_term_term xi) x)
    (upRen_term_term rho x) := up_ren_ren xi zeta rho Eq.
Fixpoint compRenRen_term (xi_term : forall _ : nat, nat)
(zeta_term : forall _ : nat, nat) (rho_term : forall _ : nat, nat)
(Eq_term : forall x, eq (funcomp zeta_term xi_term x) (rho_term x))
(s : term) :
eq (ren_term zeta_term (ren_term xi_term s)) (ren_term rho_term s) :=
  match s with
  | var s0 => ap var (Eq_term s0)
  | const s0 => congr_const ((fun x => eq_refl x) s0)
  | app s0 s1 =>
      congr_app (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | lam s0 s1 =>
      congr_lam (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  | pi s0 s1 =>
      congr_pi (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  end.
Definition up_ren_subst_term_term (xi : forall _ : nat, nat)
  (tau : forall _ : nat, term) (theta : forall _ : nat, term)
  (Eq : forall x, eq (funcomp tau xi x) (theta x)) :
  forall x,
  eq (funcomp (up_term_term tau) (upRen_term_term xi) x)
    (up_term_term theta x) :=
  fun n =>
  match n with
  | S n' => ap (ren_term shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint compRenSubst_term (xi_term : forall _ : nat, nat)
(tau_term : forall _ : nat, term) (theta_term : forall _ : nat, term)
(Eq_term : forall x, eq (funcomp tau_term xi_term x) (theta_term x))
(s : term) :
eq (subst_term tau_term (ren_term xi_term s)) (subst_term theta_term s) :=
  match s with
  | var s0 => Eq_term s0
  | const s0 => congr_const ((fun x => eq_refl x) s0)
  | app s0 s1 =>
      congr_app (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | lam s0 s1 =>
      congr_lam (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  | pi s0 s1 =>
      congr_pi (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  end.
Definition up_subst_ren_term_term (sigma : forall _ : nat, term)
  (zeta_term : forall _ : nat, nat) (theta : forall _ : nat, term)
  (Eq : forall x, eq (funcomp (ren_term zeta_term) sigma x) (theta x)) :
  forall x,
  eq (funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x)
    (up_term_term theta x) :=
  fun n =>
  match n with
  | S n' =>
      eq_trans
        (compRenRen_term shift (upRen_term_term zeta_term)
           (funcomp shift zeta_term) (fun x => eq_refl) (sigma n'))
        (eq_trans
           (eq_sym
              (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                 (fun x => eq_refl) (sigma n')))
           (ap (ren_term shift) (Eq n')))
  | O => eq_refl
  end.
Fixpoint compSubstRen_term (sigma_term : forall _ : nat, term)
(zeta_term : forall _ : nat, nat) (theta_term : forall _ : nat, term)
(Eq_term : forall x,
           eq (funcomp (ren_term zeta_term) sigma_term x) (theta_term x))
(s : term) :
eq (ren_term zeta_term (subst_term sigma_term s)) (subst_term theta_term s)
:=
  match s with
  | var s0 => Eq_term s0
  | const s0 => congr_const ((fun x => eq_refl x) s0)
  | app s0 s1 =>
      congr_app
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | lam s0 s1 =>
      congr_lam
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  | pi s0 s1 =>
      congr_pi (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  end.
Definition up_subst_subst_term_term (sigma : forall _ : nat, term)
  (tau_term : forall _ : nat, term) (theta : forall _ : nat, term)
  (Eq : forall x, eq (funcomp (subst_term tau_term) sigma x) (theta x)) :
  forall x,
  eq (funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x)
    (up_term_term theta x) :=
  fun n =>
  match n with
  | S n' =>
      eq_trans
        (compRenSubst_term shift (up_term_term tau_term)
           (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
           (sigma n'))
        (eq_trans
           (eq_sym
              (compSubstRen_term tau_term shift
                 (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                 (sigma n'))) (ap (ren_term shift) (Eq n')))
  | O => eq_refl
  end.
Fixpoint compSubstSubst_term (sigma_term : forall _ : nat, term)
(tau_term : forall _ : nat, term) (theta_term : forall _ : nat, term)
(Eq_term : forall x,
           eq (funcomp (subst_term tau_term) sigma_term x) (theta_term x))
(s : term) :
eq (subst_term tau_term (subst_term sigma_term s)) (subst_term theta_term s)
:=
  match s with
  | var s0 => Eq_term s0
  | const s0 => congr_const ((fun x => eq_refl x) s0)
  | app s0 s1 =>
      congr_app
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | lam s0 s1 =>
      congr_lam
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  | pi s0 s1 =>
      congr_pi
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  end.
Definition rinstInst_up_term_term (xi : forall _ : nat, nat)
  (sigma : forall _ : nat, term)
  (Eq : forall x, eq (funcomp var xi x) (sigma x)) :
  forall x,
  eq (funcomp var (upRen_term_term xi) x) (up_term_term sigma x) :=
  fun n =>
  match n with
  | S n' => ap (ren_term shift) (Eq n')
  | O => eq_refl
  end.
Fixpoint rinst_inst_term (xi_term : forall _ : nat, nat)
(sigma_term : forall _ : nat, term)
(Eq_term : forall x, eq (funcomp var xi_term x) (sigma_term x))
(s : term) : eq (ren_term xi_term s) (subst_term sigma_term s) :=
  match s with
  | var s0 => Eq_term s0
  | const s0 => congr_const ((fun x => eq_refl x) s0)
  | app s0 s1 =>
      congr_app (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | lam s0 s1 =>
      congr_lam (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  | pi s0 s1 =>
      congr_pi (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  end.
Lemma rinstInst_term (xi_term : forall _ : nat, nat) :
  eq (ren_term xi_term) (subst_term (funcomp var xi_term)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => rinst_inst_term xi_term _ (fun n => eq_refl) x)).
Qed.
Lemma instId_term : eq (subst_term var) id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => idSubst_term var (fun n => eq_refl) (id x))).
Qed.
Lemma rinstId_term : eq (@ren_term id) id.
Proof.
exact (eq_trans (rinstInst_term (id _)) instId_term).
Qed.
Lemma varL_term (sigma_term : forall _ : nat, term) :
  eq (funcomp (subst_term sigma_term) var) sigma_term.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma varLRen_term (xi_term : forall _ : nat, nat) :
  eq (funcomp (ren_term xi_term) var) (funcomp var xi_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun x => eq_refl)).
Qed.
Lemma renRen_term (xi_term : forall _ : nat, nat)
  (zeta_term : forall _ : nat, nat) (s : term) :
  eq (ren_term zeta_term (ren_term xi_term s))
    (ren_term (funcomp zeta_term xi_term) s).
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.
Lemma renRen'_term (xi_term : forall _ : nat, nat)
  (zeta_term : forall _ : nat, nat) :
  eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renRen_term xi_term zeta_term n)).
Qed.
Lemma compRen_term (sigma_term : forall _ : nat, term)
  (zeta_term : forall _ : nat, nat) (s : term) :
  eq (ren_term zeta_term (subst_term sigma_term s))
    (subst_term (funcomp (ren_term zeta_term) sigma_term) s).
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.
Lemma compRen'_term (sigma_term : forall _ : nat, term)
  (zeta_term : forall _ : nat, nat) :
  eq (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compRen_term sigma_term zeta_term n)).
Qed.
Lemma renComp_term (xi_term : forall _ : nat, nat)
  (tau_term : forall _ : nat, term) (s : term) :
  eq (subst_term tau_term (ren_term xi_term s))
    (subst_term (funcomp tau_term xi_term) s).
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.
Lemma renComp'_term (xi_term : forall _ : nat, nat)
  (tau_term : forall _ : nat, term) :
  eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => renComp_term xi_term tau_term n)).
Qed.
Lemma compComp_term (sigma_term : forall _ : nat, term)
  (tau_term : forall _ : nat, term) (s : term) :
  eq (subst_term tau_term (subst_term sigma_term s))
    (subst_term (funcomp (subst_term tau_term) sigma_term) s).
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.
Lemma compComp'_term (sigma_term : forall _ : nat, term)
  (tau_term : forall _ : nat, term) :
  eq (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
                (fun n => compComp_term sigma_term tau_term n)).
Qed.
