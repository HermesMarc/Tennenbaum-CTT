
Require Import Tarski.
Require Import List.

Notation "x 'el' A" := (In x A) (at level 70).
Notation "A '<<=' B" := (incl A B) (at level 70).


Local Set Implicit Arguments.

Inductive peirce := class | intu.
Existing Class peirce.

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Reserved Notation "A ⊢ phi" (at level 61).

  (** * Natural Deduction  *)
  (** ** Definition *)

  Implicit Type p : peirce.
  Implicit Type ff : falsity_flag.

  Inductive prv : forall (ff : falsity_flag) (p : peirce), list form -> form -> Prop :=
  | II {ff} {p} A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi
  | IE {ff} {p} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | AllI {ff} {p} A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
  | AllE {ff} {p} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
  | ExI {ff} {p} A t phi : A ⊢ phi[t..] -> A ⊢ ∃ phi
  | ExE {ff} {p} A phi psi : A ⊢ ∃ phi -> phi::(map (subst_form ↑) A) ⊢ psi[↑] -> A ⊢ psi
  | Exp {p} A phi : prv p A falsity -> prv p A phi
  | Ctx {ff} {p} A phi : phi el A -> A ⊢ phi
  | CI {ff} {p} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 {ff} {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 {ff} {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
  | DI1 {ff} {p} A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
  | DI2 {ff} {p} A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
  | DE {ff} {p} A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
  | Pc {ff} A phi psi : prv class A (((phi --> psi) --> phi) --> phi)
  where "A ⊢ phi" := (prv _ A phi).

  Definition tprv `{falsity_flag} `{peirce} (T : form -> Prop) phi :=
    exists A, (forall psi, psi el A -> T psi) /\ A ⊢ phi.

End ND_def.

Arguments prv {_ _ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 55).
Notation "A ⊢C phi" := (@prv _ _ _ class A phi) (at level 55).
Notation "A ⊢I phi" := (@prv _ _ _ intu A phi) (at level 55).
Notation "A ⊢M phi" := (@prv _ _ falsity_off intu A phi) (at level 55).
Notation "T ⊢T phi" := (tprv T phi) (at level 55).
Notation "T ⊢TI phi" := (@tprv _ _ _ intu T phi) (at level 55).
Notation "T ⊢TC phi" := (@tprv _ _ _ class T phi) (at level 55).



Ltac comp := repeat (progress (cbn in *; autounfold in *)).


(** ** Lemmas for context manipulation. *)
                     
Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Context {ff : falsity_flag}.
  Context {p : peirce}.

  Theorem Weak A B phi :
    A ⊢ phi -> A <<= B -> B ⊢ phi.
  Proof.
    intros H. revert B.
    induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
  Qed.


  Lemma combine_context {Γ1 Γ2} alpha beta : Γ1 ⊢ alpha -> Γ2 ⊢ (alpha --> beta) -> (Γ1 ++ Γ2) ⊢ beta.
  Proof.
    intros H1 H2.
    apply (@Weak _ (Γ1 ++ Γ2)) in H1.
    apply (@Weak _ (Γ1 ++ Γ2)) in H2.
    eapply IE; eassumption.
    now apply incl_appr. now apply incl_appl.
  Qed.


  Hint Constructors prv : core.

  
  Lemma imps T phi psi :
    T ⊢ phi --> psi <-> (phi :: T) ⊢ psi.
  Proof.
    split; try apply II.
    intros H. apply IE with phi; auto. apply (Weak H). firstorder. apply Ctx; firstorder.
  Qed.

  Lemma CE T phi psi :
    T ⊢ phi ∧ psi -> T ⊢ phi /\ T ⊢ psi.
  Proof.
    intros H. split.
    - apply (CE1 H).
    - apply (CE2 H).
  Qed.

  Lemma DE' A phi :
    A ⊢ phi ∨ phi -> A ⊢ phi.
  Proof.
    intros H. apply (DE H); apply Ctx; firstorder.
  Qed.

  Lemma switch_conj_imp alpha beta phi A :
    A ⊢ alpha ∧ beta --> phi <-> A ⊢ alpha --> beta --> phi.
  Proof.
    split; intros H.
    - apply II, II. eapply IE.
      apply (@Weak A). apply H. firstorder.
      apply CI; apply Ctx; firstorder.
    - apply II. eapply IE. eapply IE.
      eapply Weak. apply H.
      firstorder.
      eapply CE1, Ctx; firstorder.
      eapply CE2, Ctx; firstorder.
  Qed.

    
End ND_def.


Hint Constructors prv : core.




(** ** Soundness *)

Section Soundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma soundness {ff : falsity_flag} A phi :
    A ⊢I phi -> valid_ctx A phi.
  Proof.
    remember intu as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    - exists (eval rho t). cbn. specialize (IHprv Heqp D I rho HA).
      apply sat_comp in IHprv. eapply sat_ext; try apply IHprv. now intros [].
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Heqp D I (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - firstorder.
    - firstorder. now apply H0.
    - firstorder. now apply H0.
    - firstorder.
    - firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - discriminate.
  Qed.

  Lemma soundness' {ff : falsity_flag} phi :
    List.nil ⊢I phi -> valid phi.
  Proof.
    intros H % soundness.
    intros D I rho. apply H. cbn. firstorder.
  Qed.

  Corollary tsoundness {ff : falsity_flag} T phi :
    T ⊢TI phi -> forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi.
  Proof.
    intros (A & H1 & H2) D I rho HI. apply (soundness H2).
    intros psi HP. apply HI, H1, HP.
  Qed.
 
  Hypothesis LEM : forall P, P \/ ~ P.

  Lemma Peirce (P Q : Prop) :
    ((P -> Q) -> P) -> P.
  Proof.
    destruct (LEM (((P -> Q) -> P) -> P)); tauto.
  Qed.

  Lemma soundness_class {ff : falsity_flag} A phi :
    A ⊢C phi -> valid_ctx A phi.
  Proof.
    remember class as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    - exists (eval rho t). cbn. specialize (IHprv Heqp D I rho HA).
      apply sat_comp in IHprv. eapply sat_ext; try apply IHprv. now intros [].
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Heqp D I (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - clear LEM. firstorder.
    - firstorder. now apply H0.
    - firstorder. now apply H0.
    - clear LEM. firstorder.
    - clear LEM. firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - apply Peirce.
  Qed.

  Lemma soundness_class' {ff : falsity_flag} phi :
    List.nil ⊢C phi -> valid phi.
  Proof.
    intros H % soundness_class. clear LEM.
    intros D I rho. apply H. cbn. firstorder.
  Qed.

  Corollary tsoundness_class {ff : falsity_flag} T phi :
    T ⊢TC phi -> forall D (I : interp D) rho, (forall psi, T psi -> rho ⊨ psi) -> rho ⊨ phi.
  Proof.
    intros (A & H1 & H2) D I rho HI. apply (soundness_class H2).
    intros psi HP. apply HI, H1, HP.
  Qed.

End Soundness.




Section Incl.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Notation "A ⊏ B" := (forall psi, psi el A -> B psi) (at level 70).
  
  Lemma incl_app {ff : falsity_flag} (A B : list form) (T : form -> Prop) : A ⊏ T -> B ⊏ T -> A ++ B ⊏ T.
  Proof.
    intros H1 H2 psi []%List.in_app_or.
    now apply H1. now apply H2.
  Qed.

End Incl.