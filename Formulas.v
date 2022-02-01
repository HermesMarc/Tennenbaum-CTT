Require Import FOL Peano Tarski Deduction CantorPairing Synthetic DecidabilityFacts NumberTheory.
Require Import Lia.
Require Import Equations.Equations Equations.Prop.DepElim.

Import Vector.VectorNotations.


Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).


Lemma switch_nat_num α rho (n : nat) : sat interp_nat rho (α[(num n)..]) <-> sat interp_nat (n.:rho) α.
Proof.
  split; intros H.
  - rewrite <- (inu_nat_id n). erewrite <-eval_num. apply sat_single, H.
  - apply sat_single. now rewrite eval_num, inu_nat_id.
Qed.

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.


Ltac invert_bounds1 :=
  match goal with
    H : bounded _ _ |- _ => inversion H; subst; clear H
  end.

Ltac invert_bounds :=
  invert_bounds1; 
  repeat match goal with
    H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H; try decide equality; subst
  end.


Section Delta0.

  (** Define Δ0 and Σ1 formulas *)

  Inductive delta0 : form -> Type :=
  | Delta_fal :  delta0 ⊥
  | Delta_eq : forall t s,  delta0 (t == s)
  | Delta_Conj : forall α β b,  delta0 α -> delta0 β ->  delta0 (bin b α β).


    Ltac invert_delta1 :=
    match goal with
      H : delta0 _ |- _ => inversion H; subst; clear H
    end.

    Ltac invert_delta :=
    invert_delta1; 
    repeat match goal with
      H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H; try decide equality; subst
    end.


  Lemma inversion_bounded_bin α β n b : 
    bounded n (bin b α β) -> bounded n α /\ bounded n β.
  Proof.
    intros H. destruct b.
    all: now invert_bounds.
  Qed.

  Lemma inversion_delta0_bin α β b : delta0 (bin b α β) -> delta0 α * delta0 β.
  Proof.
    intros H. destruct b.
    all: now invert_delta.
  Qed.


  (* Formulas stay at their level of the hierarchy under substitions. *)
  
  Fact subst_delta0 {ff : falsity_flag} phi sigma : 
    delta0 phi -> delta0 phi[sigma].
  Proof.
    induction 1; now constructor.
  Qed.


  (* Numerals are closed terms. *)

  Lemma closed_num n k : bounded_t k (num n).
  Proof.
    eapply bounded_up_t. instantiate (1 := 0).
    induction n; cbn; now solve_bounds. lia.
  Qed.


  Lemma vec_map_preimage {X N} (v : Vector.t term N) f (x : X) :
    Vector.In x (Vector.map f v) -> exists t, Vector.In t v /\ x = f t.
  Proof.
    induction v; cbn; intros H.
    - inversion H.
    - inversion H.
      exists h. split. constructor. reflexivity.
      apply Eqdep_dec.inj_pair2_eq_dec in H3. subst.
      destruct (IHv H2) as [t Ht].
      exists t. split. constructor. all: try apply Ht.
      decide equality.
  Qed.


  Lemma subst_bound_t t N B sigma :
    bounded_t N t -> (forall n, n < N -> bounded_t B (sigma n) ) -> bounded_t B (t`[sigma]).
  Proof.
    induction 1 as [| f v H IH]; intros HN; cbn.
    - now apply HN. 
    - constructor. intros s (t & Ht & ->)%vec_map_preimage.
      now apply IH.
  Qed.

  Lemma subst_bound phi :
    forall sigma N B, bounded N phi -> (forall n, n < N -> bounded_t B (sigma n) ) -> bounded B phi[sigma].
  Proof.
    induction phi using form_ind_falsity_on; cbn.
    all: intros sigma N B HN HB.
    - solve_bounds.
    - constructor. intros v Hv. depelim Hv.
    - apply inversion_bounded_bin in HN. destruct HN.
      constructor.
      + eapply IHphi1; eauto.
      + eapply IHphi2; eauto.
    - constructor; eapply subst_bound_t with (N := N); auto.
      all: now inversion HN.
    - constructor. apply IHphi with (N:= S N).
      + now invert_bounds.
      + intros [|n] hn.
        * constructor. lia.
        * eapply subst_bound_t.
          ** apply HB. lia.
          ** intros ??. constructor. lia.
  Qed.

End Delta0.




(* PA and Q are consistent in Coq. *)

Lemma PA_consistent : ~ PA ⊢TI ⊥.
Proof.
  intros H. eapply tsoundness in H.
  2: instantiate (1 := fun _ => 0).
  apply H.
  intros ax Hax. 
  now apply PA_std_axioms.
Qed.

Corollary Q_consistent : ~ Q ⊢I ⊥.
Proof.
  intros H. apply PA_consistent.
  exists Q. split; [constructor|]; auto.
Qed.


Fact Faster1 {X} A (x : X) : A <<= x :: A.
Proof.
  firstorder.
Qed.

Fact Faster2 {X} A (x y : X) : A <<= x :: y :: A.
Proof.
  firstorder.
Qed.


Definition Q_dec ϕ := {Q ⊢I ϕ} + {Q ⊢I ¬ ϕ}.

Lemma Q_neg_equiv ϕ : 
  Q_dec ϕ -> (~ Q ⊢I ϕ) <-> Q ⊢I ¬ ϕ.
Proof.
  intros dec. split.
    - intros. now destruct dec.
    - intros H1 H2.
      apply PA_consistent.
      exists Q. split. intros.
      now constructor.
      eapply IE. apply H1. apply H2.
Qed.


(* Results concerning closed Delta_0 Formulas *)

Section Closed.

  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  
  Variable phi : form.
  Variable Hcl : bounded 0 phi.
  Variable H0 : delta0 phi.

  Variable D : Type.
  Variable I : interp D.
  Variable axioms : forall ax, PA ax -> ⊨ ax. 


  Theorem Q_dec_closed_delta0 :
    Q_dec phi.
  Proof.
    induction H0.
    - cbn -[Q]. right.
      apply II, Ctx. firstorder.
    - apply term_eq_dec; now inversion Hcl. 
    - apply inversion_bounded_bin in Hcl.
      apply inversion_delta0_bin in H0.
      specialize (IHd1 (proj1 Hcl) (fst H0)).
      specialize (IHd2 (proj2 Hcl) (snd H0)).
      destruct b.
      + destruct IHd1 as [Hf1 | Hf1], IHd2 as [Hf2 | Hf2].
        left. now apply CI.
        all: right; apply II.
        eapply IE. apply Weak with Q. apply Hf2. shelve.
        eapply CE2, Ctx. firstorder.
        eapply IE. apply Weak with Q. apply Hf1. shelve.
        eapply CE1, Ctx. firstorder.
        eapply IE. apply Weak with Q. apply Hf2. shelve.
        eapply CE2, Ctx. firstorder.
        Unshelve. all: apply Faster1.
      + destruct IHd1 as [Hf1 | Hf1], IHd2 as [Hf2 | Hf2].
        all: try (left; now (apply DI1 + apply DI2)).
        right. apply II. eapply DE.
        apply Ctx; firstorder.
        eapply IE. apply Weak with Q. apply Hf1. apply Faster2.
        apply Ctx; firstorder.
        eapply IE. apply Weak with Q. apply Hf2. apply Faster2.
        apply Ctx; firstorder.
      + destruct IHd1 as [Hf1 | Hf1], IHd2 as [Hf2 | Hf2].
        left. apply II. apply Weak with Q. apply Hf2. apply Faster1.
        right. apply II. eapply IE.
        apply Weak with Q. apply Hf2. apply Faster1.
        eapply IE. apply Ctx. firstorder.
        apply Weak with Q. apply Hf1. apply Faster1.
        left. now apply imps, Exp, imps.
        left. now apply imps, Exp, imps.
  Qed.




  Corollary Q_neg_equiv_delta0 : (~ Q ⊢I phi) <-> Q ⊢I ¬ phi.
  Proof.
    apply Q_neg_equiv, Q_dec_closed_delta0.
  Qed.


  Corollary dec_closed_delta0: {PA ⊢TI phi} + {PA ⊢TI ¬ phi}.
  Proof.
    destruct Q_dec_closed_delta0 as [H|H].
    - left. exists Q. split.
      intros; now constructor.
      apply H.
    - right. exists Q. split.
      intros; now constructor.
      apply H. 
  Qed.


  Corollary neg_equiv_delta0 : (~ PA ⊢TI phi) <-> PA ⊢TI ¬ phi.
  Proof.
    split.
    - intros. now destruct dec_closed_delta0.
    - intros [Γ1 []] [Γ2 []].
      apply PA_consistent.
      exists (Γ1 ++ Γ2)%list.
      split. now apply incl_app.
      eapply IE. eapply Weak. apply H1. intuition.
      eapply Weak. apply H3. intuition. 
  Qed.


  Lemma delta0_complete rho : 
    sat interp_nat rho phi -> PA ⊢TI phi.
  Proof.
    intros H. destruct dec_closed_delta0 as [C|C]. assumption.
    specialize (tsoundness C interp_nat rho) as F.
    exfalso. apply F. apply PA_std_axioms. apply H.
  Qed.

  Lemma Q_delta0_complete rho : 
    sat interp_nat rho phi -> Q ⊢I phi.
  Proof.
    intros H. destruct Q_dec_closed_delta0 as [C|C]. assumption.
    specialize (soundness C interp_nat rho) as F.
    exfalso. apply F.
    apply Q_std_axioms. apply H.
  Qed.


  Lemma delta0_complete' rho : 
    sat I rho phi -> PA ⊢TI phi.
  Proof.
    intros H. destruct dec_closed_delta0 as [C|C]. assumption.
    specialize (tsoundness C I rho) as F.
    exfalso. apply F. intuition. apply H.
  Qed.


  Lemma Q_delta0_complete' rho : 
    sat I rho phi -> Q ⊢I phi.
  Proof.
    intros H. destruct Q_dec_closed_delta0 as [C|C]. assumption.
    specialize (soundness C I rho) as F.
    exfalso. apply F. intros ??. apply axioms.
    now constructor.
    apply H.
  Qed.


  Lemma delta0_absolutness rho : 
    sat interp_nat rho phi -> PA⊨ phi.
  Proof.
    intros H. apply tsoundness.
    destruct dec_closed_delta0 as [C|C]. assumption.
    specialize (tsoundness C interp_nat rho) as F.
    exfalso. apply F. apply PA_std_axioms. apply H.
  Abort.


  Lemma delta0_absolutness' rho : 
    sat I rho phi -> PA⊨ phi.
  Proof.
    intros H. apply tsoundness.
    destruct dec_closed_delta0 as [C|C]. assumption.
    specialize (tsoundness C I rho) as F.
    exfalso. apply F. intuition. apply H.
  Qed.

End Closed.


Notation "N⊨ phi" := (forall rho, @sat _ _ nat interp_nat _ rho phi) (at level 40).

Section Sigma1.

  Variable α : form.
  Variable binary_α : binary α.
  Variable delta0_α : delta0 α.

  Lemma Σ1_complete' n :
    N⊨ (∃ α)[(num n)..] -> exists m, Q ⊢I α[up (num n)..][(num m)..].
  Proof.
    intros [m Hm]%(fun h => h (fun _ => 0)).
    rewrite <-switch_nat_num in Hm. exists m.
    eapply Q_delta0_complete; eauto.
    - eapply subst_bound; eauto.
      eapply subst_bound; eauto.
      intros [|[]]; solve_bounds; cbn.
      rewrite num_subst.
      apply closed_num.
      intros [|]; solve_bounds; cbn.
      apply closed_num.
    - now repeat apply subst_delta0.
  Qed.

  Lemma Σ1_complete n :
    N⊨ (∃ α)[(num n)..] -> Q ⊢I (∃ α)[(num n)..].
  Proof.
    intros [m Hm]%Σ1_complete'.
    cbn -[Q].
    change (∃ α[up (num n)..]) with (Peano.exist_times 1 (α[up (num n)..])).
    eapply subst_exist_prv; eauto.
    eapply subst_bound; eauto.
    intros [|[]]; solve_bounds. cbn.
    rewrite num_subst.
    apply closed_num.
  Qed.

  Lemma Σ1_complete'' n :
    Q ⊢I (∃ α)[(num n)..] -> exists m, Q ⊢I α[up (num n)..][(num m)..].
  Proof.
    intros H%soundness.
    apply Σ1_complete'.
    specialize (H nat interp_nat).
    intros ?. apply H.
    intros ??. now apply Q_std_axioms.
  Qed.

End Sigma1.


Section Sigma1.

  Variable α : form.
  Variable ternary_α : bounded 3 α.
  Variable delta0_α : delta0 α.

  Lemma Σ1_ternary_complete' n :
    N⊨ (∃∃α)[(num n)..] -> exists a b, Q ⊢I α[up (up (num n)..)][(num b)..][(num a)..].
  Proof.
    intros [a [b Hab]]%(fun h => h (fun _ => 0)).
    rewrite <-!switch_nat_num in Hab. exists a, b.
    eapply Q_delta0_complete; eauto.
    - eapply subst_bound with (N:=1); eauto.
      eapply subst_bound with (N:=2); eauto.
      eapply subst_bound with (N:=3); eauto.
      intros [|[|[]]]; solve_bounds; cbn.
      rewrite !num_subst. apply closed_num.
      intros [|[]]; solve_bounds; cbn.
      apply closed_num.
      intros [|]; solve_bounds; cbn.
      apply closed_num.
    - now repeat apply subst_delta0.
  Qed.

  Lemma Σ1_ternary_complete n :
    N⊨ (∃∃α)[(num n)..] -> Q ⊢I (∃∃α)[(num n)..].
  Proof.
    intros (a & b & Hab)%Σ1_ternary_complete'.
    cbn -[Q].
    change (∃∃ α[up (up (num n)..)]) with (Peano.exist_times 2 (α[up (up (num n)..)])).
    rewrite subst_comp in Hab.
    eapply subst_exist_prv; eauto. 
    eapply subst_bound; eauto.
    intros [|[|[]]]; solve_bounds. cbn.
    rewrite !num_subst.
    apply closed_num.
  Qed.

End Sigma1.