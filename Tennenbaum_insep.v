Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic Formulas DecidabilityFacts Church Coding.
Require Import Lia.
Require Import Equations.Equations Equations.Prop.DepElim.

Import Vector.VectorNotations.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).


Section Model.

  Variable D : Type.
  Variable I : interp D.
  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  Variable axioms : forall ax, PA ax -> ⊨ ax.

  Notation "N⊨ phi" := (forall rho, @sat _ _ nat interp_nat _ rho phi) (at level 40).
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  (* We also assume the existence of a formula which represents the prime number function *)
  Variable ψ : form.
  Variable Hψ : binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (Irred x) ).


  Definition div e d := exists k : D, e i⊗ k = d.
  Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
  Definition Div_nat (d : D) := fun n => div_num n d.
  Definition div_pi n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).


  Definition Insep :=
    exists α β, 
      binary α /\ inhabited(delta0 α) /\ binary β /\ inhabited(delta0 β) /\ 
      (forall n, ~ Q ⊢I ((∃α) ∧ (∃β))[(num n)..] ) /\ 
      (forall G, Dec G -> (forall n, Q ⊢I (∃α)[(num n)..] -> G n) -> 
        (forall n, ~ (Q ⊢I (∃β)[(num n)..] /\ G n)) -> False).


  Lemma nonDecDiv :
    Insep -> Stable std -> nonStd D -> ~ ~ exists d : D, ~ Dec (fun n => div_pi n d).
  Proof.
    intros (α & β & Ha1 & [Ha0] & Hb1 & [Hb0] & Disj & Insepa) Stab [d Hd].
    pose (phi := (∀ $0 ⧀ $1 --> ∀ $0 ⧀ $2 --> ∀ $0 ⧀ $3 --> ¬ (α[$1..] ∧ β[$2..]) ) ).
    enough (forall n rho, ((inu n).:rho) ⊨ phi ) as H.
    eapply Overspill_DN in H; eauto.
    - refine (DN_chaining (Coding_nonstd_binary_Definite _ _ _ _ _ _ _ (∃ $0 ⧀ $2 ∧ α) _ _) _); eauto.
      {apply nonStd_notStd. now exists d. }
      { repeat solve_bounds.
        eapply bounded_up; eauto; lia. }
      { intros b u.
        specialize (LEM_bounded_exist _ _ axioms ψ Hψ (fun _ => i0) Ha0 Ha1 b (inu u)) as [h|h].
        - left. intros ?. eapply bound_ext with (N := 2).
          3 : apply h.
          repeat solve_bounds. eapply bounded_up; eauto.
          intros [|[]]; try reflexivity; lia.
        - right. intros nh. apply h.
          eapply bound_ext with (N := 2).
          3 : apply nh.
          repeat solve_bounds. eapply bounded_up; eauto.
          intros [|[]]; try reflexivity; lia.
      }
      apply (DN_chaining H).
      apply DN. clear H.
      intros [e [? He]] [c Hc]%(fun h => h e).
      exists c. intros Dec_div_c.
      eapply (Insepa _ Dec_div_c).
      + intros n A_n. unfold Div_nat.
        specialize (Hc n (fun _ => e)) as [Hc _].
        cbn in Hc. destruct Hc as [ d' [H1 H2] ].
        * assert (N⊨ (∃α)[(num n)..]) as A_n'.
          { intros rho. eapply soundness.
            - apply A_n.
            - apply Q_std_axioms.
          }
          apply Σ1_complete' in A_n'; auto.
          destruct A_n' as [m Hm].
          exists (inu m). split; [apply num_lt_nonStd; auto|].
          rewrite <-!switch_num.
          apply soundness in Hm.
          rewrite !switch_num, <-switch_up_num, <-switch_num.
          apply Hm.
          intros ??. apply axioms. now constructor.
        * exists d'. split.
          eapply bound_ext. apply Hψ. 2: apply H1.
          intros [|[]]; try reflexivity; try lia.
          cbn. apply H2.
      + intros n [B_n C_n].
        assert (N⊨ (∃β)[(num n)..]) as B_n'.
        { intros rho. eapply soundness. 
          - apply B_n.
          - apply Q_std_axioms.
        }
        apply Σ1_complete' in B_n'; auto.
        destruct B_n' as [m Hm].
        apply soundness in Hm.
        assert ( (e .: (fun _ => e)) ⊨ (∃ $0 ⧀ $1 ∧ β[up (num n)..] )) as Heβ.
        cbn. exists (inu m). split.
        now apply num_lt_nonStd. 
        rewrite <-switch_num. apply Hm.
        intros ??; apply axioms; now constructor.
        cbn in Hc. 
        specialize (Hc n (fun _ => e)) as [_ Hc].
        destruct Hc as [d1 Hd1].
        * destruct C_n as [d' Hd']. exists d'. split.
          eapply bound_ext. apply Hψ. 2 : apply Hd'.
          intros [|[]]; solve_bounds.
          apply Hd'.
        * cbn in Heβ. destruct Heβ as [d2 Hd2].
          rewrite switch_up_num in Hd2.
          eapply He.
          apply Hd2.
          apply Hd1.
          cbn. apply num_lt_nonStd; eauto.
          fold sat.
          rewrite !sat_comp. split; eapply bound_ext.
          1, 4 : eauto.
          2 : apply Hd1.
          3 : apply Hd2.
          all: intros [|[]]; solve_bounds.
          Unshelve. exact (fun _ => i0).
    - repeat solve_bounds.
      eapply subst_bound; eauto. 
      intros [|[|[|[]]]]; solve_bounds.
      eapply subst_bound; eauto.
      intros [|[|[|[]]]]; solve_bounds.
    - apply nonStd_notStd. now exists d.  
    - intros n rho. cbn.
      intros d2 H2 d1 H1 d0 H0 [Ha Hb].
      apply lessthen_num in H2.
      apply lessthen_num in H1.
      apply lessthen_num in H0.
      destruct H2 as (k2 & H2 & ->).
      destruct H1 as (k1 & H1 & ->).
      destruct H0 as (k0 & H0 & ->).
      apply (Disj k0).
      change (Q ⊢I ((∃ α)[(num k0)..] ∧ (∃ β)[(num k0)..])).
      apply CI.
      + apply Σ1_complete; auto.
        intros sigma. rewrite sat_comp in Ha.
        eapply bound_ext with (rho0 := (inu k1 .: inu k0 .: inu k2 .: inu n .: rho)) in Ha.
        rewrite <-switch_up_num, <-switch_num in Ha.
        exists k1. rewrite <-switch_nat_num.
        repeat eapply subst_bound; eauto. 
        eapply delta0_absolutness' with (rho0 := sigma) in Ha.
        apply Ha.
        admit.
        repeat apply subst_delta0; auto.
        apply axioms.
        apply PA_std_axioms.
        apply Ha1.
        intros [|[]]; solve_bounds.
      + apply Σ1_complete; auto.
        intros sigma. rewrite sat_comp in Ha.
        rewrite sat_comp in Hb.
        eapply bound_ext with (rho0 := (inu k2 .: inu k0 .: inu k1 .: inu n .: rho)) in Hb.
        rewrite <-switch_up_num, <-switch_num in Hb.
        exists k2. rewrite <-switch_nat_num.
        eapply delta0_absolutness' with (rho0 := sigma) in Hb.
        apply Hb.
        admit.
        repeat apply subst_delta0; auto.
        apply axioms.
        apply PA_std_axioms.
        apply Hb1.
        intros [|[]]; solve_bounds.
      + apply axioms.
      + apply axioms.
      + apply axioms.
  Admitted.



End Model.