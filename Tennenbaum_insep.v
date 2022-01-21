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
      bounded 3 α /\ inhabited(delta0 α) /\ bounded 3 β /\ inhabited(delta0 β) /\ 
      (forall n, ~ Q ⊢I ((∃∃α) ∧ (∃∃β))[(num n)..] ) /\ 
      (forall G, Dec G -> (forall n, Q ⊢I (∃∃α)[(num n)..] -> G n) -> 
        (forall n, ~ (Q ⊢I (∃∃β)[(num n)..] /\ G n)) -> False).

(* 
  Compute ($0 == $1 ∨ $1 == $2)[$3..][$1..].
  Compute ($0 == $1 ∨ $1 == $2)[$5..][$3..].
 *)

  Lemma LEM_bounded_exist_ternary {phi} sigma : 
    delta0 phi -> bounded 3 phi -> forall b x, (x .: b .: sigma) ⊨ (∃∃ $0 ⧀ $3 ∧ $1 ⧀ $3 ∧ phi) \/ ~ (x .: b .: sigma) ⊨ (∃∃ $0 ⧀ $3 ∧ $1 ⧀ $3 ∧ phi).
  Proof.
  Admitted.

  Lemma nonDecDiv :
    Insep -> Stable std -> nonStd D -> ~ ~ exists d : D, ~ Dec (fun n => div_pi n d).
  Proof.
    intros (α & β & Ha1 & [Ha0] & Hb1 & [Hb0] & Disj & Insepa) Stab [d Hd].
    pose (phi := (∀ $0 ⧀ $1 --> ∀ $0 ⧀ $2 --> ∀ $0 ⧀ $3 --> ∀ $0 ⧀ $4 --> ∀ $0 ⧀ $5 --> ¬ (α[$3..][$1..] ∧ β[$5..][$3..]) ) ).
    enough (forall n rho, ((inu n).:rho) ⊨ phi ) as H.
    eapply Overspill_DN in H; eauto.
    - refine (DN_chaining (Coding_nonstd_binary_Definite _ _ _ _ _ _ _ (∃∃ $0 ⧀ $3 ∧ $1 ⧀ $3 ∧ α) _ _) _); eauto.
      {apply nonStd_notStd. now exists d. }
      { repeat solve_bounds.
        eapply bounded_up; eauto; lia. }
      { intros b u.
        specialize (LEM_bounded_exist_ternary (fun _ => i0) Ha0 Ha1 b (inu u)) as [h|h].
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
        * assert (N⊨ (∃∃α)[(num n)..]) as A_n'.
          { intros rho. eapply soundness.
            - apply A_n.
            - apply Q_std_axioms.
          }
          apply Σ1_ternary_complete' in A_n'; auto.
          destruct A_n' as (a & b & Hab).
          exists (inu a), (inu b). repeat split; [apply num_lt_nonStd; auto|apply num_lt_nonStd; auto| ].
          apply soundness in Hab.
          specialize (Hab D I (fun _ => i0)). rewrite !sat_comp in Hab.
          eapply bound_ext. apply Ha1. 2: apply Hab.
          intros [|[|[]]] ?; cbn; try now rewrite ?num_subst, ?eval_num; try lia.
          intros ??. apply axioms. now constructor.
        * exists d'. split.
          eapply bound_ext. apply Hψ. 2: apply H1.
          intros [|[]]; try reflexivity; try lia.
          cbn. apply H2.
      + intros n [B_n C_n].
        assert (N⊨ (∃∃β)[(num n)..]) as B_n'.
        { intros rho. eapply soundness. 
          - apply B_n.
          - apply Q_std_axioms.
        }
        apply Σ1_ternary_complete' in B_n'; auto.
        destruct B_n' as (a & b & Hab).
        apply soundness in Hab.
        assert ((fun _ => e) ⊨ (∃∃ $0 ⧀ $2 ∧ $1 ⧀ $2 ∧ β[up (up (num n)..)] )) as Heβ.
        { cbn. exists (inu a), (inu b). repeat split; [apply num_lt_nonStd; auto|apply num_lt_nonStd; auto| ].
          specialize (Hab D I (fun _ => i0)). rewrite !sat_comp in Hab.
          rewrite sat_comp.
          eapply bound_ext. apply Hb1. 2: apply Hab.
          intros [|[|[]]] ?; cbn; try now rewrite ?num_subst, ?eval_num; try lia.
          intros ??. apply axioms. now constructor. }
        specialize (Hc n (fun _ => e)) as [_ Hc].
        destruct Hc as (k1 & k2 & [Hk2 Hk1] & Hk12); fold sat in *.
        * destruct C_n as [d' Hd']. exists d'. split.
          eapply bound_ext. apply Hψ. 2 : apply Hd'.
          intros [|[]]; solve_bounds.
          apply Hd'.
        * cbn in Heβ, Hk12, Hk1, Hk2. destruct Heβ as (k3 & k4 & [Hk4 Hk3] & Hk34).
          rewrite sat_comp in Hk34.
          eapply He; fold sat; cbn.
          apply Hk4.
          apply Hk3.
          apply Hk2.
          apply Hk1.
          apply num_lt_nonStd with (n:=n); auto.
          rewrite !sat_comp.
          split.
          **  eapply bound_ext. 
              apply Ha1. 2: apply Hk12.
              intros [|[|[]]] ?; try reflexivity; try lia.
          **  eapply bound_ext. 
              apply Hb1. 2: apply Hk34.
              intros [|[|[]]] ?; cbn; try reflexivity; try lia.
              now rewrite !num_subst, eval_num. 
          Unshelve. exact (fun _ => i0).
    - repeat solve_bounds.
      eapply subst_bound with (N:=4).
      eapply subst_bound with (N:=4). eapply bounded_up; eauto. 
      intros [|[|[|[|[]]]]]; solve_bounds.
      intros [|[|[|[|[]]]]]; solve_bounds.
      eapply subst_bound with (N:=6).
      eapply subst_bound with (N:=6). eapply bounded_up; eauto. 
      intros [|[|[|[|[|[]]]]]]; solve_bounds.
      intros [|[|[|[|[|[]]]]]]; solve_bounds.
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
        * eapply subst_bound with (N:=1).
          eapply subst_bound with (N:=2); eauto.
          intros [|[]] ?; cbn; try rewrite num_subst; [solve_bounds | apply closed_num | lia].
          intros [|] ?; cbn; [apply closed_num |lia].
        * repeat apply subst_delta0; auto.
        * apply axioms.
        * apply PA_std_axioms.
        * apply Ha1.
        * intros [|[]]; solve_bounds.
      + apply Σ1_complete; auto.
        intros sigma. rewrite sat_comp in Ha.
        rewrite sat_comp in Hb.
        eapply bound_ext with (rho0 := (inu k2 .: inu k0 .: inu k1 .: inu n .: rho)) in Hb.
        rewrite <-switch_up_num, <-switch_num in Hb.
        exists k2. rewrite <-switch_nat_num.
        eapply delta0_absolutness' with (rho0 := sigma) in Hb.
        apply Hb.
        * eapply subst_bound with (N:=1).
          eapply subst_bound with (N:=2); eauto.
          intros [|[]] ?; cbn; try rewrite num_subst; [solve_bounds | apply closed_num | lia].
          intros [|] ?; cbn; [apply closed_num |lia].
        * repeat apply subst_delta0; auto.
        * apply axioms.
        * apply PA_std_axioms.
        * apply Hb1.
        * intros [|[]]; solve_bounds.
      + apply axioms.
      + apply axioms.
      + apply axioms.
  Qed.

End Model.