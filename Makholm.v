Require Import FOL Tarski Deduction Peano Formulas NumberTheory Synthetic DecidabilityFacts Church Coding.
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


  Variable ψ : form.
  Variable Hψ : binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (Irred x) ).

  Definition obj_Coding := forall α, binary α -> delta0 α -> PA ⊢TI ∀∀∃∀ $0 ⧀ $3 --> (∃ $0 ⧀ $3 ∧ α) <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3). 

  Hypothesis coding : obj_Coding.


  Definition obj_Insep := 
    exists α β,
      binary α /\ inhabited(delta0 α) /\ binary β /\ inhabited(delta0 β) /\ 
      ( PA ⊢TI ¬ ∃ (∃ α) ∧ (∃ β) ) /\ 
      (forall G,
          Dec G -> (forall n, Q ⊢I (∃ α)[(num n)..] -> G n) ->
          (forall n, ~ (Q ⊢I (∃ β)[(num n)..] /\ G n)) -> False).

  Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
  Definition Div_nat (d : D) := fun n => div_num n d.

  Theorem Makholm :
    obj_Insep -> nonStd D -> exists d, ~ Dec (Div_nat d).
  Proof.
    intros (α & β & Ha1 & [Ha0] & Hb1 & [Hb0] & Disj & Insepa).
    intros [e Nstd_e].
    specialize (coding α Ha1 Ha0).
    pose (X n := (inu n .: (fun _ => e)) ⊨ ((∃ $0 ⧀ $3 ∧ α) )).
    eapply tsoundness with (rho := (fun _ => e)) in coding.
    - cbn in coding.
      specialize (coding e e) as [c Hc].
      assert (forall n : nat, (X n) <-> (inu n .: (fun _ => c)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)) ).
      + intros n. split.
        -- specialize (Hc (inu n)) as [H _]. 
          now apply num_lt_nonStd.
          intros X_n. destruct H as [d Hd].
          ++ destruct X_n as [a Ha].
            exists a. split. apply Ha.
            eapply bound_ext. eauto.
            2 : apply Ha.
            intros [|[]]; solve_bounds.
          ++ exists d. cbn. split.
            eapply bound_ext. apply Hψ.
            2 : apply Hd.
            intros [|[]]; solve_bounds.
            apply Hd. 
        -- specialize (Hc (inu n)) as [_ H]. 
           now apply num_lt_nonStd.
           intros H_n. destruct H as [d Hd].
           ++ destruct H_n as [a Ha].
              exists a. split.
              eapply bound_ext. apply Hψ.
              2 : apply Ha.
              intros [|[]]; solve_bounds.
              apply Ha.
           ++ exists d. cbn. split. apply Hd.
              eapply bound_ext. eauto.
              2 : apply Hd.
              intros [|[]]; solve_bounds.
      + exists c. intros [Dec_Div_c].
        apply (Insepa X).
        -- constructor. intros n.
           destruct (Dec_Div_c (Irred n)) as [h|h]; auto.
           ++ left. apply H, ψ_equiv; auto.
           ++ right. intros nh%H. apply h.
              apply ψ_equiv in nh; auto.
        --  intros n [m Hm]%Σ1_complete''; auto. 
            exists (inu m). cbn. split.
            now apply num_lt_nonStd.
            rewrite <-switch_up_num, <-switch_num.
            eapply soundness; eauto.
            intros ??; apply axioms. now constructor.
        --  intros n [[m Bnm]%Σ1_complete'' X_n]; auto.
            eapply tsoundness with (rho := (fun _ => e)) in Disj; auto.
            cbn in Disj. apply Disj.
            exists (inu n). split.
            ++  specialize X_n as [d [_ Hd]]; cbn in Hd.
                rewrite <-switch_up_num in Hd.
                exists d. rewrite <-switch_up_num. apply Hd.
            ++  apply soundness in Bnm.
                specialize (Bnm D I). exists (inu m).
                rewrite <-switch_up_num, <-switch_num. apply Bnm.
                intros ??. apply axioms. now constructor. 
    - intros ??. now apply axioms.
  Qed.


End Model.