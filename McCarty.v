Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic DecidabilityFacts.
Require Import Lia.
Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Formulas Synthetic DecidabilityFacts Coding.
Require Import Lia.


Section Model.

  Variable D : Type.
  Variable I : interp D.
  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  Variable axioms : forall ax, PA ax -> ⊨ ax.

  Notation "N⊨ phi" := (forall rho, @sat _ _ nat interp_nat _ rho phi) (at level 40).
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  Lemma bounded_definite_unary'' ϕ :
    bounded 1 ϕ -> forall x, ~ ~ forall y, y i⧀ x -> (fun _ => y) ⊨ ϕ \/ ~ (fun _ => y) ⊨ ϕ.
  Proof.
    intros H1.
    pose (Φ := ¬¬ ∀ $0 ⧀ $1 --> ϕ ∨ ¬ ϕ).
    assert (forall d rho, (d .: rho) ⊨ Φ) as H.
    apply induction.
    - apply axioms.
    - repeat solve_bounds; eapply bounded_up; try apply H1; try lia.
    - intros rho. cbn. apply DN.
      now intros y Hy%nolessthen_zero.
    - intros x IHx rho. cbn -[Q] in *.
      specialize (IHx rho).
      assert (~~ ((x .: rho) ⊨ ϕ \/ ~ (x .: rho) ⊨ ϕ) ) as H' by tauto.
      apply (DN_chaining IHx), (DN_chaining H'), DN.
      intros H IH y.
      rewrite lt_S; auto.
      intros [LT| <-].
      + destruct (IH _ LT) as [h|h].
        * left. eapply bound_ext. apply H1. 2 : apply h.
          intros []; solve_bounds.
        * right. intros h1. apply h. 
          eapply bound_ext. apply H1. 2 : apply h1.
          intros []; solve_bounds.
      + destruct H as [h|h]. 
        * left. eapply bound_ext. apply H1. 2 : apply h.
          intros []; solve_bounds.
        * right. intros h1. apply h. 
          eapply bound_ext. apply H1. 2 : apply h1.
          intros []; solve_bounds.
    - intros x.
      specialize (H x (fun _ => i0)). cbn in H.
      apply (DN_chaining H), DN. clear H; intros H.
      intros y Hy. destruct (H _ Hy) as [h|h].
      + left. eapply bound_ext. apply H1. 2: apply h.
        intros []; solve_bounds.
      + right. intros G. apply h. 
        eapply bound_ext. apply H1. 2: apply G.
        intros []; solve_bounds.
  Abort.


  Lemma bounded_definite_unary' ϕ rho :
    bounded 2 ϕ -> forall x b, ~ ~ forall y, y i⧀ x -> (y .: b .: rho) ⊨ ϕ \/ ~ (y .: b .: rho) ⊨ ϕ.
  Proof.
    intros b2.
    pose (Φ := ∀ ¬¬ ∀ $0 ⧀ $2 --> ϕ ∨ ¬ ϕ).
    assert (forall d rho, (d .: rho) ⊨ Φ) as H.
    apply induction.
    - apply axioms.
    - repeat solve_bounds; eapply bounded_up; try apply b2; try lia.
    - intros sigma b. cbn. apply DN.
      now intros y Hy%nolessthen_zero.
    - intros x IHx. cbn -[Q] in *.
      intros sigma b. specialize (IHx sigma b).
      assert (~~ ((x .: b .: b .: sigma) ⊨ ϕ \/ ~ (x .: b .: b .: sigma) ⊨ ϕ) ) as H' by tauto.
      apply (DN_chaining IHx), (DN_chaining H'), DN.
      intros H IH y.
      rewrite lt_S; auto.
      intros [LT| <-].
      + destruct (IH _ LT) as [h|h].
        * left. eapply bound_ext. apply b2. 2 : apply h.
          intros [|[]]; solve_bounds.
        * right. intros h1. apply h. 
          eapply bound_ext. apply b2. 2 : apply h1.
          intros [|[]]; solve_bounds.
      + destruct H as [h|h]. 
        * left. eapply bound_ext. apply b2. 2 : apply h.
          intros [|[]]; solve_bounds.
        * right. intros h1. apply h. 
          eapply bound_ext. apply b2. 2 : apply h1.
          intros [|[]]; solve_bounds.
    - intros x b.
      specialize (H x (fun _ => i0)). cbn in H.
      specialize (H b).
      apply (DN_chaining H), DN. clear H; intros H.
      intros y Hy. destruct (H _ Hy) as [h|h].
      + left. eapply bound_ext. apply b2. 2: apply h.
        intros [|[]]; solve_bounds.
      + right. intros G. apply h. 
        eapply bound_ext. apply b2. 2: apply G.
        intros [|[]]; solve_bounds.
  Qed.

  Corollary bounded_definite_unary ϕ b rho x :
    bounded 2 ϕ -> ~ ~ forall y, y i⧀ x -> (y .: b .: rho) ⊨ ϕ \/ ~ (y .: b .: rho) ⊨ ϕ.
  Proof.
    intros b2; now apply bounded_definite_unary'.
  Qed.

  Lemma bounded_definite_binary ϕ :
    bounded 2 ϕ -> forall x, ~ ~ forall y z, y i⧀ x -> z i⧀ x -> (z .: fun _ => y) ⊨ ϕ \/ ~ (z .: fun _ => y) ⊨ ϕ.
  Proof.
    intros b2.
    pose (Φ := ¬¬ ∀∀ $0 ⧀ $2 --> $1 ⧀ $2 --> ϕ ∨ ¬ ϕ).
    assert (forall d rho, (d .: rho) ⊨ Φ) as H.
    apply induction. apply axioms.
    repeat solve_bounds; eapply bounded_up; try apply b2; try lia.
    - intros rho. cbn. intros nH. apply nH.
      now intros y z Hy%nolessthen_zero.
    - intros b IH rho. cbn -[Q] in *.
      specialize (IH rho). 
      assert (~~ ((b .: b .: rho) ⊨ ϕ \/ ~ (b .: b .: rho) ⊨ ϕ) ) as Hbb by tauto.
      apply (DN_chaining IH), (DN_chaining Hbb).
      apply (DN_chaining (bounded_definite_unary _ b rho b b2)).
      refine (DN_chaining (bounded_definite_unary (ϕ[$1 ..] ) b rho b _) _).
      { eapply subst_bound; eauto. 
        intros [|[]]; solve_bounds. }
      apply DN. clear IH Hbb.
      intros H1 H2 Hbb IH x y.
      rewrite !lt_S; try apply axioms.
      intros [lty| <-] [ltx| <-].
      + destruct (IH _ _ lty ltx) as [h|h].
        * left. eapply bound_ext. apply b2. 2 : apply h.
          intros [|[]]; solve_bounds.
        * right. intros h1. apply h. 
          eapply bound_ext. apply b2. 2 : apply h1.
          intros [|[]]; solve_bounds.
      + destruct (H2 _ lty) as [h|h].
        * left. eapply bound_ext. apply b2. 2 : apply h.
          intros [|[]]; solve_bounds.
        * right. intros h1. apply h. 
          eapply bound_ext. apply b2. 2 : apply h1.
          intros [|[]]; solve_bounds.
      + destruct (H1 _ ltx) as [h|h]; rewrite sat_comp in h.
        * left. eapply bound_ext. apply b2. 2 : apply h.
          intros [|[]]; solve_bounds.
        * right. intros h1. apply h.
          eapply bound_ext. apply b2. 2 : apply h1.
          intros [|[]]; solve_bounds.
      + destruct Hbb as [h|h].
        * left. eapply bound_ext. apply b2. 2 : apply h.
          intros [|[]]; solve_bounds.
        * right. intros h1. apply h.
        eapply bound_ext. apply b2. 2 : apply h1.
        intros [|[]]; solve_bounds.
      - intros x.
        specialize (H x (fun _ => i0)). cbn in H.
        apply (DN_chaining H), DN. clear H; intros H.
        intros y z Hy Hz. destruct (H _ _ Hz Hy) as [h|h].
        + left. eapply bound_ext. apply b2. 2: apply h.
          intros [|[]]; solve_bounds.
        + right. intros h1. apply h. 
          eapply bound_ext. apply b2. 2: apply h1.
          intros [|[]]; solve_bounds.
  Qed.


  Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
  Definition Div_nat (d : D) := fun n => div_num n d.

  Lemma DN_Div_nat :
    UC nat bool -> nonStd D -> forall d, ~~Dec (Div_nat d).
  Proof.
    intros uc [e He] d.
    refine (DN_chaining _ _).
    2 : { now apply DN, UC_Def_Dec. }
    refine (DN_chaining (bounded_definite_binary (∃ $1 ⊗ $0 == $2) _ (iσ (d i⊕ e))) _).
    { repeat solve_bounds. }
    apply DN. intros H n.
    destruct (H d (inu n)) as [h|h].
    - now exists e.
    - apply num_lt_nonStd; auto.
      rewrite <-add_rec; auto.
      intros h%std_add; auto. 
      now apply He.
    - left. apply h.
    - right. apply h.
  Qed.

End Model.