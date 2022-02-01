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
  Variable Hψ : bounded 2 ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (Irred x) ).


  Definition div e d := exists k : D, e i⊗ k = d.
  Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
  Definition Div_nat (d : D) := fun n => div_num n d.
  Definition div_pi n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).

  Variable surj_form_ : { Φ : nat -> form & surj Φ }.
  Variable enumerable_Q_prv : forall Φ : nat -> form, enumerable (fun n => Q ⊢I (Φ n)).
  
  Definition Φ := projT1 surj_form_.
  Definition surj_form := projT2 (surj_form_).
  Definition A n := Q ⊢I ¬(Φ n)[(num n)..].
  Definition B n := Q ⊢I (Φ n)[(num n)..].


  Lemma Disjoint_AB : forall n, ~(A n /\ B n).
  Proof.
    unfold A, B. intros n [A_n B_n].
    apply Q_consistent.
    eapply IE; eauto.
  Qed.

  Definition Insep' :=
    exists A B : nat -> Prop,
      enumerable A /\ enumerable B /\ 
      (forall n, ~ (A n /\ B n) ) /\ 
      (forall D, Dec D -> 
        (forall n, A n -> D n) ->
        (forall n, ~ (B n /\ D n)) -> False).

  Definition Insep :=
    exists α β,
      bounded 3 α /\ inhabited(delta0 α) /\ bounded 3 β /\ inhabited(delta0 β) /\ 
      (forall n, ~ Q ⊢I ((∃∃α) ∧ (∃∃β))[(num n)..] ) /\ 
      (forall G, Dec G -> (forall n, Q ⊢I (∃∃α)[(num n)..] -> G n) -> 
        (forall n, ~ (Q ⊢I (∃∃β)[(num n)..] /\ G n)) -> False).

  Lemma Insep_ :
    RT_strong -> Insep'.
  Proof.
    intros rt.
    exists A, B. repeat split; auto.
    1,2 : apply enumerable_Q_prv.
    { apply Disjoint_AB. }
    intros G Dec_G.
    destruct (rt G Dec_G) as [γ [? [? []]]],
      (surj_form (∃ γ)) as [c Hc].
    rewrite <-Hc in *.
    unfold A, B in *; fold Φ in *.
    intros ? ?%(fun h => h c).
    enough (~ G c); auto.
  Qed.

  Lemma CT_Inseparable : 
    CT_Q -> Insep.
  Proof.
    intros ct.
    destruct (Insep_ (CT_RTs ct)) as (A & B & HA & HB & disj & H).
    destruct ((CT_RTw ct) A HA) as [α (Ha0 & [Ha1] & Hα)],
            ((CT_RTw ct) B HB) as [β (Hb0 & [Hb1] & Hβ)].
    exists α, β. repeat split; auto; unfold weak_repr in *.
    - intros n h%soundness. apply (disj n).
      rewrite Hα, Hβ.
      split; apply Σ1_ternary_complete; auto.
      all: intros rho; specialize (h _ interp_nat rho);
            apply h; apply Q_std_axioms.
    - setoid_rewrite <-Hα.
      setoid_rewrite <-Hβ.
      apply H.
  Qed.  


  Lemma LEM_ternary phi : 
    delta0 phi -> bounded 3 phi -> ⊨ ∀∀∀ phi ∨ ¬ phi.
  Proof.
  Admitted.

  Lemma LEM_bounded_exist_Nary {phi} sigma N : 
    bounded N phi -> (forall rho, definite (rho ⊨ phi)) -> sigma ⊨ (∃ $0 ⧀ $N ∧ phi) \/ ~ sigma ⊨ (∃ $0 ⧀ $N ∧ phi).
  Proof.
  Admitted.


  Lemma LINE p : 
    (forall x y : nat, definite (p x y)) -> forall b y, definite (exists x, x < b /\ p x y).
  Proof.
    intros def b. induction b; intros y.
    - right. intros [? []]. admit.
    - destruct (IHb y) as [[x ]|h].
      + left; exists x. split; [lia| tauto].
      + destruct (def b y).
        * left. exists b. split; [lia| tauto].
        * right.
          assert (forall x y, x < S y <-> x = y \/ x < y) as L by lia.
          intros [x [[-> |]%L ?]].
          ** tauto.
          ** apply h. now exists x.
  Admitted.

  Lemma SQUARE p :
    (forall x1 x2 y : nat, definite (p x1 x2 y)) -> forall b y, definite (exists x1 x2, x1 < b /\ x2 < b /\ p x1 x2 y).
  Proof.
    intros Hp b y.
    enough (forall x1 y, definite (exists x2, x2 < b /\ p x1 x2 y)) as A.
    destruct (LINE _ A b y) as [[x1 [? [x2 ] ]]| nh].
    - left. exists x1, x2. repeat split; tauto.
    - right. intros h. apply nh.
      destruct h as (x1 & x2 & H).
      exists x1. split; [tauto|]. 
      exists x2; tauto.
    - intros x1 z. apply LINE. intros. apply Hp. 
  Qed.


  Lemma LEM_bounded_exist_ternary' phi : 
    (⊨ ∀∀∀ phi ∨ ¬ phi) -> bounded 3 phi -> ⊨ ∀∀∀ (∃ $0 ⧀ $3 ∧ phi) ∨ ¬ (∃ $0 ⧀ $3 ∧ phi).
  Proof.
  Admitted.


  (* LINE = LEM_bounded_exist_sat *)

  Lemma LEM_bounded_exist_ternary {phi} sigma : 
    delta0 phi -> bounded 3 phi -> forall b x, (x .: b .: sigma) ⊨ (∃∃ $0 ⧀ $3 ∧ $1 ⧀ $3 ∧ phi) \/ ~ (x .: b .: sigma) ⊨ (∃∃ $0 ⧀ $3 ∧ $1 ⧀ $3 ∧ phi).
  Proof.
    intros d0 b3 b y.
    unshelve refine (let D' := LEM_bounded_exist_ternary' (∃ $0 ⧀ $3 ∧ phi) _ _ in _); auto.
    - apply LEM_bounded_exist_ternary'; auto. 
      intros rho x1 x2 x3.
      specialize (d0 var).
      cbn. 
      admit.
    - repeat solve_bounds. eapply bounded_up; eauto.
    - specialize (D' sigma b b y); fold sat in *.
      destruct D' as [H|nH].
    + left. cbn in H. destruct H as [x1 [H1 [x2 [H2 H]]]].
      exists x1, x2. cbn. repeat split; try tauto.
      eapply bound_ext. 3 : apply H. eauto.
      intros [|[|[]]]; solve_bounds.
    + right; cbn. intros (x1 & x2 & H). apply nH; fold sat; cbn.
      exists x1. split; try tauto.
      exists x2. split; try tauto.
      eapply bound_ext. 3 : apply H. eauto.
      intros [|[|[]]]; solve_bounds.

    Restart.
    intros d0 b3 b y.
    unshelve refine (let D := LEM_bounded_exist_sat _ _ axioms ψ Hψ (∃ $0 ⧀ $3 ∧ phi) _ _ in _).
    - admit.
    - do 2 constructor; auto. admit.
    - specialize (D0 sigma b y); fold sat in *.
      destruct D0 as [H|nH].
      + left. cbn in H. destruct H as [x1 [H1 [x2 [H2 H]]]].
        exists x1, x2. cbn. repeat split; tauto.
      + right; cbn. intros (x1 & x2 & H). apply nH; fold sat; cbn.
        exists x1. split; [tauto|].
        exists x2; tauto.
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
      intros d4 H4 d3 H3 d2 H2 d1 H1 d0 H0 [H31 H53].
      apply lessthen_num in H4; auto.
      apply lessthen_num in H3; auto.
      apply lessthen_num in H2; auto.
      apply lessthen_num in H1; auto.
      apply lessthen_num in H0; auto.
      destruct H4 as (k4 & H4 & ->).
      destruct H3 as (k3 & H3 & ->).
      destruct H2 as (k2 & H2 & ->).
      destruct H1 as (k1 & H1 & ->).
      destruct H0 as (k0 & H0 & ->).
      apply (Disj k0).
      change (Q ⊢I ((∃∃ α)[(num k0)..] ∧ (∃∃ β)[(num k0)..])).
      apply CI.
      + apply Σ1_ternary_complete; auto.
        intros sigma. rewrite <-switch_num in H31.
        exists k1, k2.
        assert ((inu k1 .: inu k2 .: inu k3 .: inu k4 .: inu n .: rho) ⊨ α[up (up (num k0)..)][(num k2)..][(num k1)..]).
        eapply bound_ext with (N:=0).
        eapply subst_bound with (N:=1).
        eapply subst_bound with (N:=2).
        eapply subst_bound with (N:=3); auto.
        intros [|[|[|[]]]]; cbn; solve_bounds.
        rewrite ?num_subst. apply closed_num.
        intros [|[|[]]]; cbn; solve_bounds.
        apply closed_num.
        intros [|[]]; cbn; solve_bounds.
        apply closed_num.
        lia.
        rewrite !sat_comp. rewrite !sat_comp in H31.
        eapply bound_ext. apply Ha1. 2 : apply H31.
        intros [|[|[]]]; cbn; rewrite ?num_subst, ?eval_num; try reflexivity; try lia.
        eapply delta0_absolutness' in H.
        rewrite !switch_nat_num in H.
        apply H.
        * eapply subst_bound with (N:=1).
          eapply subst_bound with (N:=2).
          eapply subst_bound; eauto.
          intros[|[|[]]]; cbn; solve_bounds.
          rewrite !num_subst. apply closed_num.
          intros[|[]]; cbn; solve_bounds. apply closed_num.
          intros[]; cbn; solve_bounds. apply closed_num.
        * now repeat eapply subst_delta0.
        * apply axioms.
        * intros ??. now apply PA_std_axioms.
      + apply Σ1_ternary_complete; auto.
        intros sigma. rewrite <-switch_num in H53.
        exists k3, k4.
        assert ((inu k1 .: inu k2 .: inu k3 .: inu k4 .: inu n .: rho) ⊨ β[up (up (num k0)..)][(num k4)..][(num k3)..]).
        eapply bound_ext with (N:=0).
        eapply subst_bound with (N:=1).
        eapply subst_bound with (N:=2).
        eapply subst_bound with (N:=3); auto.
        intros [|[|[|[]]]]; cbn; solve_bounds.
        rewrite ?num_subst. apply closed_num.
        intros [|[|[]]]; cbn; solve_bounds.
        apply closed_num.
        intros [|[]]; cbn; solve_bounds.
        apply closed_num.
        lia.
        rewrite !sat_comp. rewrite !sat_comp in H53.
        eapply bound_ext. apply Hb1. 2 : apply H53.
        intros [|[|[]]]; cbn; rewrite ?num_subst, ?eval_num; try reflexivity; try lia.
        eapply delta0_absolutness' in H.
        rewrite !switch_nat_num in H.
        apply H.
        * eapply subst_bound with (N:=1).
          eapply subst_bound with (N:=2).
          eapply subst_bound; eauto.
          intros[|[|[]]]; cbn; solve_bounds.
          rewrite !num_subst. apply closed_num.
          intros[|[]]; cbn; solve_bounds. apply closed_num.
          intros[]; cbn; solve_bounds. apply closed_num.
        * now repeat eapply subst_delta0.
        * apply axioms.
        * intros ??. now apply PA_std_axioms.
    Unshelve. all: auto.
  Qed.

End Model.