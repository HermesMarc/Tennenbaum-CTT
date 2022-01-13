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
  (* | Delta_lt : forall t s,  delta0 (t ⧀ s) *)
  | Delta_Conj : forall α β b,  delta0 α -> delta0 β ->  delta0 (bin b α β).

  Inductive Delta0 : form -> Type :=
  | Delta_id : forall α, delta0 α ->  Delta0 α
  | Delta_bounded_exist : forall α t,  Delta0 α -> Delta0 (∃ $0 ⧀ t`[↑] ∧ α)
  | Delta_bounded_forall : forall α t,  Delta0 α -> Delta0 (∀ $0 ⧀ t`[↑] --> α).


  Inductive sigma1 : form -> Type :=
  | Sigma_Delta : forall α, delta0 α -> sigma1 α
  | Sigma_exists : forall α, sigma1 α -> sigma1 (∃ α).


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


  Lemma inversion_delta0_lt α : 
    delta0 (∃ α) -> { s &{ t & α = t`[↑] == σ (s`[↑] ⊕ $0) }}.
  Proof.
    intros H. invert_delta.
  Qed.

  Lemma inversion_delta0_forall α : 
    Delta0 (∀ α) ->  { '(ϕ, t) & (Delta0 ϕ * (α = $0 ⧀ t`[↑] --> ϕ))%type}.
  Proof.
    intros H. 
    inversion H; subst.
    + inversion X.
    + apply Eqdep_dec.inj_pair2_eq_dec in H1; try decide equality.
      exists (α0, t). split; auto.
  Qed.

  Lemma inversion_delta0_exists α : Delta0 (∃ α) -> {ϕ & (Delta0 ϕ * (α = $0 ⧀ $1 ∧ ϕ))%type}.
  Proof.
    intros H. inversion H; subst.
  Admitted.


  (* Formulas stay at their level of the hierarchy under substitions. *)
  
  Fact subst_delta0 {ff : falsity_flag} phi sigma : 
    delta0 phi -> delta0 phi[sigma].
  Proof.
    induction 1; now constructor.
  Qed.

  Fact subst_sigma1 {ff : falsity_flag} phi sigma : 
    sigma1 phi -> sigma1 phi[sigma].
  Proof.
    intros S. revert sigma. induction S; intros sigma.
    - now apply Sigma_Delta, subst_delta0.
    - now apply Sigma_exists.
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
      admit.
      admit.
  Admitted.


  Lemma subst_bound' N phi sigma B :
    bounded N phi -> (forall n, n < N -> bounded_t B (sigma n) ) -> bounded B phi[sigma].
  Proof.
    intros H. revert sigma B. induction H.
    all: intros sigma B HB.
    - constructor. intros t Ht. depelim Ht.
    - constructor. 
      + eapply IHbounded1; eauto.
      + eapply IHbounded2; eauto.
    - constructor. all: admit.
    - constructor; fold subst_form. 
      apply IHbounded. intros x.
      assert (x < S n <-> x < n \/ x = n) as -> by lia.
      intros [Hx| ->].
      + destruct x.
        * constructor. lia.
        * admit.
      + 
  Admitted.



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

Section Closed.
  


  Lemma TEMP_NAME_2 k: 
    forall N x, bounded_t (k + N) (iter (subst_term ↑) k (var x)) ->  bounded_t N (var x).
  Proof.
    induction k.
    - auto.
    - intros N x.
      assert (S k + N = k + S N) as -> by lia.
      cbn. rewrite iter_switch.
      intros ?%IHk. inversion H0. constructor. lia.
  Qed.

  Lemma TEMP_NAME_3 t : 
    forall N k, bounded_t (k + N) (iter (subst_term ↑) k t) ->  bounded_t N t.
  Proof.
    induction t.
    - intros ??. apply TEMP_NAME_2.
    - intros N k H. constructor.
      intros t Ht. eapply IH; auto.
  Admitted.


  Lemma How α t : 
    bounded 0 (∃ $0 ⧀ t`[↑] ∧ α) -> bounded 1 α * {n & Q ⊢I t == num n}.
  Proof.
    intros H. split.
    - do 2 invert_bounds; assumption.
    - apply closed_term_is_num; [now intros ?|]. 
      do 2 invert_bounds. clear H6. 
      do 2 invert_bounds. clear H5. 
      now apply (TEMP_NAME_3 _ _ 2).
  Qed.

  Lemma Q_lt_equiv n : 
    Q ⊢I ∀ $0 ⧀ num (S n) <--> $0 ⧀ num n ∨ $0 == num n.
  Proof.
  Admitted.

  Lemma prv_DeMorgan {p : peirce} Γ α β : 
    Γ ⊢ (¬ α) ∧ (¬ β) --> ¬ (α ∨ β).
  Proof.
    apply II, II. eapply DE.
    - apply Ctx. now left.
    - eapply IE. 2: apply Ctx; now left.
      eapply CE1, Ctx; cbn; auto.
    - eapply IE. 2: apply Ctx; now left.
      eapply CE2, Ctx; cbn; auto.
  Qed.
  
  Lemma TEMP_NAME n α : 
    (forall x, x < n -> ~ Q ⊢I α[(num x)..]) -> Q ⊢I ¬ (∃ $0 ⧀ num n ∧ α).
  Proof.
    induction n; intros H.
    - apply II. admit.
    - 
  Admitted.

  Lemma dec_bounded_exists α t : 
    delta0 α -> bounded 0 (∃ $0 ⧀ t`[↑] ∧ α) -> Q_dec (∃ $0 ⧀ t`[↑] ∧ α).
  Proof.
    intros delta_α ( b1 & [n ] )%How.
    refine (let D := dec_lt_bounded_sig n (fun n => Q ⊢I α[(num n)..]) _ in _).
    destruct D as [[x Hx]|h].
    - left. apply ExI with (t0 := num x). 
      cbn -[Q]; apply CI.
      + admit.
      + apply Hx.
    - right. apply TEMP_NAME in h. 
      
  Admitted.



  Lemma How2 α n : 
    bounded 0 (∃ $0 ⧀ num n ∧ α) -> bounded 1 α.
  Proof.
    intros H. do 2 invert_bounds; assumption.
  Qed.

  Lemma Q_dec_bounded_exists α n : 
    (forall x, Q_dec α[(num x)..]) -> bounded 0 (∃ $0 ⧀ num n ∧ α) -> Q_dec (∃ $0 ⧀ num n ∧ α).
  Proof.
    intros Dec_α b1%How2.
    induction n as [| n [h|h]].
    - right. apply II. eapply ExE.
      {apply Ctx; now left. }
      cbn -[Q]. eapply IE.
      {eapply Weak with (A:=Q). (* apply not_lt_zero_prv. *) }
      admit.
    - left. admit.
    - destruct (Dec_α n).
      { left. eapply ExI with (t:=num n); cbn -[Q].
        rewrite !num_subst. apply CI; auto.
        eapply ExI with (t:=num 0); cbn -[Q num].
        rewrite !num_subst.
        apply eq_succ, symmetry; try now intros ?.
        rewrite plus_n_O at 2.
        apply num_add_homomorphism.
        now intros ?. 
      }
      { right. apply II.
        eapply ExE; cbn - [Q].
        { apply Ctx. now left. }
        (* $0 is now a number for which we have $0 ⧀ S n  *)
        pose (ϕ := $0 ⧀ num n ∨ $0 == num n).
        apply IE with (phi:= ϕ).
        { apply II. eapply DE.
          * apply Ctx; now left.
          * eapply IE.
            { eapply Weak; [apply h|].
              do 4 right. now cbn. }
            eapply ExI with (t:= $0).
            cbn -[Q]; apply CI.
            { rewrite !num_subst in *. apply Ctx; now left. }
            { (* since α is bounded by 1, α[$0..] = α 
                 which we can prove, as α is part of the second statement in the context. *) admit. }
        }
        { (* this must follow from an external lemma *) admit. }
      }
  Admitted.
    

  
  Theorem Q_dec_closed_Delta0 : 
    forall α (H : Delta0 α), bounded 0 α -> Q_dec α.
  Proof. 
    change (forall α (H : Delta0 α), (fun h a => bounded 0 a -> Q_dec a) H α).
    apply Delta0_rect; intros α delta_α H.
    - admit. (* Just need to move this lemma out of the section *)
    - intros B.
  Abort.


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
    eapply subst_exist_prv with (sigma := (num m)..); auto.
    + eapply subst_bound; eauto.
      intros [|[]]; solve_bounds. cbn.
      rewrite num_subst.
      apply closed_num.
  Qed.

End Sigma1.



Lemma sigma1_complete {ϕ} :
  sigma1 ϕ -> 
  forall N s, bounded N ϕ -> 
  (forall n, n < N -> bounded_t 0 (s n) ) -> 
  forall rho, @sat _ _ _ interp_nat _ rho ϕ[s] -> 
  Q ⊢I ϕ[s].
Proof.
  induction 1; intros N s HN Hs rho Hrho.
  - eapply Q_delta0_complete'.
    4: apply Hrho.
    + eapply subst_bound; eauto.
    + now apply subst_delta0.
    + intros ???. now apply PA_std_axioms.
  - cbn -[Q]. destruct Hrho as [n Hn].
    eapply ExI with (t:= num n).
    rewrite subst_comp.
    eapply IHX.
    + admit.
    + intros [|] ?; cbn. apply closed_num.
      admit.
    + rewrite <-subst_comp, switch_num, inu_nat_id.
      apply Hn.
Admitted.



Lemma sigma1_complete' N {ϕ} s :
  sigma1 ϕ -> 
  bounded N ϕ -> 
  (forall n, n < N -> bounded_t 0 (s n) ) -> 
  Q ⊢I (∃ ϕ)[s] -> 
  exists n, Q ⊢I ϕ[up s][(num n)..].
Proof.
  intros S1 HN Hs H%soundness.
  specialize (H _ interp_nat (fun _ => 0)) as [n Hn].
  { intros ??. now apply Q_std_axioms. }
  exists n. rewrite <-(inu_nat_id n), <-switch_num in Hn.
  rewrite subst_comp in Hn.
  eapply sigma1_complete in Hn. 
  - now rewrite subst_comp.
  - assumption.
  - apply HN.
  - intros [] ?; cbn. 
    + apply closed_num.
    + unfold ">>". repeat rewrite subst_closed_term.
      all: apply Hs; lia.  
Qed.
