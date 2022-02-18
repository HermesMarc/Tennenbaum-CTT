Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic DecidabilityFacts Formulas Coding Church.
Require Import Lia.
Require Import Equations.Equations Equations.Prop.DepElim.

Import Vector.VectorNotations.



Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.


Section Model.

  Context {Δ0 : Delta0}.

  Variable D : Type.
  Variable I : interp D.
  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  Variable axioms : forall ax, PA ax -> ⊨ ax.

  Notation "N⊨ phi" := (forall rho, @sat _ _ nat interp_nat _ rho phi) (at level 40).
  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).

  Variable ψ : form.
  Variable Hψ : binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (Irred x) ).


  Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
  Definition div_pi n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).

  (** * Enumerable and discrete PA models have decidable divisibility. *)

  Lemma dec_div :
    Enumerable D -> Discrete D -> Dec (fun '(n, d) => div_num n d).
  Proof.
    intros [G Hg] [eq]%Discrete_sum.
    pose (g n := match G n with None => i0 | Some d => d end).
    constructor. intros [n d].
    destruct (eq d i0) as [->|h].
    { left; exists i0. now rewrite mult_zero_r. }
    destruct n as [|n].
    { right; intros [k Hk]. rewrite mult_zero in Hk; auto. }
    refine (let H' := @iEuclid' D I axioms d (S n) _ in _).
    assert (exists q r, r < S n /\ d = (g q) i⊗ inu (S n) i⊕ inu r) as H.
    { destruct H' as [Q [r ]], (Hg Q) as [q Hq]. 
      exists q, r. unfold g. now rewrite Hq. 
    } clear H'.
    apply ProductWO in H.
    destruct H as [q [r [? Hr]]].
    * destruct (eq_dec r 0) as [E|E].
      + left. exists (g q).
        now rewrite Hr, E, add_zero_r, mult_comm.
      + right. intros [k Hk]. apply E.
        enough (iE : inu r = inu 0). 
        { now apply inu_inj in iE. }
        enough ((g q) = k /\ inu r = inu 0) by tauto.
        unshelve eapply (iFac_unique _ _ (inu (S n))).
        -- apply axioms.
        -- apply lt_equiv; auto.
        -- apply lt_equiv; auto. lia.
        -- now rewrite add_zero, add_comm, <-Hr, mult_comm.
    * intros x y. apply dec_conj; [apply lt_dec|apply eq].
    Unshelve. lia.
  Qed.


  Lemma dec_div_2 :
    Witnessing D -> Discrete D -> Dec (fun '(n, d) => div_num n d).
  Proof.
    intros wo [eq]%Discrete_sum.
    constructor. intros [n d].
    destruct (eq d i0) as [->|h].
    { left; exists i0. now rewrite mult_zero_r. }
    destruct n as [|n].
    { right; intros [k Hk]. rewrite mult_zero in Hk; auto. }
    refine (let H := @iEuclid' D I axioms d (S n) _ in _).
    apply wo in H.
    - destruct H as [a Ha].
      apply Witnessing_nat in Ha. 
      * destruct Ha as [r [? Hr]].
        destruct (eq_dec r 0) as [E|E].
        + left. exists a.
          now rewrite Hr, E, add_zero_r, mult_comm.
        + right. intros [k Hk]. apply E.
          enough (iE : inu r = inu 0). 
          { now apply inu_inj in iE. }
          enough (a = k /\ inu r = inu 0) by tauto.
          unshelve eapply (iFac_unique _ _ (inu (S n))).
          -- apply axioms.
          -- now apply lt_equiv.
          -- apply lt_equiv; auto. lia.
          -- now rewrite add_zero, add_comm, <-Hr, mult_comm.
      * intros x. apply dec_conj; [apply lt_dec|apply eq].
    - intros ?. apply dec_lt_bounded_exist.
      intros ?. apply eq.
    Unshelve. lia.
  Qed.

  (** * Tennenbaum's Tehorem via a diagnoal argument. *)

  Theorem Tennenbaum_diagonal :
    RT_strong -> MP -> Enumerable D -> Discrete D -> ~ exists e, ~std e.
  Proof.
    intros rt mp enum eq.
    specialize (dec_div enum eq) as [dec_div].
    specialize enum as [G HG].
    apply Discrete_sum in eq.
    pose (g n := match G n with None => i0 | Some d => d end).
    pose (p n := ~ div_pi n (g n)).
    enough (Dec p) as Dec_p.
    destruct (rt _ Dec_p) as [ϕ (b1 & _ & H1 & H2)].
    intros nonStd.
    unshelve refine (let H:= Coding_nonStd_unary _ _ _ _ Hψ _ _ (∃ ϕ) _ in _); auto.
    - now apply nonStd_notStd.
    - intros e. apply MP_Dec_stable; auto.
      destruct eq as [eq]. constructor. intros n. apply eq.
    - now solve_bounds.
    - enough (~~False) by tauto.
      apply (DN_chaining H), DN.
      intros [cp Hcp]; clear H.
      destruct (HG cp) as [c Hc].
      specialize (Hcp c (fun _ => g c)) as [Hc1 Hc2].
      destruct Dec_p as [Dec_p], (Dec_p c) as [h|h].
      * specialize (H1 _ h). apply soundness in H1.
        apply h. unfold div_pi.
        eapply bound_ext with (N:= 2)(sigma:= inu c .: cp .: (fun _ => g c)).
        { repeat solve_bounds.
          eapply bounded_up; [apply Hψ|lia]. }
        2: {  cbn in Hc1; apply Hc1.
              destruct (H1 D I (fun _ => g c)) as [d Hd].
              intros ??; apply axioms; now constructor.
              exists d. rewrite <-switch_up_num.
              eapply bound_ext with (N:=1). 3: apply Hd.
              eapply subst_bound. 1: eauto.
              intros [|[]]; solve_bounds.
              cbn. rewrite num_subst. apply closed_num.
              intros [|]; solve_bounds.
          }
        intros [|[]]; cbn; [reflexivity| |lia].
        intros _. unfold g. now rewrite Hc.
      * specialize (H2 _ h). apply soundness in H2.
        apply h. intros H'. eapply H2 with (rho := fun _ => i0); fold sat.
        intros ??; apply axioms; now constructor.
        setoid_rewrite switch_num. cbn in Hc2.
        eapply bound_ext with (N:= 1)(sigma:= inu c .: cp .: (fun _ => g c)).
        { now solve_bounds. }
        intros []; cbn; [reflexivity|lia].
        apply Hc2. destruct H' as [d Hd].
        exists d. split.
        { eapply bound_ext. apply Hψ. 2: apply Hd.
          intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
        destruct Hd as [_ [k Hk]]. exists k.
        rewrite Hk; cbn. unfold g. now rewrite Hc.
    - unfold p. constructor. intros n.
      destruct (dec_div (Irred n, g n)) as [h|nh].
      + right. apply DN. now apply ψ_equiv.
      + left. intros ?. apply nh. eapply ψ_equiv; eauto.
  Qed.

  Theorem Tennenbaum_diagonal' :
    WRT_strong -> MP -> Enumerable D -> Discrete D -> ~ exists e, ~std e.
  Proof.
    intros wrt mp enum eq.
    specialize (dec_div enum eq) as [dec_div].
    specialize enum as [G HG].
    apply Discrete_sum in eq.
    pose (g n := match G n with None => i0 | Some d => d end).
    pose (p n := ~ div_pi n (g n)).
    enough (Dec p) as Dec_p.
    apply (DN_remove (wrt _ Dec_p)).
    intros [ϕ (b1 & _ & H1 & H2)] nonStd.
    unshelve refine (let H:= Coding_nonStd_unary _ _ _ _ Hψ _ _ (∃ ϕ) _ in _); auto.
    - now apply nonStd_notStd.
    - intros e. apply MP_Dec_stable; auto.
      destruct eq as [eq]. constructor. intros n. apply eq.
    - now solve_bounds.
    - enough (~~False) by tauto.
      apply (DN_chaining H), DN.
      intros [cp Hcp]; clear H.
      destruct (HG cp) as [c Hc].
      specialize (Hcp c (fun _ => g c)) as [Hc1 Hc2].
      destruct Dec_p as [Dec_p], (Dec_p c) as [h|h].
      * specialize (H1 _ h). apply soundness in H1.
        apply h. unfold div_pi.
        eapply bound_ext with (N:= 2)(sigma:= inu c .: cp .: (fun _ => g c)).
        { repeat solve_bounds.
          eapply bounded_up; [apply Hψ|lia]. }
        2: {  cbn in Hc1; apply Hc1.
              destruct (H1 D I (fun _ => g c)) as [d Hd].
              intros ??; apply axioms; now constructor.
              exists d. rewrite <-switch_up_num.
              eapply bound_ext with (N:=1). 3: apply Hd.
              eapply subst_bound. 1: eauto.
              intros [|[]]; solve_bounds.
              cbn. rewrite num_subst. apply closed_num.
              intros [|]; solve_bounds.
          }
        intros [|[]]; cbn; [reflexivity| |lia].
        intros _. unfold g. now rewrite Hc.
      * specialize (H2 _ h). apply soundness in H2.
        apply h. intros H'. eapply H2 with (rho := fun _ => i0); fold sat.
        intros ??; apply axioms; now constructor.
        setoid_rewrite switch_num. cbn in Hc2.
        eapply bound_ext with (N:= 1)(sigma:= inu c .: cp .: (fun _ => g c)).
        { now solve_bounds. }
        intros []; cbn; [reflexivity|lia].
        apply Hc2. destruct H' as [d Hd].
        exists d. split.
        { eapply bound_ext. apply Hψ. 2: apply Hd.
          intros [|[]]; cbn; [reflexivity|reflexivity|lia]. }
        destruct Hd as [_ [k Hk]]. exists k.
        rewrite Hk; cbn. unfold g. now rewrite Hc.
    - unfold p. constructor. intros n.
      destruct (dec_div (Irred n, g n)) as [h|nh].
      + right. apply DN. now apply ψ_equiv.
      + left. intros ?. apply nh. eapply ψ_equiv; eauto.
  Qed.


End Model.