Require Import FOL Peano Tarski Deduction CantorPairing NumberTheory Synthetic DecidabilityFacts.
Require Import Lia.

Import Vector.VectorNotations.

Require Import Equations.Equations Equations.Prop.DepElim.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.

Definition std {D I} d := exists n, @inu D I n = d.
Definition stdModel D I := forall d, exists n, (@inu D I) n = d.

Fact nonStd_notStd {D I} :
  (exists e, ~std e) -> ~ stdModel D I.
Proof.
  intros [e He] H; apply He, H.
Qed.


Section ChurchThesis.

Instance ff : falsity_flag := falsity_on.

Variable Phi : nat -> form.
Variable goed : form -> nat.
Hypothesis ϕg_id : forall alpha, Phi (goed alpha) = alpha.


Definition represents n f := forall x, Q ⊢I ∀ (Phi n)[up (num x)..] <--> $0 == num (f x).
Definition CT_Q :=
  forall f : nat -> nat, exists c, bounded 2 (Phi c) /\ represents c f.
Definition WCT_Q :=
  forall f : nat -> nat, ~ ~ exists c, bounded 2 (Phi c) /\ represents c f.


Definition RT_strong := forall p : nat -> Prop, Dec p ->
  exists c, bounded 1 (Phi c)
    /\ (forall x, p x -> Q ⊢I (Phi c)[(num x)..])
    /\ (forall x, ~ p x -> Q ⊢I ¬(Phi c)[(num x)..]).

Definition WRT_strong := forall p : nat -> Prop, Dec p ->
  ~ ~ exists c, bounded 1 (Phi c)
    /\ (forall x, p x -> Q ⊢I (Phi c)[(num x)..])
    /\ (forall x, ~ p x -> Q ⊢I ¬(Phi c)[(num x)..]).



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


  Lemma ψ_repr x d rho : (d .: inu x .: rho) ⊨ ψ <-> d = inu (Irred x).
  Proof.
    destruct Hψ as (_ & H).
    specialize (H x).
    apply soundness in H.
    specialize (H D I). cbn -[Q] in H.
    setoid_rewrite eval_num in H.
    rewrite <-switch_up_num.
    apply H.
    intros ax Hax. apply axioms. now constructor.
  Qed.


  Lemma ψ_equiv n a : div_pi n a <-> div_num (Irred n) a.
  Proof.
    unfold div_pi. cbn. split.
    - intros [d [->%ψ_repr H]]. apply H.
    - intros. exists (inu (Irred n)). rewrite ψ_repr. now split.
  Qed.




Section Facts.


Lemma std_add x y : 
  std (x i⊕ y) -> std x /\ std y.
Proof.
  intros [n Hn].
  revert Hn.  revert x y.
  induction n.
  - intros ?? H. symmetry in H. apply sum_is_zero in H as [-> ->].
    split; exists 0; auto. apply axioms. 
  - intros. destruct (@zero_or_succ D I axioms x) as [-> | [e ->]].
    + rewrite add_zero in Hn. rewrite <-Hn. split.
      exists 0; auto. exists (S n); auto. apply axioms.
    + cbn in *. rewrite add_rec in Hn. apply succ_inj in Hn.
      assert (std e /\ std y) as []. now apply IHn.
      split; auto.
      destruct H as [k <-]. exists (S k); auto.
      all: apply axioms.
Qed.

Lemma std_mult x y m : 
  (iσ x) i⊗ y = inu m -> std y.
Proof.
  cbn. rewrite mult_rec. intros E.
  assert (std (y i⊕ x i⊗ y)) as H%std_add.
  exists m; auto. tauto.
  apply axioms.
Qed.

Lemma lt_equiv x y : x < y <-> inu x i⧀ inu y.
Proof.
  assert (x < y <-> exists k, S x + k = y) as H.
  split.
  - induction y in x |-*; [lia|].
    destruct x; intros; [exists y; lia|].
    destruct (IHy x) as [k <-]; [lia|].
    exists k; lia.
  - intros []. lia.
  - split.
    + intros [k <-]%H. exists (inu k); cbn.
      now rewrite inu_add_hom.
    + intros [k Hk].
      assert (std (inu (S x) i⊕ k)) as [_ [l Hl]]%std_add.
      * exists y. cbn. now rewrite add_rec.
      * rewrite <-Hl in *.
        apply H. exists l.
        rewrite <-inu_inj, inu_add_hom; cbn;
        [now rewrite add_rec, Hk | apply axioms | apply axioms].
Qed.

Lemma num_lt_nonStd n d : ~ std d -> inu n i⧀ d.
Proof.
  intros nonStd.
  destruct (@trichotomy D I axioms (inu n) d) as [H|[<-|H]]; auto.
  all : contradiction nonStd.
  - exists n; auto.
  - apply lessthen_num in H. 
    destruct H as [k [? ->]].
    exists k; auto.
    apply axioms.
Qed.

End Facts.




Lemma stdModel_equiv :
  stdModel D I <-> exists ϕ, unary ϕ /\ (forall e, std e <-> forall ρ, (e .: ρ) ⊨ ϕ).
Proof.
  split.
  - intros H.
    pose (ϕ := $0 == $0).
    exists ϕ. split.
    repeat solve_bounds.
    intros e; split; intros ?; [reflexivity|apply H].
  - intros [ϕ Hϕ] e.
    apply Hϕ, induction. 
    + apply axioms.
    + apply Hϕ.
    + apply Hϕ. exists 0. reflexivity.
    + intros d [x <-]%Hϕ. apply Hϕ.
      exists (S x). reflexivity.
Qed.

Section Overspill.

  Variable α : form.
  Hypothesis Hα : unary α.

  Variable nStd : ~ stdModel D I.
  Variable stable_std : forall x, stable (std x).

  Corollary Overspill :
    (forall e, std e -> (forall rho, (e.:rho) ⊨ α) ) -> ~ (forall e, (forall rho, (e.:rho) ⊨ α) -> std e ).
  Proof.
    intros ??. apply nStd, stdModel_equiv. exists α. split.
    - apply Hα.
    - split; auto.
  Qed.
  
  
  Lemma Overspill_DN' :
    (forall e, std e -> (forall rho, (e.:rho) ⊨ α) ) ->  ~ ~ exists e, ~ std e /\ (forall rho, (e.:rho) ⊨ α).
  Proof.
    intros H1 H2. apply Overspill in H1. apply H1. intros e.
    intros H. apply stable_std. intros He. apply H2. now exists e.
  Qed.


  Lemma on_std_equiv : 
    (forall n rho, ((inu n).:rho) ⊨ α) <-> (forall e, std e -> (forall rho, (e.:rho) ⊨ α)).
  Proof.
    split; intros H.
    - intros e [n <-]. apply H.
    - intros n. apply H. exists n; reflexivity.
  Qed.

  Lemma Overspill_DN :
    (forall n rho, ((inu n).:rho) ⊨ α) ->  ~ ~ exists e, ~ std e /\ (forall rho, (e.:rho) ⊨ α).
  Proof.
    setoid_rewrite on_std_equiv.
    apply Overspill_DN'.
  Qed.


End Overspill.


Section Coding.


  Lemma Coding_nat A n :
    ~ ~ exists c, forall u, (u < n -> A u <-> Mod (Irred u) c = 0) /\ (Mod (Irred u) c = 0 -> u < n).
  Proof.
    induction n.
    - apply DN. exists 1. intros u. split. lia.
      intros [k ]%Mod_divides.
      assert (Irred u > 1). apply irred_Irred.
      destruct k; lia.
    - assert (~ ~ (A n \/ ~ A n)) as Dec_An by tauto.
      apply (DN_chaining Dec_An), (DN_chaining IHn), DN.
      clear IHn Dec_An.
      intros [a Ha] [A_n | NA_n].
      + exists (a * Irred n). intros u.
        assert (u < S n <-> u < n \/ u = n) as -> by lia.
        split.
        ++ intros [| ->]. split.
           +++ intros A_u%Ha.
               rewrite Mod_mult_hom, A_u.
               now rewrite Mod0_is_0.
               apply H.
           +++ intros [|H']%irred_integral_domain.
               apply Ha; assumption.
               apply irred_Mod_eq, inj_Irred in H'. lia. 
               all: apply irred_Irred.
           +++ intuition. apply Mod_divides. 
               now exists a.
        ++ intros [H |H]%irred_integral_domain.
           apply Ha in H. auto.
           apply irred_Mod_eq, inj_Irred in H. lia. 
           all: apply irred_Irred.
      + exists a. intros u.
        assert (u < S n <-> u < n \/ u = n) as -> by lia.
        split.
        ++ intros Hu. destruct Hu as [| ->]. 
           now apply Ha.
           split. now intros ?%NA_n.
           intros H%Ha. lia.
        ++ intros H%Ha. tauto.
  Qed.




  Lemma Divides_num x y : 
    div_num x (inu y) <-> Mod x y = 0.
  Proof.
    split.
    - intros [k Hk]. destruct x.
      + cbn in Hk. rewrite mult_zero in Hk.
        change i0 with (inu 0) in Hk.
        cbn. now apply inu_inj in Hk.
        apply axioms.
      + cbn in *. destruct (std_mult _ _ _  Hk) as [l <-].
        apply Mod_divides. exists l.
        change (iσ inu x) with (inu (S x)) in Hk.
        rewrite <-inu_mult_hom, inu_inj in Hk. lia.
        all: apply axioms.
    - intros [k Hk]%Mod_divides.
      exists (inu k).
      rewrite <-inu_mult_hom, inu_inj. lia.
      all: apply axioms.
  Qed.

  Lemma Coding_model' alpha : unary alpha ->
     forall n rho, rho ⊨ ¬ ¬ ∃ ∀ $0 ⧀ (num n) --> alpha <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).
  Proof.
    intros unary_α n rho. cbn.
    apply (DN_chaining (Coding_nat (fun n => forall rho, rho ⊨ alpha[(num n)..] ) n)), DN.
    intros [a Ha].
    exists (inu a).
    intros u' Hu. cbn in Hu.
    rewrite num_subst in Hu.
    setoid_rewrite eval_num in Hu.
    apply lessthen_num in Hu. 2: apply axioms.
    destruct Hu as [u [Hu ->]]. split.
    + intros α_u.
      exists (inu (Irred u)).
      split; [now apply ψ_repr| ].
      apply Divides_num.
      apply Ha; [apply Hu|].
      intros ?. rewrite switch_num.
      eapply bound_ext; [apply unary_α| |apply α_u].
      intros []; try lia; reflexivity.
    + intros [d [->%ψ_repr H]].
      eapply Divides_num, (proj1 (Ha u)) in H; auto.
      rewrite <-switch_num. apply H.
  Qed.


  Lemma Coding_model alpha : binary alpha ->
    forall n b rho, (b .: rho) ⊨ ¬ ¬ ∃ ∀ $0 ⧀ (num n) --> alpha[up ($1)..] <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).
  Proof.
    intros binary_α n b rho. cbn.
    apply (DN_chaining (Coding_nat (fun n => forall rho, (b .: rho) ⊨ alpha[(num n)..] ) n)), DN.
    intros [a Ha].
    exists (inu a).
    intros u' Hu. cbn in Hu.
    rewrite num_subst in Hu.
    setoid_rewrite eval_num in Hu.
    apply lessthen_num in Hu. 2: apply axioms.
    destruct Hu as [u [Hu ->]]. split.
    + intros α_u.
      exists (inu (Irred u)).
      split; [now apply ψ_repr| ].
      apply Divides_num.
      apply Ha; [apply Hu|].
      intros ?. rewrite switch_num.
      admit.
    + intros [d [->%ψ_repr H]].
      eapply Divides_num, (proj1 (Ha u)) in H; auto.
      rewrite <-switch_num.
  Admitted.


Section notStd.

  Variable notStd : ~ stdModel D I.
  Variable stable_std : forall x, stable (std x).

  Theorem Coding_nonStd' α : unary α ->
    ~ ~ exists a, forall u rho, (inu u .: a .: rho) ⊨ (α <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).
  Proof.
    intros unary_α.
    specialize (Coding_model' _ unary_α) as H.
    assert (forall n rho, (inu n .: rho) ⊨ ¬ ¬ ∃ ∀ $0 ⧀ $2 --> α <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3) ) as H'.
    intros n rho.
    rewrite <-switch_num. cbn -[sat].
    cbn in H; specialize (H n rho).
    assert (ψ[var] = ψ[up (up (up (num n)..))] ) as <-.
    { eapply bounded_subst. apply Hψ.
    intros [|[]]; try now intros. lia. }
    assert (α[var] = α[up (up (num n)..)] ) as E.
    { eapply bounded_subst. apply unary_α.
    intros []; try now intros. lia. }
    setoid_rewrite <-E.
    cbn. rewrite num_subst, num_subst, num_subst, !subst_var in *. apply H.
    apply Overspill_DN in H'; auto.
    2 : { repeat solve_bounds.
          all: eapply bounded_up; try apply binary_α; try apply Hψ.
          all: eauto; lia. }
    rewrite <-NNN_N.
    apply (DN_chaining H'), DN. clear H' H.
      intros (e & He1 & He2).
      specialize (He2 (fun _ => i0)).
      cbn in He2. apply (DN_chaining He2), DN.
      intros [a Ha].
      exists a. intros n rho.
      assert (inu n i⧀ e) as Hne;  [now apply num_lt_nonStd|].
      specialize (Ha _ Hne) as [Ha1 Ha2].
      split; cbn.
    + intros H. destruct Ha1 as [d Hd].
      eapply bound_ext. apply unary_α. 2: apply H.
      intros []; try now intros. lia.
      exists d. split.
      eapply bound_ext. apply Hψ. 2: apply Hd.
      intros [|[]]; try now intros. lia.
      apply Hd.
    + intros [k Hk].
      eapply bound_ext. apply unary_α. 2: apply Ha2.
      intros []; try now intros. lia.
      exists k. split.
      eapply bound_ext. apply Hψ. 2: apply Hk.
      intros [|[]]; try now intros. lia.
      apply Hk.
  Qed.



  Theorem Coding_nonstd α b : binary α ->
    ~ ~ exists a, forall u rho, (inu u .: b .: a .: rho) ⊨ (α <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $4)).
  Proof.
    intros binary_α.
    specialize (Coding_model _ binary_α) as H.
(*     assert (forall n rho, (inu n .: rho) ⊨ ¬ ¬ ∃ ∀ $0 ⧀ $2 --> α <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3) ) as H'.
    intros n rho.
    rewrite <-switch_num. cbn -[sat].
    cbn in H; specialize (H n rho).
    cbn. rewrite num_subst, num_subst, num_subst in *.
    assert (ψ[var] = ψ[up (up (up (num n)..))] ) as <-.
    eapply bounded_subst. apply Hψ.
    intros [|[]]; try now intros. lia.
    assert (α[var] = α[up (up (num n)..)] ) as <-.
    eapply bounded_subst. apply unary_α.
    intros []; try now intros. lia.
    rewrite !subst_var. apply H.
    apply Overspill_DN in H'; auto.
    2 : { repeat solve_bounds.
          all: eapply bounded_up; try apply binary_α; try apply Hψ.
          all: eauto; lia. }
    rewrite <-NNN_N.
    apply (DN_chaining H'), DN. clear H' H.
      intros (e & He1 & He2).
      specialize (He2 (fun _ => i0)).
      cbn in He2. apply (DN_chaining He2), DN.
      intros [a Ha].
      exists a. intros n rho.
      assert (inu n i⧀ e) as Hne;  [now apply num_lt_nonStd|].
      specialize (Ha _ Hne) as [Ha1 Ha2].
      split; cbn.
    + intros H. destruct Ha1 as [d Hd].
      eapply bound_ext. apply unary_α. 2: apply H.
      intros []; try now intros. lia.
      exists d. split.
      eapply bound_ext. apply Hψ. 2: apply Hd.
      intros [|[]]; try now intros. lia.
      apply Hd.
    + intros [k Hk].
      eapply bound_ext. apply unary_α. 2: apply Ha2.
      intros []; try now intros. lia.
      exists k. split.
      eapply bound_ext. apply Hψ. 2: apply Hk.
      intros [|[]]; try now intros. lia.
      apply Hk. *)
  Admitted.


End notStd.
End Coding.



Lemma dec_div :
  Enumerable D -> Discrete D -> forall d, Dec (Div_nat d).
Proof.
  intros [G Hg] [eq]%Discrete_sum d.
  pose (g n := match G n with None => i0 | Some d => d end).
  destruct (eq d i0) as [->|h].
  { constructor. left; exists i0. now rewrite mult_zero_r. }
  constructor. intros [|n].
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
      -- apply lt_equiv; lia.
      -- apply lt_equiv; lia.
      -- now rewrite add_zero, add_comm, <-Hr, mult_comm.
  * intros x y. apply dec_conj; [apply lt_dec|apply eq].
  Unshelve. lia.
Qed.


Lemma Dec_Div_nat :
  Witnessing D -> Discrete D -> forall d, Dec (Div_nat d).
Proof.
  intros wo [eq]%Discrete_sum d.
  destruct (eq d i0) as [->|h].
  { constructor. left; exists i0. now rewrite mult_zero_r. }
  constructor. intros [|n].
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
        -- apply lt_equiv; lia.
        -- now rewrite add_zero, add_comm, <-Hr, mult_comm.
    * intros x. apply dec_conj; [apply lt_dec|apply eq].
  - intros ?. apply dec_lt_bounded_exist.
    intros ?. apply eq.
  Unshelve. lia.
Qed.




Theorem Tennenbaum :
    WRT_strong -> MP -> Enumerable D -> Discrete D -> ~ exists e, ~std e.
Proof.
  intros wrt mp enum eq.
  specialize (dec_div enum eq) as [dec_div].
  specialize enum as [G HG].
  pose (g n := match G n with None => i0 | Some d => d end).
  pose (p n := ~ div_pi n (g n)).
  enough (Dec p) as Dec_p.
  apply (DN_remove (wrt _ Dec_p)).
  intros [np (b1 & H1 & H2)] nonStd.
  unshelve refine (let H:= Coding_nonStd' _ _ _ b1 in _).
  - now apply nonStd_notStd.
  - admit.
  - enough (~~False) by tauto.
    apply (DN_chaining H), DN.
    intros [cp Hcp]; clear H.
    destruct (HG cp) as [c Hc].
    specialize (Hcp c (fun _ => g c)) as [Hc1 Hc2].
    apply Dec_sum in Dec_p.
    destruct Dec_p as [Dec_p], (Dec_p c) as [h|h].
    * specialize (H1 _ h). apply soundness in H1.
      apply h. unfold div_pi.
      eapply bound_ext with (N:= 2)(sigma:= inu c .: cp .: (fun _ => g c)).
      { repeat solve_bounds.
        eapply bounded_up; [apply Hψ|lia]. }
      2: {  cbn in Hc1; apply Hc1.
            rewrite <-switch_num. apply H1.
            intros ??; apply axioms; now constructor. }
      intros [|[]]; cbn; [reflexivity| |lia].
      intros _. unfold g. now rewrite Hc.
    * specialize (H2 _ h). apply soundness in H2.
      apply h. intros H'. eapply H2 with (rho := fun _ => i0); fold sat.
      intros ??; apply axioms; now constructor.
      rewrite switch_num. admit.
  - unfold p. apply Dec_sum. constructor. intros n.
    destruct (dec_div (inu (Irred n)) (g n)) as [h|nh].
    + right. apply DN. now apply ψ_equiv.
    + left. intros ?. apply nh. now apply ψ_equiv.
Admitted.






End Model.
End ChurchThesis.