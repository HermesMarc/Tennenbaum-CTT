Require Import FOL Peano Tarski Deduction CantorPairing LogicFacts NumberTheory.
Require Import Lia.
Import Vector.VectorNotations.

Require Import Equations.Equations Equations.Prop.DepElim.

Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

(** * Tennenbaum's Theorem *)

(** ** Preliminaries *)


Definition surj {X Y} f := forall y : Y, exists x : X, f x = y.

Definition stable A := ~ ~A -> A.
Definition Stable {X} p := forall x : X, stable (p x).

Fact DN_forall_stable {X} p : 
  (forall x : X, stable (p x)) -> ~~ (forall x, p x) <-> (forall x, ~~ p x).
Proof. firstorder. Qed.

Fact stable_lemma {X} p : 
  (forall x, stable (p x)) -> ( ~(forall x : X, p x) <-> ~ ~ exists x, ~ p x).
Proof. firstorder. Qed.

Fact DN (A : Prop) : A -> ~~A. 
Proof. tauto. Qed.

Fact DN_implication {A B : Prop} : ~ ~ A -> ~ ~(A -> B) -> ~ ~ B.
Proof. tauto. Qed.

Fact NNN_N A : ~~~A <-> ~A.
Proof. tauto. Qed.

Fact DN_exists {X} {p : X -> Prop} : 
  (exists x, ~ ~ p x) -> (~ ~ exists x, p x).
Proof. firstorder. Qed.


(** *** Synthetic Computability Definitions *)
Definition enumerable p := exists f : nat -> nat, forall x, p x <-> exists n, f n = S x.
Definition Semidec {X} p := exists f : X -> nat -> bool, forall x, p x <-> exists n, f x n = true.
Definition Dec {X} p := inhabited( forall x : X, {p x} + {~ p x} ).

Definition EQ X := forall x y : X, dec (x = y).
Definition AP X := forall x y : X, dec (x <> y).
Definition Enum X := { f : nat -> option X & forall x, exists n, f n = Some x }.
Definition WO X := forall p : X -> Prop, LogicFacts.Dec p -> ex p -> sigma p.

Definition MP := forall p : nat -> Prop, Dec p -> stable(ex p).


Lemma Dec_equiv {X} p :
  Dec p <-> (exists f, forall x : X , p x <-> f x = true).
Proof.
  split.
  - intros [D].
    exists (fun x => if D x then true else false).
    intros x. destruct (D x); cbn; intuition congruence.
  - intros [f Hf]. constructor. intros x. destruct (f x) eqn:Hx; intuition.
    right. intros ?%Hf. congruence.
Qed.

Lemma Dec_nat_equiv (p : nat -> Prop) : 
  Dec p <-> (exists f, forall x, p x <-> f x = 0).
Proof.
  setoid_rewrite Dec_equiv. split; intros [f Hf].
  - exists (fun x => if f x then 0 else 1).
    intros x. setoid_rewrite Hf.
    destruct (f x); split; congruence.
  - exists (fun x => match f x with 0 => true | _ => false end).
    intros x. setoid_rewrite Hf.
    destruct (f x); split; congruence.
Qed.




(** *** Standard Model Definition *)
Definition std {D I} d := exists n, @inu D I n = d.
Definition stdModel D I := surj (@inu D I).



(** *** Delta_0 and Sigma_1 Formulas *)

Section Delta0.

  Definition unary α := bounded 1 α.
  Definition binary α := bounded 2 α.

  (** Define Δ0 formulas *)

  Inductive Δ0 : forall {ff : falsity_flag}, form -> Prop :=
  | Delta_fal : @Δ0 falsity_on ⊥
  | Delta_eq ff : forall t s, @Δ0 ff (t == s)
  (* | Delta_lt ff : forall t s, @Δ0 ff (t ⧀ s) *)
  | Delta_Conj ff : forall α β, @Δ0 ff α -> Δ0 β -> @Δ0 ff (α ∧ β)
  | Delta_Disj ff : forall α β, @Δ0 ff α -> Δ0 β -> Δ0 (α ∨ β)
  | Delta_Impl ff : forall α β, @Δ0 ff α -> Δ0 β -> Δ0 (α --> β).

  Inductive Δ0' : forall {ff : falsity_flag}, form -> Prop :=
  | Delta_id ff : forall α, Δ0 α -> @Δ0' ff α
  | Delta_bounded_exist ff : forall α, @Δ0' ff α -> Δ0' (∃ $0 ⧀ $1 ∧ α)
  | Delta_bounded_forall ff : forall α, @Δ0' ff α -> Δ0' (∀ $0 ⧀ $1 --> α).


  Inductive Σ1 : forall {ff : falsity_flag}, form -> Prop :=
  | Sigma_Delta ff : forall α, Δ0' α -> @Σ1 ff α
  | Sigma_exists ff : forall α, Σ1 α -> @Σ1 ff (∃ α).


  Lemma inversion_bounded_bin α β n b : bounded n (bin b α β) -> bounded n α /\ bounded n β.
  Proof.
    intros H. destruct b.
    all: inversion H; subst.
    all: apply Eqdep_dec.inj_pair2_eq_dec in H1.
    all: apply Eqdep_dec.inj_pair2_eq_dec in H5.
    all: try decide equality; intuition congruence.
  Qed.

  Lemma inversion_Δ0_bin α β b : Δ0 (bin b α β) -> Δ0 α /\ Δ0 β.
  Proof.
    intros H. destruct b.
    all: inversion H; subst.
    all: apply Eqdep_dec.inj_pair2_eq_dec in H1.
    all: apply Eqdep_dec.inj_pair2_eq_dec in H0.
    all: try decide equality; intuition congruence.
  Qed.

  Lemma inversion_Δ0_forall α : Δ0' (∀ α) -> exists ϕ, Δ0' ϕ /\ α = $0 ⧀ $1 --> ϕ.
  Proof.
    intros H. inversion H; subst.
    all: apply Eqdep_dec.inj_pair2_eq_dec in H0; try decide equality.
    + rewrite H0 in *. inversion H2.
    + exists α0. split; auto.
  Qed.


  (* Delta_0 Formulas stay Delta_0 under substitions. *)
  
  Lemma subst_Δ0 phi sigma : Δ0 phi -> Δ0 (phi[sigma]).
  Proof.
    induction phi using form_ind_falsity_on.
    - now cbn.
    - destruct P.
    - destruct b; intros H; cbn; constructor.
      all : try apply IHphi1; try apply IHphi2; inversion H; subst.
      all: (apply Eqdep_dec.inj_pair2_eq_dec in H0;
                apply Eqdep_dec.inj_pair2_eq_dec in H1); try decide equality.
      all: now rewrite H0, H1 in *.
    - intros. constructor.
    - intros H; inversion H.
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


  Lemma subst_bound phi N : Δ0 phi ->
    forall B sigma, bounded N phi -> (forall n, n < N -> bounded_t B (sigma n) ) -> bounded B (phi[sigma]).
  Proof.
    intros H0.
    induction phi using form_ind_falsity_on; cbn; intros B sigma H Hb.
    - solve_bounds.
    - rename t into v.
      constructor. intros t Ht.
      depelim Ht.
    - apply inversion_bounded_bin in H.
      apply inversion_Δ0_bin in H0.
      constructor.
      now apply IHphi1.
      now apply IHphi2.
    - constructor; eapply subst_bound_t with (N := N); auto.
      all : now inversion H.
    - inversion H0.
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



Lemma Q_contra α : Q ⊢I α /\ Q ⊢I ¬α -> False.
Proof.
  intros [H%soundness nH%soundness].
  specialize (H nat interp_nat (fun _ => 0)).
  specialize (nH nat interp_nat (fun _ => 0)).
  cbn -[Q] in nH. apply nH.
  - apply Q_std_axioms.
  - apply H, Q_std_axioms. 
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
  Variable H0 : Δ0 phi.

  Variable D : Type.
  Variable I : interp D.
  Variable axioms : forall ax, PA ax -> ⊨ ax. 

  
  Theorem Q_dec_closed_Δ0 : Q_dec phi.
  Proof.
    induction phi using form_ind_falsity_on.
    - cbn -[Q]. right.
      apply II, Ctx. firstorder.
    - destruct P.
    - apply inversion_bounded_bin in Hcl.
      apply inversion_Δ0_bin in H0.
      specialize (IHf1 (proj1 Hcl) (proj1 H0)).
      specialize (IHf2 (proj2 Hcl) (proj2 H0)).
      destruct b.
      + destruct IHf1 as [Hf1 | Hf1], IHf2 as [Hf2 | Hf2].
        left. now apply CI.
        all: right; apply II.
        eapply IE. apply Weak with Q. apply Hf2. shelve.
        eapply CE2, Ctx. firstorder.
        eapply IE. apply Weak with Q. apply Hf1. shelve.
        eapply CE1, Ctx. firstorder.
        eapply IE. apply Weak with Q. apply Hf2. shelve.
        eapply CE2, Ctx. firstorder.
        Unshelve. all: apply Faster1.
      + destruct IHf1 as [Hf1 | Hf1], IHf2 as [Hf2 | Hf2].
        all: try (left; now (apply DI1 + apply DI2)).
        right. apply II. eapply DE.
        apply Ctx; firstorder.
        eapply IE. apply Weak with Q. apply Hf1. apply Faster2.
        apply Ctx; firstorder.
        eapply IE. apply Weak with Q. apply Hf2. apply Faster2.
        apply Ctx; firstorder.
      + destruct IHf1 as [Hf1 | Hf1], IHf2 as [Hf2 | Hf2].
        left. apply II. apply Weak with Q. apply Hf2. apply Faster1.
        right. apply II. eapply IE.
        apply Weak with Q. apply Hf2. apply Faster1.
        eapply IE. apply Ctx. firstorder.
        apply Weak with Q. apply Hf1. apply Faster1.
        left. now apply imps, Exp, imps.
        left. now apply imps, Exp, imps.
    - apply term_eq_dec; now inversion Hcl. 
    - now exfalso.
  Qed.


  Theorem Q_dec_closed_Δ0' α : 
    Δ0' α -> bounded 0 α -> Q_dec α.
  Proof.
  Abort.



  Corollary Q_neg_equiv_Δ0 : (~ Q ⊢I phi) <-> Q ⊢I ¬ phi.
  Proof.
    apply Q_neg_equiv, Q_dec_closed_Δ0.
  Qed.


  Corollary dec_closed_Δ0: {PA ⊢TI phi} + {PA ⊢TI ¬ phi}.
  Proof.
    destruct Q_dec_closed_Δ0 as [H|H].
    - left. exists Q. split.
      intros; now constructor.
      apply H.
    - right. exists Q. split.
      intros; now constructor.
      apply H. 
  Qed.


  Corollary neg_equiv_Δ0 : (~ PA ⊢TI phi) <-> PA ⊢TI ¬ phi.
  Proof.
    split.
    - intros. now destruct dec_closed_Δ0.
    - intros [Γ1 []] [Γ2 []].
      apply PA_consistent.
      exists (Γ1 ++ Γ2)%list.
      split. now apply incl_app.
      eapply IE. eapply Weak. apply H1. intuition.
      eapply Weak. apply H3. intuition. 
  Qed.


  Lemma Δ0_complete rho : sat interp_nat rho phi -> PA ⊢TI phi.
  Proof.
    intros H. destruct dec_closed_Δ0 as [C|C]. assumption.
    specialize (tsoundness C interp_nat rho) as F.
    exfalso. apply F. apply PA_std_axioms. apply H.
  Qed.

  Lemma Q_Δ0_complete rho : sat interp_nat rho phi -> Q ⊢I phi.
  Proof.
    intros H. destruct Q_dec_closed_Δ0 as [C|C]. assumption.
    specialize (soundness C interp_nat rho) as F.
    exfalso. apply F.
    apply Q_std_axioms. apply H.
  Qed.


  Lemma Δ0_complete' rho : sat I rho phi -> PA ⊢TI phi.
  Proof.
    intros H. destruct dec_closed_Δ0 as [C|C]. assumption.
    specialize (tsoundness C I rho) as F.
    exfalso. apply F. intuition. apply H.
  Qed.


  Lemma Q_Δ0_complete' rho : sat I rho phi -> Q ⊢I phi.
  Proof.
    intros H. destruct Q_dec_closed_Δ0 as [C|C]. assumption.
    specialize (soundness C I rho) as F.
    exfalso. apply F. intros ??. apply axioms.
    now constructor.
    apply H.
  Qed.


  Lemma Δ0_absolutness rho : sat interp_nat rho phi -> PA⊨ phi.
  Proof.
    intros H. apply tsoundness.
    destruct dec_closed_Δ0 as [C|C]. assumption.
    specialize (tsoundness C interp_nat rho) as F.
    exfalso. apply F. apply PA_std_axioms. apply H.
  Abort.


  Lemma Δ0_absolutness' rho : sat I rho phi -> PA⊨ phi.
  Proof.
    intros H. apply tsoundness.
    destruct dec_closed_Δ0 as [C|C]. assumption.
    specialize (tsoundness C I rho) as F.
    exfalso. apply F. intuition. apply H.
  Qed.



End Closed.







Section Tennenbaum.


Instance ff : falsity_flag := falsity_on.

(* We assume a PA model with decidable equality *)

Variable D : Type.
Variable I : interp D.

Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).
Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).

Variable axioms : forall ax, PA ax -> ⊨ ax. 

Hypothesis dec_eq : forall x y : D, {x = y} + {x <> y}.


Notation "N⊨ phi" := (forall rho, @sat _ _ nat interp_nat _ rho phi) (at level 40).


(** *** Definition of CT and RT *)

(* Smith Theorem 39.2 page 298. Also says that ψ is Σ1 *)
Definition CT_Q :=
  forall f : nat -> nat, exists ψ, binary ψ /\ Σ1 ψ
  /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (f x) ).


Definition RT_weak := forall p : nat -> Prop,  enumerable p ->
   exists ϕ, Δ0 ϕ /\ binary ϕ /\ forall n, p n <-> Q ⊢I (∃ϕ)[(num n)..].

Definition RT_strong := forall p : nat -> Prop, Dec p ->
  exists ϕ, Σ1 ϕ /\ unary ϕ
  /\ (forall x, p x -> Q ⊢I ϕ[(num x)..])
  /\ (forall x, ~ p x -> Q ⊢I ¬ϕ[(num x)..]).





Definition Ex_lt n (α : form) := ∃ $0 ⧀ (num n) ∧ α.

(*  alpha decidable for every term *)
Lemma bounded_exists_Δ0_equiv n α : Δ0 α -> bounded 0 (Ex_lt n α) -> 
  Q ⊢I Ex_lt n α <-> exists k, k < n /\ Q ⊢I α[(num k)..].
Proof.
  intros Δ0_α closed. split.
  - intros H. unfold Ex_lt in *.
    apply soundness in H.
    destruct (H _ interp_nat (fun _ => 0)) as [k [H1 H2]].
    + now apply Q_std_axioms.
    + exists k. split.
    ++  destruct H1 as [m Hm]. apply lt_nat_equiv.
        exists m. cbn in Hm.
        rewrite num_subst, eval_num, inu_nat_id in Hm. lia.
    ++  rewrite <-(inu_nat_id k), <-switch_num in H2.
        apply Q_Δ0_complete in H2.
        * assumption.
        * inversion closed; subst.
          apply Eqdep_dec.inj_pair2_eq_dec in H6.
          rewrite H6 in H5.
          inversion H5; subst.
          apply Eqdep_dec.inj_pair2_eq_dec in H9.
          rewrite H9 in *.
          eapply subst_bound; eauto.
          intros []; intros; cbn; 
          [apply closed_num | lia].
          all: decide equality.
        * now apply subst_Δ0.
  - intros [k [[m Hm]%lt_nat_equiv H2]].
    apply ExI with (t := num k). cbn -[Q].
    apply CI; auto.
    apply ExI with (t := num m). cbn -[Q].
    rewrite !num_subst, <-Hm. cbn -[Q].
    apply eq_succ. easy.
    apply symmetry, num_add_homomorphism; easy.
Abort.


Lemma switch_nat_num α rho (n : nat) : sat interp_nat rho (α[(num n)..]) <-> sat interp_nat (n.:rho) α.
Proof.
  split; intros H.
  - rewrite <- (inu_nat_id n). erewrite <-eval_num. apply sat_single, H.
  - apply sat_single. now rewrite eval_num, inu_nat_id.
Qed.


Lemma nolessthen_zero d : ~ d i⧀ i0.
Proof. now intros [? []%zero_succ]. Qed.


Section Sigma1.

  Variable α : form.
  Variable binary_α : binary α.
  Variable Δ0_α : Δ0 α.

  Lemma Σ1_complete' n :
    N⊨ (∃ α)[(num n)..] -> exists m, Q ⊢I α[up (num n)..][(num m)..].
  Proof.
    intros [m Hm].
    rewrite <-switch_nat_num in Hm.
    apply Q_Δ0_complete in Hm.
    exists m. auto.
    - eapply subst_bound; eauto.
      now apply subst_Δ0.
      eapply subst_bound; eauto.
      intros [|[]]; solve_bounds; cbn.
      rewrite num_subst.
      apply closed_num.
      intros [|]; solve_bounds; cbn.
      apply closed_num.
    - now repeat apply subst_Δ0.
      Unshelve. exact (fun _ => 0).
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




Section Insep.

  Variable surj_form_ : { f : nat -> form & surj f }.
  Variable enumerable_Q_prv : forall phi, enumerable (fun n => Q ⊢I phi n).
  
  Definition f := projT1 surj_form_.
  Definition surj_form := projT2 (surj_form_).
  Definition A n := Q ⊢I ¬(f n)[(num n)..].
  Definition B n := Q ⊢I (f n)[(num n)..].

  
  Lemma Disjoint_AB : forall n, ~(A n /\ B n).
  Proof.
    unfold A, B. intros n [A_n B_n].
    eapply Q_contra. eauto.
  Qed.


  Definition Insep1 :=
    exists A B : nat -> Prop, 
      enumerable A /\ enumerable B /\ 
      (forall n, ~ (A n /\ B n) ) /\ 
      (forall ϕ,
          (forall n, Q ⊢I ϕ[(num n)..] \/ Q ⊢I ¬ ϕ[(num n)..] ) -> 
          (forall n, A n -> Q ⊢I ϕ[(num n)..]) -> 
          (forall n, ~ B n /\ Q ⊢I ϕ[(num n)..]) -> False).


  Definition Insep2 :=
    exists α β,
      binary α /\ Δ0 α /\ binary β /\ Δ0 β /\ 
      (forall n, ~ Q ⊢I ((∃ α) ∧ (∃ β))[(num n)..] ) /\ 
      (forall ϕ,
          (forall n, Q ⊢I ϕ[(num n)..] \/ Q ⊢I ¬ ϕ[(num n)..] ) -> (forall n, Q ⊢I (∃ α)[(num n)..] -> Q ⊢I ϕ[(num n)..]) -> 
          (forall n, ~ Q ⊢I (∃ β)[(num n)..] /\ Q ⊢I ϕ[(num n)..]) -> False).


  Definition Insep :=
    exists α β, 
      binary α /\ Δ0 α /\ binary β /\ Δ0 β /\ 
      (forall n, ~ Q ⊢I ((∃ α) ∧ (∃ β))[(num n)..] ) /\ 
      (forall G, Dec G -> (forall n, Q ⊢I (∃ α)[(num n)..] -> G n) -> 
            (forall n, ~ (Q ⊢I (∃ β)[(num n)..] /\ G n)) -> False).


  Definition Insep3 :=
    exists A B : nat -> Prop,
      enumerable A /\ enumerable B /\ 
      (forall n, ~ (A n /\ B n) ) /\ 
      (forall D, Dec D -> (forall n, A n -> D n) ->
            (forall n, ~ B n /\ D n) -> False).


  Definition obj_Insep := 
    exists α β,
      binary α /\ Δ0 α /\ binary β /\ Δ0 β /\ 
      ( PA ⊢TI ¬ ∃ (∃ α) ∧ (∃ β) ) /\ 
      (forall G, 
          Dec G -> (forall n, N⊨ (∃ α)[(num n)..] -> G n) ->
          (forall n, ~ (N⊨ (∃ β)[(num n)..] /\ G n)) -> False).



  Lemma Insep_1 : Insep1.
  Proof.
    exists A, B. repeat split; auto.
    1,2 : apply enumerable_Q_prv.
    { apply Disjoint_AB. }
    intros γ dec_γ.
    unfold A, B in *.
    destruct (surj_form γ) as [c Hc].
    destruct (dec_γ c) as [h|h]; rewrite <-Hc in *.
    - intros _ H.
      now apply (H c).
    - intros H _. specialize (H _ h).
      eapply Q_contra. eauto.
  Qed.


  Lemma Insep_3 : RT_strong -> Insep3.
  Proof.
    intros rt.
    destruct Insep_1 as (A' & B' & HA' & HB' & Disj & ?).
    exists A', B'. repeat split; auto.
    intros G Dec_G.
    destruct (rt G Dec_G) as [γ [sig_γ [unary_γ [H1 H2]]]].
    specialize (H γ); intuition.
  Qed.


  Lemma Insep_2 : RT_weak -> Insep2.
  Proof.
    intros rt.
    destruct Insep_1 as (A' & B' & HA' & HB' & Disj & ?).
    destruct (rt A' HA') as [α (Ha0 & Ha1 & Hα)], (rt B' HB') as [β (Hb0 & Hb1 & Hβ)].
    exists α, β. repeat split; auto.
    - intros n nH % soundness. apply (Disj n).
      rewrite Hα, Hβ.
      split; apply Σ1_complete; auto.
      all: intros rho; specialize (nH _ interp_nat rho); apply nH; apply Q_std_axioms.
    - setoid_rewrite Hα in H.
      setoid_rewrite Hβ in H.
      apply H.
  Qed.

  (** ** Assuming RT there are recursively inseparable Sigma_1 Formulas. *)

  Lemma Inseparable : RT_strong -> RT_weak -> Insep.
  Proof.
    intros rts rtw.
    destruct (rtw A (enumerable_Q_prv _)) as [α (Ha0 & Ha1 & Hα)], (rtw B (enumerable_Q_prv _)) as [β (Hb0 & Hb1 & Hβ)].
    exists α, β. repeat split; auto.
    - intros n H % soundness. apply (Disjoint_AB n).
      rewrite Hα, Hβ.
      split; apply Σ1_complete; auto.
      all: intros rho; specialize (H _ interp_nat rho); apply H; apply Q_std_axioms.
    - intros G Dec_G.
      destruct (rts G Dec_G) as [γ [sig_γ [unary_γ [H1 H2]]]].
      setoid_rewrite <-Hα.
      setoid_rewrite <-Hβ.
      unfold A, B.
      destruct (surj_form γ) as [c Hc].
      destruct Dec_G as [Dec_G].
      destruct (Dec_G c) as [h|h].
      + intros _ H.
        apply (H c). split; [|trivial].
        unfold f. rewrite Hc. now apply H1.
      + intros H _. apply h, (H c).
        unfold f. rewrite Hc. now apply H2.
  Qed.


End Insep.



(** ** Overspill Lemma *)

Section Overspill.

  Variable α : form.
  Hypothesis Hα : unary α.

  Variable nStd : ~ stdModel D I.
  Variable stable_std : forall x, stable (std x).


  Lemma stdModel_equiv :
    stdModel D I <-> exists ϕ, unary ϕ /\ (forall e, std e <-> forall ρ, (e .: ρ) ⊨ ϕ).
  Proof.
    split.
    - intros H.
      pose (ϕ := $0 == $0).
      exists ϕ. split.
      repeat solve_bounds.
      cbn. firstorder.
    - intros [ϕ Hϕ] e.
      apply Hϕ.
      apply induction.
      apply axioms.
      + apply Hϕ.
      + apply Hϕ. exists 0. reflexivity.
      + intros d [x <-]%Hϕ. apply Hϕ.
        exists (S x). reflexivity.
  Qed.

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


  Lemma on_std_equiv : (forall n rho, ((inu n).:rho) ⊨ α) <-> (forall e, std e -> (forall rho, (e.:rho) ⊨ α)).
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



Section weak_Overspill.

  Variable α : form.
  Hypothesis Hα : unary α.

  Variable nnnStd : ~ forall e, ~~ std e.


  Lemma weak_std_equiv :
    (forall e, ~~ std e) <-> exists ϕ, unary ϕ /\ (forall e, ~~ std e <-> forall ρ, (e .: ρ) ⊨ ϕ).
  Proof.
    split.
    - intros H.
      pose (ϕ := $0 == $0).
      exists ϕ. split.
      repeat solve_bounds.
      cbn. firstorder.
    - intros [ϕ Hϕ] e.
      apply Hϕ.
      apply induction.
      apply axioms.
      + apply Hϕ.
      + apply Hϕ. apply DN.
        exists 0. reflexivity.
      + intros d H%Hϕ. apply Hϕ.
        eapply DN_implication.
        apply H. apply DN.
        intros [x <-].
        exists (S x). reflexivity.
  Qed.


  Corollary weak_Overspill :
    (forall e, ~~ std e -> (forall rho, (e.:rho) ⊨ α) ) -> ~ (forall e, (forall rho, (e.:rho) ⊨ α) -> ~~ std e ).
  Proof.
    intros ??. apply nnnStd, weak_std_equiv. exists α. split.
    - apply Hα.
    - split; auto.
  Qed.


  Lemma weak_Overspill_DN' :
    (forall e, ~~ std e -> (forall rho, (e.:rho) ⊨ α) ) ->  ~ ~ exists e, ~ std e /\ (forall rho, (e.:rho) ⊨ α).
  Proof.
    intros H1 H2. 
    eapply weak_Overspill in H1. apply H1. intros e.
    intros H. intros He. apply H2. now exists e.
  Qed.
  

End weak_Overspill.



(** ** Facts about divisibility and order of standard and non-standard numbers. *)


Lemma std_add x y : std (x i⊕ y) -> std x /\ std y.
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


Lemma lt_equiv x y : x < y <-> inu x i⧀ inu y.
Proof.
  induction y in x |-*.
  - split; [lia|].
    now intros ?%nolessthen_zero.
  - destruct x as [|z].
    + split; [|lia].
      intros _. exists (inu y).
      cbn. now rewrite add_zero.
    + assert (S z < S y <-> z < y) as -> by lia.
      cbn. rewrite lt_SS; [now apply IHy| apply axioms].
Qed.



Lemma std_mult x y m : (iσ x) i⊗ y = inu m -> std y.
Proof.
  cbn. rewrite mult_rec. intros E.
  assert (std (y i⊕ x i⊗ y)) as H%std_add.
  exists m; auto. tauto.
  apply axioms.
Qed.


Lemma std_mult' x y n : x i⊗ y = iσ (inu n) -> std y.
Proof.
  intros H.
  destruct (@zero_or_succ D I axioms x) as [-> | [k ->]].
  - rewrite mult_zero in H. now apply zero_succ in H.
    apply axioms.
  - change (iσ inu n) with (inu (S n)) in H.
    now apply std_mult in H.
Qed.



Definition Divides n (d : D) := exists e, inu n i⊗ e = d.


Lemma LEM_Divides : forall n d, Divides n d \/ ~ Divides n d.
Proof.
  intros [] e; unfold Divides.

  - destruct (@zero_or_succ D I axioms e) as [-> | [x ->]].
    + left. exists i0. now rewrite mult_zero.
    + right. intros [d Hd]. rewrite mult_zero in Hd.
       now apply zero_succ in Hd. apply axioms.
       
  - assert (Hn : S n > 0) by lia.
    destruct (@iEuclid' D I axioms e (S n) Hn) as [d [r [? Hr]]].
    destruct (eq_dec r 0) as [E|E].
    + left. exists d.
      now rewrite Hr, E, add_zero_r, mult_comm.
    + right. intros [k Hk]. apply E.
      enough (iE : inu r = inu 0). now apply inu_inj in iE.
      enough (d = k /\ inu r = inu 0) by tauto.
      eapply (iFac_unique _ _ (inu (S n))).
      now apply lt_equiv.
      now apply lt_equiv.
      now rewrite add_zero, add_comm, <-Hr, mult_comm.
    Unshelve. apply axioms.
Qed.




Lemma dec_Divides' : WO D -> EQ D -> forall n d, n > 0 -> dec(Divides n d).
Proof.
  intros wo deceq [] d Hn; unfold Divides. lia.

  specialize (@iEuclid' D I axioms d (S n) Hn) as H.
  apply wo in H.
  destruct H as [a Ha].
  apply Witness in Ha. destruct Ha as [r [? Hr]].

  destruct (eq_dec r 0) as [E|E].
  + left. exists a.
    now rewrite Hr, E, add_zero_r, mult_comm.
  + right. intros [k Hk]. apply E.
    enough (iE : inu r = inu 0). now apply inu_inj in iE.
    enough (a = k /\ inu r = inu 0) by tauto.
    eapply (iFac_unique _ _ (inu (S n))).
    now apply lt_equiv.
    now apply lt_equiv.
    now rewrite add_zero, add_comm, <-Hr, mult_comm.
  + intros x. apply dec_conj. apply lt_dec.
    apply deceq.
  + intros ?. apply dec_lt_bounded_exist.
    intros ?. apply deceq.
  Unshelve. apply axioms.
Qed.


Lemma dec_Divides_temp : ((WO D -> False) -> False) -> ((EQ D -> False) -> False) -> ((forall n d, n > 0 -> dec(Divides n d)) -> False) -> False.
Proof.
  intros nn_wo nn_deceq; unfold Divides.
  intros nh.
  apply nn_deceq. intros deceq.
  apply nn_wo. intros wo.
  apply nh.
  intros [] d Hn. lia.
  specialize (@iEuclid' D I axioms d (S n) Hn) as H.
  apply wo in H.
  destruct H as [a Ha].
  apply Witness in Ha. destruct Ha as [r [? Hr]].

  destruct (eq_dec r 0) as [E|E].
  + left. exists a.
    now rewrite Hr, E, add_zero_r, mult_comm.
  + right. intros [k Hk]. apply E.
    enough (iE : inu r = inu 0). now apply inu_inj in iE.
    enough (a = k /\ inu r = inu 0) by tauto.
    eapply (iFac_unique _ _ (inu (S n))).
    now apply lt_equiv.
    now apply lt_equiv.
    now rewrite add_zero, add_comm, <-Hr, mult_comm.
  + intros x. apply dec_conj. apply lt_dec.
    apply deceq.
  + intros ?. apply dec_lt_bounded_exist.
    intros ?. apply deceq.
  Unshelve. apply axioms.
Qed.


Lemma dec_num_lt n d : EQ D -> dec(inu n i⧀ d).
Proof.
  intros deceq. induction n. 
  - destruct (deceq i0 d) as [<- |].
    right. apply nolessthen_zero.
    left. destruct (@zero_or_succ D I axioms d) as [| [k ->]].
    congruence.
    exists k. now rewrite add_zero.
  - destruct IHn as [H|H]. 
    + destruct (dec_eq (inu (S n)) d) as [<- |].
      right. intros ?%lt_equiv; lia.
      left. destruct H as [k ->].
      destruct (@zero_or_succ D I axioms k) as [->|[k' ->]].
      rewrite add_zero_r in *. tauto.
      all: try apply axioms.
      exists k'; cbn.
      now rewrite add_rec, add_rec_r.
    + right. intros [k ->]. apply H.
      exists (iσ k). cbn.
      now rewrite add_rec, add_rec_r.
 Qed.



Lemma LEM_num_lt n d : inu n i⧀ d \/ ~ inu n i⧀ d.
Proof.
  induction n in d |-*;
  destruct (@zero_or_succ D I axioms d) as [->| [k ->]].
  + right. apply nolessthen_zero.
  + left. exists k. now rewrite add_zero.
  + right. apply nolessthen_zero.
  + destruct (IHn k) as [H|H]; [apply lt_SS in H|]. 
    * now left. 
    * apply axioms.
    * right. intros nH. apply H. now apply lt_SS.
Abort.

(** *** Non-standard numbers are larger than any numeral. *)

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


Lemma Divides_num x y : Divides x (inu y) <-> Mod x y = 0.
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


(** *** Divisibility is decidable if the PA model is a data type *)

(* Proof the way it is presented in Smith and Kaye *)
Lemma dec_Divides n d : Enum D -> EQ D -> 0 < n -> dec(Divides n d).
Proof.
  intros [g Hg] deceq H0.
  pose (F := fun n => match (g n) with Some d => d | None => i0 end ).

  enough ( { r & { k & d = (inu n) i⊗ (F k) i⊕ (inu r) /\ (i0 i⧀ inu n -> inu r i⧀ inu n) }} ) as (r & k & [E B]).
  destruct (nat_eqdec r 0) as [R|R]; unfold Divides.
  - left. exists (F k).
    now rewrite E, R, add_zero_r.
  - right. intros H.
    destruct H as [d' H'].
    assert (F k = d' /\ inu r = i0) as [_ R'].
    eapply (iFac_unique D I (inu n)).
    apply B. shelve. shelve.
    rewrite add_zero.
    rewrite mult_comm in H'. rewrite H'.
    now rewrite add_comm, mult_comm.
    all : try apply axioms.
    apply R. now apply (@inu_inj D I).
  - apply ProductWO.
    intros. apply dec_conj. apply deceq.
    apply dec_imp; change i0 with (inu 0); apply dec_num_lt; auto.
    destruct (@iEuclid D I axioms d (inu n) ) as (K & R & [H1 H2]).
    destruct (Hg K) as [k Hk].
    destruct (@lessthen_num D I axioms n R) as [r [? ->]]. apply H2. shelve.
    exists r, k. unfold F. now rewrite Hk, mult_comm.
    Unshelve. apply axioms.
    all: now apply lt_equiv in H0.
Qed.



Section Thm4.
  
  Variable ψ : form.
  Variable Hψ : binary ψ /\ Σ1 ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (Irred x) ).


  Definition Divides_Irred n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).


  Lemma ψ_repr x d rho : (d .: inu x .: rho) ⊨ ψ <-> d = inu (Irred x).
  Proof.
    destruct Hψ as (_ & _ & H).
    specialize (H x).
    apply soundness in H.
    specialize (H D I). cbn -[Q] in H.
    setoid_rewrite eval_num in H.
    rewrite <-switch_up_num.
    apply H.
    intros ax Hax. apply axioms. now constructor.
  Qed.

  Lemma ψ_equiv n a : Divides_Irred n a <-> Divides (Irred n) a.
  Proof.
    unfold Divides_Irred. cbn. split.
    - intros [d [->%ψ_repr H]]. apply H.
    - intros. exists (inu (Irred n)). rewrite ψ_repr. now split.
  Qed.


  (** ** Coding Lemma for natural numbers *)

  Lemma preThm4_nat A : (forall n, A n \/ ~ A n) ->
  forall n, exists a, forall u, (u < n -> A u <-> Mod (Irred u) a = 0) /\ (Mod (Irred u) a = 0 -> u < n).
  Proof.
    intros Dec_A.
    induction n.
    - exists 1. intros u. split. lia.
      intros [k ]%Mod_divides.
      assert (Irred u > 1). apply irred_Irred.
      destruct k; lia.
    - destruct IHn as [a Ha].
      destruct (Dec_A n) as [A_n | NA_n].
      
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


  Lemma LEM_binary ϕ : binary ϕ -> Δ0 ϕ -> ⊨ ∀∀ ϕ ∨ ¬ ϕ.
  Proof.
    intros binary_ϕ Δ0_ϕ rho d e.
    induction ϕ using form_ind_falsity_on.
    - cbn. tauto.
    - destruct P.
    - apply inversion_bounded_bin in binary_ϕ.
      apply inversion_Δ0_bin in Δ0_ϕ.
      specialize (IHϕ1 (proj1 binary_ϕ) (proj1 Δ0_ϕ)).
      specialize (IHϕ2 (proj2 binary_ϕ) (proj2 Δ0_ϕ)).
      destruct b.
      all: fold sat in *; cbn in *; tauto.
    - cbn. eapply Peano.eq_dec. apply axioms.
    - inversion Δ0_ϕ.
  Qed.


  Lemma LEM_bounded_exist_sat ϕ : Δ0 ϕ -> binary ϕ ->
    ⊨ ∀∀ (∃ $0 ⧀ $2 ∧ ϕ) ∨ ¬ (∃ $0 ⧀ $2 ∧ ϕ).
  Proof.
    intros Δ0_ϕ binary_ϕ ρ N.
    pose (Φ := ∀ (∃ $0 ⧀ $2 ∧ ϕ) ∨ ¬ (∃ $0 ⧀ $2 ∧ ϕ)).
    assert (H : forall d rho, (d.:rho) ⊨ Φ).
    apply induction. apply axioms.
    repeat solve_bounds.
    eapply bounded_up. apply binary_ϕ. lia.
    eapply bounded_up. apply binary_ϕ. lia.
    - intros rho y. cbn. right.
      now intros (? & ?%nolessthen_zero & ?).
    - intros n IHN rho y. cbn.
      destruct (IHN rho y) as [IH|IH]; fold sat in *; cbn in IH.
      + left. destruct IH as [d Hd]. exists d. split.
        ++ destruct Hd as [[k ->] _]. exists (iσ k). 
          now rewrite add_rec_r.
        ++ eapply bound_ext. apply binary_ϕ.
          2 : apply Hd.
          intros [|[]]; solve_bounds.
      + specialize (LEM_binary ϕ binary_ϕ Δ0_ϕ) as lem_ϕ.
        destruct (lem_ϕ (fun _ => i0) y n) as [HN|HN].
        ++ left. exists n. split.
          exists i0. now rewrite add_zero_r.
          eapply bound_ext. apply binary_ϕ.
          2 : apply HN.
          intros [|[]]; solve_bounds.
        ++ right. intros H. apply IH.
          destruct H as (x & Hx1%lt_S & Hx2).
          exists x. split.
          destruct Hx1 as [| ->]. assumption.
          exfalso. apply HN.
          eapply bound_ext. apply binary_ϕ.
          2 : apply Hx2.
          intros [|[]]; solve_bounds.
          eapply bound_ext. apply binary_ϕ.
          2 : apply Hx2.
          intros [|[]]; solve_bounds.
          apply axioms.
      - intros y. specialize (H N (fun _ => N) y).
        fold sat in H; cbn in *. 
        destruct H as [h|h].
        left. destruct h as [d Hd]. 
        exists d. split. apply Hd.
        eapply bound_ext. apply binary_ϕ.
        2 : apply Hd.
        intros [|[]]; solve_bounds.
        right. intros h1. apply h.
        destruct h1 as [d Hd]. 
        exists d. split. apply Hd.
        eapply bound_ext. apply binary_ϕ.
        2 : apply Hd.
        intros [|[]]; solve_bounds.
  Qed.


  Lemma LEM_bounded_exist_sat' ϕ : Δ0 ϕ -> bounded 2 ϕ ->
    ⊨ ∀∀ (∃ $0 ⧀ $2 ∧ ϕ) ∨ (∀ $0 ⧀ $2 --> ¬ ϕ).
  Proof.
    intros Δ0_ϕ binary_ϕ ρ N.
    pose (Φ := ∀ (∃ $0 ⧀ $2 ∧ ϕ) ∨ (∀ $0 ⧀ $2 --> ¬ ϕ)).
    assert (H : forall d rho, (d.:rho) ⊨ Φ).
    apply induction. apply axioms.
    repeat solve_bounds.
    eapply bounded_up. apply binary_ϕ. lia.
    eapply bounded_up. apply binary_ϕ. lia.
    - intros rho y. cbn. right.
      now intros ? ?%nolessthen_zero.
    - intros n IHN rho y. cbn.
      destruct (IHN rho y) as [IH|IH]; fold sat in *; cbn in IH.
      + left. destruct IH as [d Hd]. exists d. split.
        ++ destruct Hd as [[k ->] _]. exists (iσ k). 
          now rewrite add_rec_r.
        ++ eapply bound_ext. apply binary_ϕ.
          2 : apply Hd.
          intros [|[]]; solve_bounds.
      + specialize (LEM_binary ϕ binary_ϕ Δ0_ϕ) as lem_ϕ.
        destruct (lem_ϕ (fun _ => i0) y n) as [HN|HN].
        ++ left. exists n. split.
          exists i0. now rewrite add_zero_r.
          eapply bound_ext. apply binary_ϕ.
          2 : apply HN.
          intros [|[]]; solve_bounds.
        ++ right. intros x [LT| ->]%lt_S.
            specialize (IH _ LT).
            intros nH. apply IH.
            eapply bound_ext. apply binary_ϕ.
            2 : apply nH.
            intros [|[]]; solve_bounds.
            intros nH. apply HN.
            eapply bound_ext. apply binary_ϕ.
            2 : apply nH.
            intros [|[]]; solve_bounds.
            apply axioms.
      - intros y. specialize (H N (fun _ => N) y).
        fold sat in H; cbn -[Q] in *. 
        destruct H as [h|h].
        left. destruct h as [d Hd]. 
        exists d. split. apply Hd.
        eapply bound_ext. apply binary_ϕ.
        2 : apply Hd.
        intros [|[]]; solve_bounds.
        right. intros d Hd. 
        specialize (h d Hd).
        intros nH. apply h.
        eapply bound_ext. apply binary_ϕ.
        2 : apply nH.
        intros [|[]]; solve_bounds.
  Qed.


  Corollary LEM_bounded_exist {ϕ} sigma : Δ0 ϕ -> binary ϕ ->
  forall b x, (x .: b .: sigma) ⊨ (∃ $0 ⧀ $2 ∧ ϕ) \/ ~ (x .: b .: sigma) ⊨ (∃ $0 ⧀ $2 ∧ ϕ).
  Proof.
    intros Δ0_ϕ binary_ϕ b y.
    specialize (LEM_bounded_exist_sat _ Δ0_ϕ binary_ϕ) as Hb.
    destruct (Hb (fun _ => b) b y) as [h|h]; fold sat in *; cbn in h.
    left. destruct h as [d Hd].
    exists d. split. apply Hd.
    eapply bound_ext. apply binary_ϕ. 2 : apply Hd.
    intros [|[]]; solve_bounds.
    right. intros h1. apply h.
    destruct h1 as [d Hd].
    exists d. split. apply Hd.
    eapply bound_ext. apply binary_ϕ. 2 : apply Hd.
    intros [|[]]; solve_bounds.
  Qed.


  Lemma preThm4 α : Δ0 α -> binary α ->
     forall n rho, rho ⊨ ∀ ∃ ∀ $0 ⧀ (num n) --> (∃ $0 ⧀ $3 ∧ α) <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).
  Proof.
    intros Δ0_α binary_α n rho b.

    enough (Dec_A : forall n, (fun _ => b) ⊨ (∃ $0 ⧀ $2 ∧ α)[(num n)..] \/ ~ (fun _ => b) ⊨ (∃ $0 ⧀ $2 ∧ α)[(num n)..] ).
    - cbn in Dec_A.

    destruct (preThm4_nat _ Dec_A n) as [a Ha].

    exists (inu a).
    intros u' Hu. cbn in Hu.
    rewrite num_subst in Hu.
    setoid_rewrite eval_num in Hu.
    apply lessthen_num in Hu. 2: apply axioms.
    destruct Hu as [u [Hu ->]].
    split.
    + intros α_u.
      cbn in α_u. setoid_rewrite <-switch_up_num in α_u.
      exists (inu (Irred u)). split. 
      { now apply ψ_repr. }
      apply Divides_num.
      apply Ha. 
      { apply Hu. }
      destruct α_u as [d [Hd α_u]].
      exists d. split; auto.
      eapply bound_ext. 3: apply α_u.
      { eapply subst_bound; eauto.
      intros [|[]]; solve_bounds. cbn.
      rewrite num_subst.
      apply closed_num. }
      intros []; solve_bounds.
    + cbn. 
      intros [d [->%ψ_repr H]].
      apply Divides_num, (proj1 (Ha _)) in H; auto.
      setoid_rewrite <-switch_up_num.
      destruct H as [d [Hd α_u]].
      exists d. split; auto.
      eapply bound_ext. 3: apply α_u.
      { eapply subst_bound; eauto.
      intros [|[]]; solve_bounds. cbn.
      rewrite num_subst.
      apply closed_num. }
      intros []; solve_bounds.
    - intros m. 
      destruct (LEM_bounded_exist (fun _ => b) Δ0_α binary_α b (inu m)) as [h|h]; cbn in h. 
      + left. destruct h as [d Hd].
        exists d. cbn. split. apply Hd.
        rewrite switch_up_num.
        eapply bound_ext. apply binary_α.
        2 : apply Hd.
        intros [|[]]; solve_bounds.
      + right. intros h1. apply h.
        destruct h1 as [d Hd].
        exists d. cbn. split. apply Hd.
        rewrite switch_up_num in Hd.
        eapply bound_ext. apply binary_α.
        2 : apply Hd.
        intros [|[]]; solve_bounds.
  Qed.


Lemma preThm4' α : Δ0 α -> unary α -> 
  (forall n, (fun _ => inu n) ⊨ α \/ ~ (fun _ => inu n) ⊨ α) ->
  forall n rho, rho ⊨ ∃ ∀ $0 ⧀ (num n) --> α <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3).
Proof.
  intros Δ0_α unary_α Dec_A n.
  edestruct (preThm4_nat _ Dec_A n) as [a Ha].

  exists (inu a).
  intros u' Hu. cbn in Hu.
  rewrite num_subst in Hu.
  setoid_rewrite eval_num in Hu.
  apply lessthen_num in Hu. 2: apply axioms.
  destruct Hu as [u [Hu ->]].
  split.
  + intros α_u.
    exists (inu (Irred u)). split.
    { now apply ψ_repr. }
    apply Divides_num.
    apply Ha; [apply Hu |].
    eapply bound_ext. 3: apply α_u.
    * apply unary_α.
    * intros []; solve_bounds.
  + cbn. 
    intros [d [->%ψ_repr H]].
    apply Divides_num, (proj1 (Ha _)) in H; auto.
    eapply bound_ext. 3: apply H.
    * apply unary_α.
    * intros []; solve_bounds.
Qed.







Section Hypoth.

  Variable nonStd : ~ stdModel D I.
  Variable stable_std : forall x, stable (std x).

  (** ** Coding Lemma for non-standard Models. *)

  (* We use the numbering from Smith, therefore calling it Thm4. *)
  
  Theorem Thm4 α : Δ0 α -> bounded 2 α ->
    ~ ~ forall b, exists a, forall n rho, (inu n .: a .: b .: rho) ⊨ ((∃ $0 ⧀ $3 ∧ α) <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).
  Proof.
    intros Δ0_α binary_α.
    assert (forall n rho, (inu n .: rho) ⊨ ∀ ∃ ∀ $0 ⧀ $3 --> (∃ $0 ⧀ $3 ∧ α) <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3) ) as H.
    intros n rho.
    rewrite <-switch_num. cbn -[sat].
    cbn. rewrite num_subst, num_subst, num_subst.
    assert (ψ[var] = ψ[up (up (up (up (num n)..)))] ) as <-.
    eapply bounded_subst. apply Hψ.
    intros [|[]]; try now intros. lia.
    assert (α[var] = α[up (up (up (up (num n)..)))] ) as <-.
    eapply bounded_subst. apply binary_α.
    intros [|[]]; try now intros. lia.
    rewrite !subst_var.
    apply preThm4; auto.

    apply Overspill_DN in H.
    - apply (DN_implication H).
      apply DN. clear H.
      intros (e & He1 & He2) b.
      specialize (He2 (fun _ => i0) b) as [a Ha]; fold sat in Ha; cbn in Ha.
      exists a. intros n rho.
      assert (inu n i⧀ e) as Hne. now apply num_lt_nonStd.
      specialize (Ha _ Hne) as [Ha1 Ha2].
      split; cbn.
      + intros [k Hk]. destruct Ha1 as [d Hd].
        exists k. split. apply Hk.
        eapply bound_ext. apply binary_α. 2: apply Hk.
        intros [|[]]; try now intros. lia.
        exists d. split.
        eapply bound_ext. apply Hψ. 2: apply Hd.
        intros [|[]]; try now intros. lia.
        apply Hd.
      + intros [k Hk]. destruct Ha2 as [d Hd].
        exists k. split.
        eapply bound_ext. apply Hψ. 2: apply Hk.
        intros [|[]]; try now intros. lia.
        apply Hk.
        exists d. split. apply Hd.
        eapply bound_ext. apply binary_α. 2: apply Hd.
        intros [|[]]; try now intros. lia.

    - repeat solve_bounds.
      all: eapply bounded_up; try apply binary_α; try apply Hψ.
      all: lia.
    - assumption.
    - assumption.
  Qed.

  (** ** Potentiall existence of a number for which divisibility is not decidable. *)

  Lemma Thm5 : Insep -> ~ ~ exists d : D, (Dec (fun n => Divides_Irred n d) ) -> False.
  Proof.
    intros (α & β & Ha1 & Ha0 & Hb1 & Hb0 & Disj & Insepa).
    pose (phi := (∀ $0 ⧀ $1 --> ∀ $0 ⧀ $2 --> ∀ $0 ⧀ $3 --> ¬ (α[$1..] ∧ β[$2..]) ) ).

    enough (forall n rho, ((inu n).:rho) ⊨ phi ) as H.
    apply Overspill_DN in H.
    - apply (DN_implication H).
      apply (DN_implication (Thm4 α Ha0 Ha1)).
      apply DN. clear H.
      intros thm4 [e He].
      destruct (thm4 e) as [a Ha].
      exists a. intros Dec_div_a.
      eapply (Insepa _ Dec_div_a).

      + intros n A_n.
        specialize (Ha n (fun _ => e)) as [Ha _].
        cbn in Ha. destruct Ha as [ d [H1 H2] ].
        assert (N⊨ (∃α)[(num n)..]) as A_n'.
        { intros rho. eapply soundness. 
          - apply A_n.
          - apply Q_std_axioms.
        }
        apply Σ1_complete' in A_n'; auto.
        destruct A_n' as [m Hm].
        exists (inu m). split.
        apply num_lt_nonStd. apply He.
        rewrite <-!switch_num.
        apply soundness in Hm.
        rewrite !switch_num, <-switch_up_num, <-switch_num.
        apply Hm.
        intros ??. apply axioms. now constructor.

        exists d. split.
        eapply bound_ext. apply Hψ. 2: apply H1.
        intros [|[]]; try reflexivity; lia.
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
        intros ??. apply axioms. now constructor.

        destruct He as [Nstd_e He]. cbn in He.
        cbn in Ha. 
        specialize (Ha n (fun _ => e)) as [_ Ha].
        destruct Ha as [d1 Hd1].
        ++ destruct C_n as [d Hd]. exists d. split.
          eapply bound_ext. apply Hψ. 2 : apply Hd.
          intros [|[]]; solve_bounds.
          apply Hd.
        ++ cbn in Heβ. destruct Heβ as [d2 Hd2].
          rewrite switch_up_num in Hd2.
          eapply He.
          1,2,3: shelve.
          rewrite !sat_comp. split.
          eapply bound_ext. apply Ha1.
          2 : apply Hd1. 
          intros [|[]]; solve_bounds; cbn.
          eapply bound_ext. apply Hb1.
          2 : apply Hd2.
          intros [|[]]; solve_bounds; cbn.
          Unshelve. exact (fun _ => e).
          all : cbn.
          apply Hd2. apply Hd1. now apply num_lt_nonStd.
    - repeat solve_bounds.
      eapply subst_bound; eauto. 
      intros [|[|[|[]]]]; solve_bounds.
      eapply subst_bound; eauto.
      intros [|[|[|[]]]]; solve_bounds.
    - assumption.
    - assumption. 
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
        eapply Δ0_absolutness' with (rho0 := sigma) in Ha.
        apply Ha.
        repeat eapply subst_bound; eauto. 
        now apply subst_Δ0.
        intros [|[]]; solve_bounds. cbn.
        rewrite num_subst.
        apply closed_num.
        intros []; solve_bounds. cbn.
        apply closed_num.
        now repeat apply subst_Δ0.
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
        eapply Δ0_absolutness' with (rho0 := sigma) in Hb.
        apply Hb.
        repeat eapply subst_bound; eauto. 
        now apply subst_Δ0.
        intros [|[]]; solve_bounds. cbn.
        rewrite num_subst.
        apply closed_num.
        intros []; solve_bounds. cbn.
        apply closed_num.
        now repeat apply subst_Δ0.
        apply axioms.
        apply PA_std_axioms.
        apply Hb1.
        intros [|[]]; solve_bounds.
      + apply axioms.
      + apply axioms.
      + apply axioms.
  Qed.


End Hypoth.

End Thm4.


(* Equality in a PA model is stable *)

Lemma eq_stable (x y : D) : stable (x = y).
Proof.
  specialize (@Peano.eq_dec D I axioms x y).
  unfold stable. tauto.
Qed.

Lemma AP_EQ : AP D -> EQ D.
Proof.
  intros apart x y.
  specialize (apart x y) as [].
  now right.
  left. now apply eq_stable.
Qed.

Lemma enumerable_form : enumerable__T form.
Proof.
  eapply enumT_form.
  - apply enum_enumT. exists (fun _ => (Zero::Succ::Plus::Mult::nil)%list ).
    intros []; exists 0; auto.
  - apply enum_enumT. exists (fun _ => nil%list ).
    intros []; exists 0; auto.
  - apply enumT_binop.
  - apply enumT_quantop.
Qed.  

Lemma enum_surj X :
  X -> enumerable__T X -> exists f : nat -> X, surj f.
Proof.
  intros a [g Hg]. unfold enumerator__T in *.
  exists (fun n => match g n with Some x => x | _ => a end).
  intros x. destruct (Hg x) as [n Hn].
  exists n. now rewrite Hn.
Qed.

Fact trunc {A : Prop} {X} :
  (X -> A) -> inhabited X -> A.
Proof.
  intros h [x]; tauto.
Qed.

(** ** Tennebaum's Theorem  *)

(** *** Base Version *)

Definition decDiv := forall n d, 0 < n -> dec (Divides n d).

Theorem Tennenbaum :
  CT_Q -> Insep -> decDiv -> Stable std -> forall e, std e.
Proof.
  intros ct_Q insep decdiv  stable_std.
  enough (~~ forall e, std e).
  { intros e. apply stable_std. firstorder. }
  intros nStd.
  destruct (ct_Q Irred) as [ψ Hψ].
  eapply NNN_N.
  2 : apply (Thm5 ψ Hψ); auto.
  intros [e He]. apply He. constructor.
  intros n. assert (H0 : 0 < Irred n).
  - enough (Irred n > 1) by lia. apply irred_Irred.
  - destruct (decdiv (Irred n) e H0).
    all: rewrite <-(ψ_equiv _ Hψ) in *; now left + right.
Qed.  


Theorem Tennenbaum_enum : 
  CT_Q -> Insep -> Enum D -> AP D ->  Stable std -> forall e, std e.
Proof.
  intros ????. apply Tennenbaum; auto.
  intros ??; now apply dec_Divides.
Qed.



(** *** Witness Operator *)

Theorem Tennenbaum_wo : 
  WO D -> AP D -> CT_Q -> Insep -> Stable std -> forall e, std e.
Proof.
  intros wo deceq%AP_EQ ??. apply Tennenbaum; auto.
  intros ??. now apply dec_Divides'.
Qed.


(** *** Weaker Assumptions *)

Theorem Tennenbaum_strenghened1 : 
  CT_Q -> Insep -> ((decDiv -> False) -> False) -> Stable std -> forall e, std e.
Proof.
  intros ct_Q insep nn_decdiv stable_std.
  enough (~~ forall e, std e).
  { intros e. apply stable_std. firstorder. }
  intros nStd.
  destruct (ct_Q Irred) as [ψ Hψ].
  eapply NNN_N.
  2 : apply (Thm5 ψ Hψ); auto.  
  intros [e He].
  apply (nn_decdiv). intros decdiv.
  apply He. constructor.
  intros n. assert (H0 : 0 < Irred n).
  - enough (Irred n > 1) by lia. apply irred_Irred.
  - destruct (decdiv (Irred n) e H0).
    all: rewrite <-(ψ_equiv _ Hψ) in *; now left + right.
Qed.



Lemma equiv_nat_enumerable (p : nat -> Prop) :
  Definitions.enumerable p -> enumerable p.
Proof.
  intros [f Hf].
  exists (fun n => match f n with Some n => S n | None => 0 end).
  intros x. rewrite (Hf x). split; intros [n Hn]; exists n.
  - now rewrite Hn.
  - destruct (f n); congruence.
Qed.

Section str2.
  Variable enum_Q_prv : forall phi, enumerable (fun n => Q ⊢I phi n).

  Theorem Tennenbaum_strenghened2 : 
    CT_Q -> RT_strong -> RT_weak -> ((WO D -> False) -> False) -> ((EQ D -> False) -> False) ->  Stable std -> forall e, std e.
  Proof.
    intros ct_Q rts rtw nn_wo nn_deceq stable_std.
    apply Tennenbaum_strenghened1; auto.
    - refine (trunc (fun h => Inseparable h _ rts rtw) _).
      + assumption.
      + destruct (enum_surj _ ⊥ enumerable_form). eauto.
    - now apply dec_Divides_temp.
  Qed.
End str2.


(** *** Makholm *)

Section Makholm.

  Variable ψ : form.
  Variable Hψ : binary ψ /\ Σ1 ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (Irred x) ).
  Hypothesis Coding : forall alpha, binary alpha -> Δ0 alpha ->  PA ⊢TI ∀∀∃∀ $0 ⧀ $3 --> (∃ $0 ⧀ $3 ∧ alpha) <--> ∃ (ψ ∧ ∃ $1 ⊗ $0 == $3) .
  
  Theorem Tennebaum_ :
    obj_Insep -> Enum D -> AP D -> forall e, ~~ std e.
  Proof.
    intros (α & β & Ha1 & Ha0 & Hb1 & Hb0 & Disj & Insepa).
    intros enum deceq%AP_EQ e Nstd_e.
    specialize (Coding α Ha1 Ha0).
    - pose (X n := (inu n .: (fun _ => e)) ⊨ ((∃ $0 ⧀ $3 ∧ α) )).
      eapply tsoundness with (rho := (fun _ => e)) in Coding.
      cbn in Coding.
      specialize (Coding e e) as [c Hc].
      assert (forall n : nat, (X n) <-> (inu n .: (fun _ => c)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)) ).
      intros n. split.
      -- specialize (Hc (inu n)) as [H _]. 
         now apply num_lt_nonStd.
         intros X_n. destruct H as [d Hd].
      + destruct X_n as [a Ha].
        exists a. split. apply Ha.
        eapply bound_ext. eauto.
        2 : apply Ha.
        intros [|[]]; solve_bounds.
      + exists d. cbn. split.
        eapply bound_ext. apply Hψ.
        2 : apply Hd.
        intros [|[]]; solve_bounds.
        apply Hd. 
        -- specialize (Hc (inu n)) as [_ H]. 
           now apply num_lt_nonStd.
           intros H_n. destruct H as [d Hd].
      + destruct H_n as [a Ha].
        exists a. split.
        eapply bound_ext. apply Hψ.
        2 : apply Ha.
        intros [|[]]; solve_bounds.
        apply Ha.
      + exists d. cbn. split. apply Hd.
        eapply bound_ext. eauto.
        2 : apply Hd.
        intros [|[]]; solve_bounds.
        -- apply (Insepa X).
      + constructor. intros n.
        destruct (dec_Divides (Irred n) c) as [h|h]; auto.
        ++ enough (Irred n > 1) by lia.
           apply irred_Irred.
        ++ left. apply H, ψ_equiv; auto.
        ++ right. intros nh%H. apply h.
           apply ψ_equiv in nh; auto.
      + intros n [m Hm]%Σ1_complete'; auto. exists (inu m).
        cbn. split.
        now apply num_lt_nonStd.
        rewrite <-switch_up_num, <-switch_num.
        eapply soundness; eauto.
        intros ??; apply axioms. now constructor.
      + intros n [B_n%Σ1_complete X_n]; auto.
        eapply tsoundness with (rho := (fun _ => e)) in Disj; auto.
        cbn in Disj. apply Disj.
        exists (inu n). split.
        ++ specialize X_n as [d [_ Hd]]; cbn in Hd.
           rewrite <-switch_up_num in Hd.
           exists d. rewrite <-switch_up_num. apply Hd.
        ++ apply soundness in B_n.
           specialize (B_n D I) as [d Hd].
           intros ??. apply axioms. now constructor.
           exists d. rewrite <-switch_up_num. apply Hd.
        -- intros ??. now apply axioms.
  Qed.

End Makholm.


(** *** McCarty *)

Section McCarty.

  Lemma McCarty_nat p b : 
    ~~ forall x, x < b -> p x \/ ~ p x.
  Proof.
    induction b.
    - intros H. apply H. lia.
    - assert (~~ (p b \/ ~ p b) ) as Hb by tauto.
      eapply DN_implication. apply IHb.
      eapply DN_implication. apply Hb.
      intros nH. apply nH.
      clear Hb IHb nH. intros Hb IHb.
      intros x.
      assert (x < S b <-> x < b \/ x = b) as -> by lia.
      intros [| ->]; intuition.
  Qed.


  Lemma McCarty' ϕ :
    bounded 1 ϕ -> forall x, ~ ~ forall y, y i⧀ x -> (fun _ => y) ⊨ ϕ \/ ~ (fun _ => y) ⊨ ϕ.
  Proof.
    intros H1.
    pose (Φ := ¬¬ ∀ $0 ⧀ $1 --> ϕ ∨ ¬ ϕ).
    assert (forall d rho, (d .: rho) ⊨ Φ) as H.
    apply induction. apply axioms.
    repeat solve_bounds; eapply bounded_up; try apply H1; try lia.
    - intros rho. cbn. intros nH. apply nH.
      now intros y Hy%nolessthen_zero.
    - intros x IHx rho. cbn -[Q] in *.
      specialize (IHx rho). 
      intros nH. apply IHx. intros IH.

      assert (~~ ((x .: rho) ⊨ ϕ \/ ~ (x .: rho) ⊨ ϕ) ) as H' by tauto.
      apply H'. intros H.

      apply nH. intros y.
      rewrite lt_S.
      intros [LT| <-].
      + destruct (IH _ LT) as [h|h].
        left. eapply bound_ext. apply H1. 2 : apply h.
        intros []; solve_bounds.
        right. intros h1. apply h. 
        eapply bound_ext. apply H1. 2 : apply h1.
        intros []; solve_bounds.
      + destruct H as [h|h]. 
        left. eapply bound_ext. apply H1. 2 : apply h.
        intros []; solve_bounds.
        right. intros h1. apply h. 
        eapply bound_ext. apply H1. 2 : apply h1.
        intros []; solve_bounds.
      + apply axioms.
    - intros x. 
      specialize (H x (fun _ => i0)). cbn in H.
      intros nA. apply H. intros nH. apply nA.
      intros y Hy. specialize (nH _ Hy).
      destruct nH as [h|h].
      + left. eapply bound_ext. apply H1. 2: apply h.
        intros []; solve_bounds.
      + right. intros G. apply h. 
        eapply bound_ext. apply H1. 2: apply G.
        intros []; solve_bounds.
  Qed.


  Definition Inform := forall A B, A \/ B -> sum A B.

  Lemma McCarty_ : obj_Insep -> Inform -> forall e, ~~ std e.
  Proof.
    intros (α & β & Ha1 & Ha0 & Hb1 & Hb0 & Disj & Insepa).
    intros info e He.
    assert (H1 : bounded 1 (∃ α)). now solve_bounds.
    specialize (McCarty' (∃ α) H1 e).
    apply DN. intros MC'.
    assert (forall y : D, y i⧀ e -> sum ((fun _ : nat => y) ⊨ (∃ α)) ((fun _ : nat => y) ⊨ (∃ α) -> False)) as H.
    {
      intros y Hy. now apply info, MC'.
    }
    apply (Insepa (fun x => (fun _ : nat => inu x) ⊨ (∃ α) )).
    constructor. intros y. 
    unshelve refine (match (H (inu y) _) with inl A => _ | inr B => _ end).
    - now apply num_lt_nonStd.
    - now left.
    - now right.
    - intros n A_n%Σ1_complete%soundness; auto.
      specialize (A_n _ _ (fun _ => inu n)).
      rewrite switch_num in A_n.
      eapply bound_ext. solve_bounds; eauto.
      2: apply A_n.
      intros []; solve_bounds.
      intros ??. apply axioms. now constructor.
    - intros n [B_n%Σ1_complete%soundness  X_n]; auto.
      eapply tsoundness with (rho := (fun _ => e)) in Disj; auto.
      cbn in Disj. apply Disj.
      exists (inu n). split.
      + destruct X_n as [d Hd].
        exists d. eapply bound_ext. eauto.
        2 : apply Hd.
        intros [|[]]; solve_bounds.
      + edestruct (B_n D I) as [d Hd].
        intros ??. apply axioms; now constructor.
        exists d. rewrite switch_up_num in Hd.
        apply Hd.
  Qed.

End McCarty.

End Tennenbaum.
