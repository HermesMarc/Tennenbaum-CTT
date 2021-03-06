Require Import FOL Peano Tarski Deduction CantorPairing Synthetic DecidabilityFacts NumberTheory Peano.
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

Lemma inversion_bounded_bin α β n b : 
  bounded n (bin b α β) -> bounded n α /\ bounded n β.
Proof.
  intros H. destruct b.
  all: now invert_bounds.
Qed.


(** * PA and Q are consistent in Coq. *)

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



(** * Δ1 Formulas. *)

Class Delta1 : Type :=  
  mk_Delta1{ 
    delta1 : form -> Prop
  ; delta1_Q : forall ϕ s, delta1 ϕ -> bounded 0 (ϕ[s]) -> Q ⊢I ϕ[s] \/ Q ⊢I ¬ ϕ[s]
  ; delta1_HA : forall ϕ, delta1 ϕ -> PA ⊢TI ϕ ∨ ¬ ϕ
  ; delta1_subst : forall ϕ s, delta1 ϕ -> delta1 (ϕ[s])
  }.


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


Fact Faster1 {X} A (x : X) : A <<= x :: A.
Proof.
  firstorder.
Qed.

Fact Faster2 {X} A (x y : X) : A <<= x :: y :: A.
Proof.
  firstorder.
Qed.


Section Delta1.

  Context {Δ1 : Delta1}.

Lemma Q_neg_equiv ϕ s : 
  delta1 ϕ -> bounded 0 ϕ[s] -> (~ Q ⊢I ϕ[s]) <-> Q ⊢I ¬ ϕ[s].
Proof.
  intros d0. split.
    - intros. destruct (delta1_Q ϕ s); tauto.
    - intros H1 H2.
      apply PA_consistent.
      exists Q. split. intros.
      now constructor.
      eapply IE. apply H1. apply H2.
Qed.

(** Results concerning Delta_0 formulas. *)

Section Closed.

  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).
  
  Variable phi : form.
  Variable Hcl : bounded 0 phi.
  Variable H0 : delta1 phi.

  Variable D : Type.
  Variable I : interp D.
  Variable axioms : forall ax, PA ax -> ⊨ ax. 


  Theorem Q_dec_closed_delta1 :
    Q ⊢I phi \/ Q ⊢I ¬ phi.
  Proof.
    setoid_rewrite <-subst_var. cbn.
    apply delta1_Q; auto. 
    now rewrite subst_var.
  Qed.


  Corollary Q_neg_equiv_delta1 : 
    (~ Q ⊢I phi) <-> Q ⊢I ¬ phi.
  Proof.
    setoid_rewrite <-subst_var. cbn.
    apply Q_neg_equiv; auto.
    now rewrite subst_var.
  Qed.


  Corollary dec_closed_delta1: PA ⊢TI phi \/ PA ⊢TI ¬ phi.
  Proof.
    destruct Q_dec_closed_delta1 as [H|H].
    - left. exists Q. split.
      intros; now constructor.
      apply H.
    - right. exists Q. split.
      intros; now constructor.
      apply H. 
  Qed.


  Corollary neg_equiv_delta1 : (~ PA ⊢TI phi) <-> PA ⊢TI ¬ phi.
  Proof.
    split.
    - intros. now destruct dec_closed_delta1.
    - intros [Γ1 []] [Γ2 []].
      apply PA_consistent.
      exists (Γ1 ++ Γ2)%list.
      split. now apply incl_app.
      eapply IE. eapply Weak. apply H1. intuition.
      eapply Weak. apply H3. intuition. 
  Qed.


  (** ** Δ1 Completeness  *)
  Lemma delta1_complete rho : 
    sat interp_nat rho phi -> PA ⊢TI phi.
  Proof.
    intros H. destruct dec_closed_delta1 as [C|C]. assumption.
    specialize (tsoundness C interp_nat rho) as F.
    exfalso. apply F. apply PA_std_axioms. apply H.
  Qed.

  Lemma Q_delta1_complete rho : 
    sat interp_nat rho phi -> Q ⊢I phi.
  Proof.
    intros H. destruct Q_dec_closed_delta1 as [C|C]. assumption.
    specialize (soundness C interp_nat rho) as F.
    exfalso. apply F.
    apply Q_std_axioms. apply H.
  Qed.


  Lemma delta1_complete' rho : 
    sat I rho phi -> PA ⊢TI phi.
  Proof.
    intros H. destruct dec_closed_delta1 as [C|C]. assumption.
    specialize (tsoundness C I rho) as F.
    exfalso. apply F. intuition. apply H.
  Qed.


  Lemma Q_delta1_complete' rho : 
    sat I rho phi -> Q ⊢I phi.
  Proof.
    intros H. destruct Q_dec_closed_delta1 as [C|C]. assumption.
    specialize (soundness C I rho) as F.
    exfalso. apply F. intros ??. apply axioms.
    now constructor.
    apply H.
  Qed.


  (** ** Δ1 Absolutness *)
  Lemma delta1_absolutness' rho : 
    sat I rho phi -> PA⊨ phi.
  Proof.
    intros H. apply tsoundness.
    destruct dec_closed_delta1 as [C|C]. assumption.
    specialize (tsoundness C I rho) as F.
    exfalso. apply F. intuition. apply H.
  Qed.

End Closed.


Notation "N⊨ phi" := (forall rho, @sat _ _ nat interp_nat _ rho phi) (at level 40).


(** ** sigma1 Completeness  *)
Section Sigma1.

  Variable α : form.
  Variable binary_α : binary α.
  Variable delta1_α : delta1 α.

  Lemma sigma1_complete' n :
    N⊨ (∃ α)[(num n)..] -> exists m, Q ⊢I α[up (num n)..][(num m)..].
  Proof.
    intros [m Hm]%(fun h => h (fun _ => 0)).
    rewrite <-switch_nat_num in Hm. exists m.
    eapply Q_delta1_complete; eauto.
    - eapply subst_bound; eauto.
      eapply subst_bound; eauto.
      intros [|[]]; solve_bounds; cbn.
      rewrite num_subst.
      apply closed_num.
      intros [|]; solve_bounds; cbn.
      apply closed_num.
    - rewrite subst_comp.
      now apply delta1_subst.
  Qed.

  Lemma sigma1_complete n :
    N⊨ (∃ α)[(num n)..] -> Q ⊢I (∃ α)[(num n)..].
  Proof.
    intros [m Hm]%sigma1_complete'.
    cbn.
    change (∃ α[up (num n)..]) with (Peano.exist_times 1 (α[up (num n)..])).
    eapply subst_exist_prv; eauto.
    eapply subst_bound; eauto.
    intros [|[]]; solve_bounds. cbn.
    rewrite num_subst.
    apply closed_num.
  Qed.

  Lemma sigma1_complete'' n :
    Q ⊢I (∃ α)[(num n)..] -> exists m, Q ⊢I α[up (num n)..][(num m)..].
  Proof.
    intros H%soundness.
    apply sigma1_complete'.
    specialize (H nat interp_nat).
    intros ?. apply H.
    intros ??. now apply Q_std_axioms.
  Qed.

End Sigma1.


Section Sigma1.

  Variable α : form.
  Variable ternary_α : bounded 3 α.
  Variable delta1_α : delta1 α.

  Lemma sigma1_ternary_complete' n :
    N⊨ (∃∃α)[(num n)..] -> exists a b, Q ⊢I α[up (up (num n)..)][(num b)..][(num a)..].
  Proof.
    intros [a [b Hab]]%(fun h => h (fun _ => 0)).
    rewrite <-!switch_nat_num in Hab. exists a, b.
    eapply Q_delta1_complete; eauto.
    - eapply subst_bound with (N:=1); eauto.
      eapply subst_bound with (N:=2); eauto.
      eapply subst_bound with (N:=3); eauto.
      intros [|[|[]]]; solve_bounds; cbn.
      rewrite !num_subst. apply closed_num.
      intros [|[]]; solve_bounds; cbn.
      apply closed_num.
      intros [|]; solve_bounds; cbn.
      apply closed_num.
    - rewrite !subst_comp.
      now apply delta1_subst.
  Qed.

  Lemma sigma1_ternary_complete n :
    N⊨ (∃∃α)[(num n)..] -> Q ⊢I (∃∃α)[(num n)..].
  Proof.
    intros (a & b & Hab)%sigma1_ternary_complete'.
    cbn.
    change (∃∃ α[up (up (num n)..)]) with (Peano.exist_times 2 (α[up (up (num n)..)])).
    rewrite subst_comp in Hab.
    eapply subst_exist_prv; eauto. 
    eapply subst_bound; eauto.
    intros [|[|[]]]; solve_bounds. cbn.
    rewrite !num_subst.
    apply closed_num.
  Qed.

End Sigma1.

End Delta1.