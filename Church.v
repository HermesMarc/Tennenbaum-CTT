Require Import FOL Tarski Deduction Peano Formulas NumberTheory Synthetic DecidabilityFacts.
Require Import Lia.
Require Import Equations.Equations Equations.Prop.DepElim.

Import Vector.VectorNotations.



Notation "x 'el' A" := (List.In x A) (at level 70).
Notation "A '<<=' B" := (List.incl A B) (at level 70).
Notation "x ∣ y" := (exists k, x * k = y) (at level 50).

Definition unary α := bounded 1 α.
Definition binary α := bounded 2 α.



Section ChurchThesis.

Instance ff : falsity_flag := falsity_on.


Definition represents ϕ f := forall x, Q ⊢I ∀ ϕ[up (num x)..] <--> $0 == num (f x).
Definition CT_Q :=
  forall f : nat -> nat, exists ϕ, bounded 2 ϕ /\ inhabited(sigma1 ϕ) /\ represents ϕ f.
Definition WCT_Q :=
  forall f : nat -> nat, ~ ~ exists ϕ, bounded 2 ϕ /\ inhabited(sigma1 ϕ) /\ represents ϕ f.


Definition strong_repr ϕ (p : nat -> Prop) := (forall x, p x -> Q ⊢I ϕ[(num x)..]) /\ (forall x, ~ p x -> Q ⊢I ¬ϕ[(num x)..]).
Definition RT_strong := forall p : nat -> Prop, Dec p -> exists ϕ, bounded 1 ϕ /\ inhabited(sigma1 ϕ) /\ strong_repr ϕ p.
Definition WRT_strong := forall p : nat -> Prop, Dec p ->  ~ ~ exists ϕ, bounded 1 ϕ /\ inhabited(sigma1 ϕ) /\ strong_repr ϕ p.


Definition weak_repr ϕ (p : nat -> Prop) := (forall x, p x <-> Q ⊢I ϕ[(num x)..]).
Definition RT_weak := forall p : nat -> Prop, enumerable p -> exists ϕ, bounded 1 ϕ /\ inhabited(sigma1 ϕ) /\ weak_repr ϕ p.
Definition WRT_weak := forall p : nat -> Prop, enumerable p -> ~ ~ exists ϕ, bounded 1 ϕ /\ inhabited(sigma1 ϕ) /\ weak_repr ϕ p.



Lemma prv_split {p : peirce} α β Gamma :
  Gamma ⊢ α <--> β <-> Gamma ⊢ (α --> β) /\ Gamma ⊢ (β --> α).
Proof.
  split; intros H.
  - split.
    + eapply CE1. apply H.
    + eapply CE2. apply H.
  - now constructor.
Qed.


Lemma up_switch ϕ s t :
  ϕ[(num s)..][(num t)..] = ϕ[up (num t)..][(num s)..].
Proof.
  rewrite !subst_comp. apply subst_ext. intros [|[]]; cbn.
  - now rewrite num_subst.
  - now rewrite !num_subst.
  - reflexivity.
Qed.


Lemma CT_RTs : 
  CT_Q -> RT_strong.
Proof.
  intros ct p Dec_p.
  destruct (Dec_decider_nat _ Dec_p) as [f Hf]. 
  destruct (ct f) as [ϕ [b2 [[s1] H]]].
  pose (Φ := ϕ[(num 0)..]).
  exists Φ. repeat split; unfold Φ.
  { eapply subst_bound; eauto.
    intros [|[]]; solve_bounds. }
  { now apply subst_sigma1. }
  all: intros x; specialize (H x); rewrite up_switch.
  all: eapply AllE with (t := num 0) in H; cbn -[Q] in H.
  all: apply prv_split in H; destruct H as [H1 H2].
  - intros px%Hf. symmetry in px.
    eapply num_eq with (Gamma := Q)(p := intu) in px; [|firstorder].
    eapply IE. apply H2. now rewrite num_subst.
  - intros npx. assert (0 <> f x) as E by firstorder.
    apply num_neq with (Gamma := Q)(p := intu) in E; [|firstorder].
    apply II. eapply IE.
    {eapply Weak; [apply E|now right]. }
    eapply IE; [|apply Ctx; now left].
    rewrite num_subst in H1. eapply Weak; [apply H1|now right].
Qed.


Lemma WCT_WRTs :
  WCT_Q -> WRT_strong.
Proof.
  intros wct p Dec_p.
  destruct (Dec_decider_nat _ Dec_p) as [f Hf]. 
  apply (DN_chaining (wct f)), DN. intros [ϕ [b2 [[s1] H]]].
  pose (Φ := ϕ[(num 0)..]).
  exists Φ. repeat split; unfold Φ.
  { eapply subst_bound; eauto. 
    intros [|[]]; solve_bounds. }
  { now apply subst_sigma1. }
  all: intros x; specialize (H x); rewrite up_switch.
  all: eapply AllE with (t := num 0) in H; cbn -[Q] in H.
  all: apply prv_split in H; destruct H as [H1 H2].
  - intros px%Hf. symmetry in px.
    eapply num_eq with (Gamma := Q)(p := intu) in px; [|firstorder].
    eapply IE. apply H2. now rewrite num_subst.
  - intros npx. assert (0 <> f x) as E by firstorder.
    apply num_neq with (Gamma := Q)(p := intu) in E; [|firstorder].
    apply II. eapply IE.
    {eapply Weak; [apply E|now right]. }
    eapply IE; [|apply Ctx; now left].
    rewrite num_subst in H1. eapply Weak; [apply H1|now right].
Qed.


Lemma CT_RTw :
  CT_Q -> RT_weak.
Proof.
  intros ct p [f Hf]%enumerable_nat.
  destruct (ct f) as [ϕ [b2 [[s1] H]]].
  pose (Φ := ∃ ϕ[(σ $1)..] ).
  exists Φ; split. 2: split.
  - solve_bounds. eapply subst_bound; eauto.
    intros [|[]]; repeat solve_bounds.
  - constructor. now apply Sigma_exists, subst_sigma1. 
  - intros x. rewrite Hf. split.
    + intros [n Hn]. symmetry in Hn.
      fold Φ.
      eapply (@sigma1_complete Φ _ 1) with (rho := fun _ => 0).
      { solve_bounds. eapply subst_bound; eauto.
        intros [|[]]; repeat solve_bounds. }
      { intros [] ?; [apply closed_num|lia]. } 
      exists n. specialize (H n).
      apply soundness in H.
      unshelve refine (let H := (H nat interp_nat (fun _ => 0)) _ in _ ).
      apply Q_std_axioms.
      cbn in H. specialize (H (S x)) as [_ H2].
      rewrite eval_num, inu_nat_id in *.
      apply H2 in Hn.
      rewrite !sat_comp in *.
      eapply bound_ext.
      apply b2. 2: apply Hn.
      intros [|[]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
      all: try lia; reflexivity.
    + intros HQ%soundness. specialize (HQ nat interp_nat (fun _ => 0)).
      destruct HQ as [n Hn].
      apply Q_std_axioms.
      exists n. specialize (H n).
      apply soundness in H.
      unshelve refine (let H := (H nat interp_nat (fun _ => 0)) _ in _ ).
      apply Q_std_axioms.
      cbn in H. specialize (H (S x)) as [H1 _].
      rewrite eval_num, inu_nat_id in *.
      symmetry. apply H1.
      rewrite !sat_comp in Hn. rewrite sat_comp.
      eapply bound_ext.
      apply b2. 2: apply Hn.
      intros [|[]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
      all: try lia; reflexivity.
    Unshelve. now apply Sigma_exists, subst_sigma1.
Qed.


Lemma WCT_WRTw :
  WCT_Q -> WRT_weak.
Proof.
  intros wct p [f Hf]%enumerable_nat.
  apply (DN_chaining (wct f)), DN. intros [ϕ [b2 [[s1] H]]].
  pose (Φ := ∃ ϕ[(σ $1)..] ).
  exists Φ; split. 2: split.
  - solve_bounds. eapply subst_bound; eauto.
    intros [|[]]; repeat solve_bounds.
  - constructor. now apply Sigma_exists, subst_sigma1. 
  - intros x. rewrite Hf. split.
    + intros [n Hn]. symmetry in Hn.
      fold Φ.
      eapply (@sigma1_complete Φ _ 1) with (rho := fun _ => 0).
      { solve_bounds. eapply subst_bound; eauto.
        intros [|[]]; repeat solve_bounds. }
      { intros [] ?; [apply closed_num|lia]. } 
      exists n. specialize (H n).
      apply soundness in H.
      unshelve refine (let H := (H nat interp_nat (fun _ => 0)) _ in _ ).
      apply Q_std_axioms.
      cbn in H. specialize (H (S x)) as [_ H2].
      rewrite eval_num, inu_nat_id in *.
      apply H2 in Hn.
      rewrite !sat_comp in *.
      eapply bound_ext.
      apply b2. 2: apply Hn.
      intros [|[]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
      all: try lia; reflexivity.
    + intros HQ%soundness. specialize (HQ nat interp_nat (fun _ => 0)).
      destruct HQ as [n Hn].
      apply Q_std_axioms.
      exists n. specialize (H n).
      apply soundness in H.
      unshelve refine (let H := (H nat interp_nat (fun _ => 0)) _ in _ ).
      apply Q_std_axioms.
      cbn in H. specialize (H (S x)) as [H1 _].
      rewrite eval_num, inu_nat_id in *.
      symmetry. apply H1.
      rewrite !sat_comp in Hn. rewrite sat_comp.
      eapply bound_ext.
      apply b2. 2: apply Hn.
      intros [|[]]; cbn; rewrite ?num_subst, ?eval_num, ?inu_nat_id in *.
      all: try lia; reflexivity.
    Unshelve. now apply Sigma_exists, subst_sigma1. 
Qed.


End ChurchThesis.