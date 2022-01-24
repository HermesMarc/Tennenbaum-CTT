Require Import FOL Peano Tarski Deduction NumberTheory Synthetic DecidabilityFacts Tennenbaum_diagonal Church Coding.


Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).


Section Variants.

Instance ff : falsity_flag := falsity_on.

Variable D : Type.
Variable I : interp D.
Variable axioms : forall ax, PA ax -> ⊨ ax.

Lemma Irred_repr :
  CT_Q -> exists ψ, bounded 3 ψ /\ (forall x, Q ⊢I ∀ (∃ ψ)[up (num x)..] <--> $0 == num (Irred x) ).
Proof.
  intros ct.
  destruct (ct Irred) as [phi Hphi].
  exists phi. split; apply Hphi.
Qed.

Definition div e d := exists k : D, e i⊗ k = d.
Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
Definition Div_nat (d : D) := fun n => div_num n d.
Definition div_pi ψ n a :=  (inu n .: (fun _ => a)) ⊨ (∃ ((∃ ψ) ∧ ∃ $1 ⊗ $0 == $3)).



End Variants.