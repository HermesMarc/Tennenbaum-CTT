Require Import FOL Peano Tarski Deduction NumberTheory Synthetic DecidabilityFacts Tennenbaum_diagonal Church Coding.


Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).


Section ChurchThesis.

Instance ff : falsity_flag := falsity_on.


Lemma Irred_repr :
  CT_Q -> exists ψ, binary ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (Irred x) ).
Proof.
  intros ct.
  destruct (ct Irred) as [phi Hphi].
  exists phi. split; apply Hphi.
Qed.


Lemma Tennenbaum1 D (I : interp D) (axioms : forall ax, PA ax -> ⊨ ax) :
  CT_Q -> RT_strong -> MP -> Enumerable D -> Discrete D -> ~ exists e, ~ std e.
Proof.
  intros wct ????.
  apply (DN_remove (Irred_repr wct)). intros [].
  eapply Tennenbaum_diagonal; eauto.
  (*  Tennenbaum.v needs to use the WCT definition from Church.v *)
Admitted.


End ChurchThesis.