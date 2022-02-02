Require Import FOL Peano Tarski Deduction NumberTheory Synthetic DecidabilityFacts Formulas Tennenbaum_diagonal Tennenbaum_insep Makholm McCarty Church Coding.


Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).


Section Variants.

Instance ff : falsity_flag := falsity_on.

Variable D : Type.
Variable I : interp D.
Variable axioms : forall ax, PA ax -> ⊨ ax.
Variable ct : CT_Q.

Hypothesis delta0_definite : forall phi, delta0 phi -> Q ⊢I phi ∨ ¬ phi.

Definition div e d := exists k : D, e i⊗ k = d.
Definition div_num n (d : D) := exists e, inu n i⊗ e = d.
Definition Div_nat (d : D) := fun n => div_num n d.
Definition div_pi ψ n a :=  (inu n .: (fun _ => a)) ⊨ (∃ (ψ ∧ ∃ $1 ⊗ $0 == $3)).
Definition prime_form ψ := bounded 2 ψ /\ (forall x, Q ⊢I ∀ ψ[up (num x)..] <--> $0 == num (Irred x) ).

Lemma Irred_repr :
  exists ψ, prime_form ψ.
Proof.
  destruct (ct Irred) as [phi Hphi].
  exists (∃ phi). split.
  - now constructor.
  - apply Hphi.
Qed.

Fact ψ_equiv n a ψ :
  prime_form ψ -> div_pi ψ n a <-> div_num (Irred n) a.
Proof.
  intros Hψ. unfold div_pi. cbn. split.
  - intros [d [->%ψ_repr H]]; auto.
  - intros. exists (inu (Irred n)). rewrite ψ_repr; auto.
Qed.


Fact MP_Discrete_stable_std :
  MP -> Discrete D -> Stable std.
Proof.
  intros mp [eq]%Discrete_sum e. unfold Stable.
  refine (MP_Dec_stable mp _ _).
  constructor. intros ?; apply eq.
Qed.

Fact stable_Std :
  Stable std -> stable (forall e, std e).
Proof.
  intros H h ?. apply H.
  now apply (DN_chaining h), DN.
Qed.

Lemma Dec_Div_nat_std :
  forall e, std e -> Dec (Div_nat e).
Proof.
  intros e [n <-].
  destruct Irred_repr as [ψ ]; auto.
  constructor; intros x.
  destruct n.
  - left. exists (inu 0).
    now rewrite mult_zero_r.
  - destruct (dec_eq_nat (Mod x (S n)) 0) as [h|nh].
    + left. apply Mod_divides in h.
      destruct h as [k ->].
      exists (inu k). now rewrite inu_mult_hom, mult_comm.
    + right. intros [K HK]. apply nh.
      enough (exists k, inu k = K) as [k <-].
      * apply Mod_divides. exists k.
        rewrite mult_comm, <-inu_mult_hom in HK; auto.
        now apply inu_inj in HK; auto.
      * eapply std_mult'; eauto.
Qed.

Lemma Dec_div_reduction d ψ :
  prime_form ψ -> Dec (Div_nat d) -> Dec (fun n => div_pi ψ n d).
Proof.
  intros Hψ [H].
  constructor. intros n.
  destruct (H (Irred n)) as [h|nh].
  + left. apply ψ_equiv; auto.
  + right. intros [k ]%ψ_equiv; auto. apply nh.
    now exists k.
Qed.

Fact Std_is_Enumerable :
  (forall e, std e) -> Enumerable D.
Proof.
  intros H.
  exists (fun n => Some (inu n)).
  intros d. destruct (H d) as [n <-]; eauto.
Qed.


(* ** Variants of Tennenbaum's Theorem *)

Theorem Tennenbaum1 :
  MP -> Discrete D -> Enumerable D <-> forall e, std e.
Proof.
  intros mp eq. 
  destruct Irred_repr as [ψ ]; auto.
  apply CT_RTs in ct.
  split.
  - intros ?.
    assert (~ exists e, ~ std e) as He.
    { eapply Tennenbaum_diagonal with (ψ:=ψ); eauto. }
    intros e. apply MP_Discrete_stable_std; auto.
    intros nH. apply He. now exists e.
  - intros ?. now apply Std_is_Enumerable.
Qed.

Section Enum.

  Variable surj_form_ : { Φ : nat -> form & surj Φ }.
  Variable enumerable_Q_prv : forall Φ : nat -> form, enumerable (fun n => Q ⊢I (Φ n)).

  Corollary Tennenbaum_insep :
    MP -> Discrete D -> (forall d, ~~Dec (Div_nat d)) -> (forall e, ~~std e).
  Proof.
    intros mp eq DecDiv e He.
    destruct Irred_repr as [ψ ]; auto.
    eapply nonDecDiv; eauto.
    - now apply CT_Inseparable.
    - now apply MP_Discrete_stable_std.
    - now exists e.
    - intros [d Hd]. apply (DecDiv d).
      intros h. apply Hd.
      now apply Dec_div_reduction.
  Qed.

  Theorem Tennenbaum2 :
    MP -> Discrete D -> (forall d, ~~Dec (Div_nat d)) <-> (forall e, std e).
  Proof.
    intros mp eq. split.
    - intros ??. apply MP_Discrete_stable_std; auto.
      eapply Tennenbaum_insep; eauto.
    - intros ??. now apply DN, Dec_Div_nat_std.
  Qed.

End Enum.


Theorem Makholm :
  (exists ψ, prime_form ψ /\ (obj_Coding ψ)) -> obj_Insep -> nonStd D <-> exists d, ~ Dec (Div_nat d).
Proof.
  intros [ψ [H1 H2]] ?. split.
  - eapply Makholm; eauto.
  - intros [d Hd]. exists d.
  now intros ?%Dec_Div_nat_std.
Qed.

Lemma Tennenbaum3 :
  (exists ψ, prime_form ψ /\ (obj_Coding ψ)) -> obj_Insep -> (UC nat bool) -> ~ nonStd D.
Proof.
  intros ??? H.
  assert (nonStd D) as [e He]%Makholm by assumption; auto.
  refine (DN_Div_nat _ _ _ _ _ e _); auto.
Qed.

Lemma UC_Discrete :
  (forall X, UC X bool) -> Discrete D.
Proof.
  intros uc. unfold Discrete.
  enough (Dec_sigT (fun p : D * D => fst p = snd p)) by (constructor; auto).
  apply UC_Def_Dec. apply uc.
  intros [x y]. destruct (@Peano.eq_dec D I axioms x y); now (left + right).
Qed.

Theorem McCarty :
  (exists ψ, prime_form ψ /\ (obj_Coding ψ)) -> obj_Insep -> MP -> (forall X, UC X bool) -> (forall e, std e).
Proof.
  intros ??? H e.
  apply MP_Discrete_stable_std; auto. 
  { now apply UC_Discrete. }
  intros He. apply Tennenbaum3; auto.
  now exists e.
Qed.


End Variants.