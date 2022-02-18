Require Export FOL.
Require Import Lia.
Require Import Vector.
Require Import Equations.Equations Equations.Prop.DepElim.


Local Set Implicit Arguments.
Local Unset Strict Implicit.


(** * Full Syntax *)

Declare Scope syn.
Open Scope syn.

Inductive full_logic_sym : Type :=
| Conj : full_logic_sym
| Disj : full_logic_sym
| Impl : full_logic_sym.

Inductive full_logic_quant : Type :=
| All : full_logic_quant
| Ex : full_logic_quant.

Definition full_operators : operators :=
  {| binop := full_logic_sym ; quantop := full_logic_quant |}.

#[export] Hint Immediate full_operators : typeclass_instances.

Notation "∀ Phi" := (@quant _ _ full_operators _ All Phi) (at level 50) : syn.
Notation "∃ Phi" := (@quant _ _ full_operators _ Ex Phi) (at level 50) : syn.
Notation "A ∧ B" := (@bin _ _ full_operators _ Conj A B) (at level 41) : syn.
Notation "A ∨ B" := (@bin _ _ full_operators _ Disj A B) (at level 42) : syn.
Notation "A '-->' B" := (@bin _ _ full_operators _ Impl A B) (at level 43, right associativity) : syn.
Notation "⊥" := (falsity) : syn.
Notation "¬ A" := (A --> ⊥) (at level 42) : syn.
Notation "A '<-->' B" := ((A --> B) ∧ (B --> A)) (at level 43) : syn.




(** * Tarski Semantics *)

Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  
  (** Semantic notions *)

  Section Semantics.

    Variable domain : Type.

    Class interp := B_I
      {
        i_f : forall f : syms, vec domain (ar_syms f) -> domain ;
        i_P : forall P : preds, vec domain (ar_preds P) -> Prop ;
      }.

    Definition env := nat -> domain.

    Context {I : interp }.
    Fixpoint eval (rho : env) (t : term) : domain :=
      match t with
      | var s => rho s
      | func f v => i_f (Vector.map (eval rho) v)
      end.

    Fixpoint sat {ff : falsity_flag} (rho : env) (phi : form) : Prop :=
      match phi with
      | atom P v => i_P (Vector.map (eval rho) v)
      | falsity => False
      | bin Impl phi psi => sat rho phi -> sat rho psi
      | bin Conj phi psi => sat rho phi /\ sat rho psi
      | bin Disj phi psi => sat rho phi \/ sat rho psi
      | eq t s => (eval rho t) = (eval rho s)
      | quant Ex phi => exists d : domain, sat (d .: rho) phi
      | quant All phi => forall d : domain, sat (d .: rho) phi
      end.

  End Semantics.

End Tarski.


Arguments sat {_ _ _ _ _} _ _, {_ _ _} _ {_} _ _.
Arguments interp {_ _} _, _ _ _.


Notation "p ⊨ phi" := (sat _ p phi) (at level 20).
Notation "p ⊫ A" := (forall psi, List.In psi A -> sat _ p psi) (at level 20).

Section Defs.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Definition valid_ctx A phi := forall D (I : interp D) rho, (forall psi, List.In psi A -> rho ⊨ psi) -> rho ⊨ phi.
  Definition valid phi := forall D (I : interp D) rho, rho ⊨ phi.
  Definition valid_L A := forall D (I : interp D) rho, rho ⊫ A.
  Definition satis phi := exists D (I : interp D) rho, rho ⊨ phi.
  Definition fullsatis A := exists D (I : interp D) rho, rho ⊫ A.

End Defs.


Section fixb.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.
  
  Fixpoint impl (A : list form) phi :=
    match A with
    | List.nil => phi
    | List.cons psi A => bin Impl psi (impl A phi)
    end.

End fixb.

Notation "A ==> phi" := (impl A phi) (right associativity, at level 55).




Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  
  Variable D : Type.
  Variable I : interp D.

  
  
  Section Substs.
        
    Lemma eval_ext rho xi t :
      (forall x, rho x = xi x) -> eval rho t = eval xi t.
    Proof.
      intros H. induction t; cbn.
      - now apply H.
      - f_equal. apply map_ext_in. now apply IH.
    Qed.

    Lemma eval_comp rho xi t :
      eval rho (subst_term xi t) = eval (xi >> eval rho) t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - f_equal. rewrite map_map. apply map_ext_in, IH.
    Qed.

    Lemma sat_ext {ff : falsity_flag} rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi <-> xi ⊨ phi.
    Proof.
      induction phi  as [ | b P v | | | ] in rho, xi |- *; cbn; intros H.
      - reflexivity.
      - erewrite map_ext; try reflexivity. intros t. now apply eval_ext.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b0; intuition.
      - now rewrite !(@eval_ext rho xi).
      - destruct q.
        + split; intros H' d; eapply IHphi; try apply (H' d). 1,2: intros []; cbn; intuition.
        + split; intros [d H']; exists d; eapply IHphi; try apply H'. 1,2: intros []; cbn; intuition.
    Qed.

    Lemma sat_ext' {ff : falsity_flag} rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi -> xi ⊨ phi.
    Proof.
      intros Hext H. rewrite sat_ext. exact H.
      intros x. now rewrite (Hext x).
    Qed.

    Lemma sat_comp {ff : falsity_flag} rho xi phi :
      rho ⊨ (subst_form xi phi) <-> (xi >> eval rho) ⊨ phi.
    Proof.
      induction phi as [ | b P v | | | ] in rho, xi |- *; cbn.
      - reflexivity.
      - erewrite map_map, map_ext; try reflexivity. intros t. apply eval_comp.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b0; intuition.
      - now rewrite !eval_comp.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext. 2, 4: apply (H d).
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext. 2, 4: apply H.
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
    Qed.

    Lemma sat_subst {ff : falsity_flag} rho sigma phi :
      (forall x, eval rho (sigma x) = rho x) -> rho ⊨ phi <-> rho ⊨ (subst_form sigma phi).
    Proof.
      intros H. rewrite sat_comp. apply sat_ext. intros x. now rewrite <- H.
    Qed.

    Lemma sat_single {ff : falsity_flag} (rho : nat -> D) (Phi : form) (t : term) :
      (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
    Proof.
      rewrite sat_comp. apply sat_ext. now intros [].
    Qed.

    Lemma impl_sat {ff : falsity_flag} A rho phi :
      sat rho (A ==> phi) <-> ((forall psi, List.In psi A -> sat rho psi) -> sat rho phi).
    Proof.
      induction A; cbn; firstorder congruence.
    Qed.

    Lemma impl_sat' {ff : falsity_flag} A rho phi :
      sat rho (A ==> phi) -> ((forall psi, List.In psi A -> sat rho psi) -> sat rho phi).
    Proof.
      eapply impl_sat.
    Qed.
    
  End Substs.



  (** Results for bounded formulas. *)
  
  Section Ext.


    Lemma bounded_eval_t n t sigma tau :
      (forall k, k < n -> sigma k = tau k) -> bounded_t n t -> eval sigma t = eval tau t.
    Proof.
      intros H. induction 1; cbn; auto.
      f_equal. now apply Vector.map_ext_in.
    Qed.

    
    Lemma bound_ext {ff : falsity_flag} N phi rho sigma :
      bounded N phi -> (forall n, n < N -> rho n = sigma n) -> (rho ⊨ phi <-> sigma ⊨ phi).
    Proof.
      induction 1 in sigma, rho |- *; cbn; intros HN; try tauto.
      - enough (map (eval rho) v = map (eval sigma) v) as E. now setoid_rewrite E.
        apply Vector.map_ext_in. intros t Ht.
        eapply bounded_eval_t; try apply HN. now apply H.
      - destruct binop; now rewrite (IHbounded1 rho sigma), (IHbounded2 rho sigma).
      - now rewrite !(@bounded_eval_t n _ rho sigma).
      - destruct quantop.
        + split; intros Hd d; eapply IHbounded.
          all : try apply (Hd d); intros [] Hk; cbn; auto.
          symmetry. all: apply HN; lia.
        + split; intros [d Hd]; exists d; eapply IHbounded.
          all : try apply Hd; intros [] Hk; cbn; auto.
          symmetry. all: apply HN; lia.
    Qed.
    

    Corollary sat_closed {ff : falsity_flag} rho sigma phi :
      bounded 0 phi -> rho ⊨ phi <-> sigma ⊨ phi.
    Proof.
      intros H. eapply bound_ext. apply H. lia.
    Qed.


    Fixpoint exist_times {ff : falsity_flag} N phi :=
      match N with
      | 0 => phi
      | S n => ∃ exist_times n phi
      end.

    Lemma switch_exists {ff : falsity_flag} N phi :
      ∃ exist_times N phi = exist_times N (∃ phi).
    Proof.
      induction N; try reflexivity.
      cbn. now rewrite IHN.
    Qed.
            

    Lemma bounded_S_exists {ff : falsity_flag} N phi : bounded (S N) phi <-> bounded N (∃ phi).
    Proof.
      split; intros H.
      - now constructor.
      - inversion H. apply Eqdep_dec.inj_pair2_eq_dec in H4 as ->; trivial.
        decide equality.
    Qed.

    Lemma bounded_S_forall {ff : falsity_flag} N phi : bounded (S N) phi <-> bounded N (∀ phi).
    Proof.
      split; intros H.
      - now constructor.
      - inversion H. apply Eqdep_dec.inj_pair2_eq_dec in H4 as ->; trivial.
        decide equality.
    Qed.

    
    Lemma subst_exist_sat {ff : falsity_flag} rho phi N :
      rho ⊨ phi -> bounded N phi -> forall rho, rho ⊨ (exist_times N phi).  
    Proof.
      induction N in phi, rho |-*; intros.
      - cbn. eapply sat_closed; eassumption.
      - cbn -[sat]. rewrite switch_exists. apply (IHN (S >> rho)).
        exists (rho 0). eapply sat_ext. 2: apply H.
        now intros [].
        now apply bounded_S_exists.
    Qed.
    

    Fact subst_exist_sat2 {ff : falsity_flag} N : forall rho phi, rho ⊨ (exist_times N phi) -> (exists sigma, sigma ⊨ phi).
    Proof.
      induction N.
      - eauto.
      - intros rho phi [? H]. now apply IHN in H.
    Qed.
    

  End Ext.


End Tarski.
