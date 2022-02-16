Require Import Synthetic.
Require Export List Lia.
Export List.ListNotations.

Module ListAutomationNotations.

  Notation "x 'el' L" := (In x L) (at level 70).
  Notation "A '<<=' B" := (incl A B) (at level 70).

  Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).

  Notation "[ s | p ∈ A ',' P ]" :=
    (map (fun p => s) (filter (fun p => dec P) A)) (p pattern).
  Notation "[ s | p ∈ A ]" :=
    (map (fun p => s) A) (p pattern).

End ListAutomationNotations.
Import ListAutomationNotations.

Require Import FOL Peano Deduction DecidabilityFacts ListEnumerabilityFacts CantorPairing.
Require Import Equations.Equations.

Lemma in_filter_iff X x p (A : list X) :
  x el filter p A <-> x el A /\ p x = true.
Proof. 
  induction A as [|y A]; cbn.
  - tauto.
  - destruct (p y) eqn:E; cbn;
      rewrite IHA; intuition; subst; auto. congruence.
Qed.

Ltac in_collect a :=
  eapply in_map_iff; exists a; split; [ eauto | match goal with [ |- In _ (filter _ _) ] =>  eapply in_filter_iff; split; [ try (rewrite !in_prod_iff; repeat split) | ] | _ => try (rewrite !in_prod_iff; repeat split) end ].

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2;
                                                      [subst | try (eauto || now intros; decide equality)]
  end.

Ltac in_app n :=
  (match goal with
  | [ |- In _ (_ ++ _) ] => 
    match n with
    | 0 => idtac
    | 1 => eapply in_app_iff; left
    | S ?n => eapply in_app_iff; right; in_app n
    end
  | [ |- In _ (_ :: _) ] => match n with 0 => idtac | 1 => left | S ?n => right; in_app n end
  end) || (repeat (try right; eapply in_app_iff; right)).

Lemma in_concat_iff A l (a:A) : a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
  induction l; cbn.
  - intuition. now destruct H. 
  - rewrite in_app_iff, IHl. clear. firstorder subst. auto.
Qed.

Lemma list_enumerator_enumerable X L :
  list_enumerator__T L X -> enumerable__T X.
Proof.
  intros H. exists (fun n => let (n, m) := decode n in nth_error (L n) m).
  intros x. rewrite list_enumerator_to_enumerator. apply H.
Qed.

Section Enumerability.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Variable list_Funcs : nat -> list syms.
  Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.
  Hypothesis cum_Funcs : cumulative list_Funcs.

  Variable list_Preds : nat -> list preds.
  Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.
  Hypothesis cum_Preds : cumulative list_Preds.

  Variable list_binop : nat -> list binop.
  Hypothesis enum_binop' : list_enumerator__T list_binop binop.
  Hypothesis cum_binop : cumulative list_binop.

  Variable list_quantop : nat -> list quantop.
  Hypothesis enum_quantop' : list_enumerator__T list_quantop quantop.
  Hypothesis cum_quantop : cumulative list_quantop.

  Fixpoint vecs_from X (A : list X) (n : nat) : list (vec X n) :=
    match n with
    | 0 => [Vector.nil X]
    | S n => [ Vector.cons X x _ v | (x,  v) ∈ (A × vecs_from X A n) ]
    end.

  Fixpoint L_term n : list term :=
    match n with
    | 0 => []
    | S n => L_term n ++ var n :: concat ([ [ func F v | v ∈ vecs_from _ (L_term n) (ar_syms F) ] | F ∈ list_Funcs n])
    end.

  Lemma L_term_cml :
    cumulative L_term.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma list_prod_in X Y (x : X * Y) A B :
    x el (A × B) -> exists a b, x = (a , b) /\ a el A /\ b el B.
  Proof.
    induction A; cbn.
    - intros [].
    - intros [H | H] % in_app_or. 2: firstorder.
      apply in_map_iff in H as (y & <- & Hel). exists a, y. tauto.
  Qed.

  Lemma vecs_from_correct X (A : list X) (n : nat) (v : vec X n) :
    (forall x, vec_in x v -> x el A) <-> v el vecs_from X A n.
  Proof.
    induction n; cbn.
    - split.
      + intros. left. now dependent elimination v.
      + intros [<- | []] x H. inversion H.
    - split.
      + intros. dependent elimination v. in_collect (pair h t); destruct (IHn t).
        eauto using vec_inB. apply H0. intros x Hx. apply H. now right. 
      + intros Hv. apply in_map_iff in Hv as ([h v'] & <- & (? & ? & [= <- <-] & ? & ?) % list_prod_in).
        intros x H. inversion H; subst; destruct (IHn v'); eauto. apply H3; trivial. now resolve_existT.
  Qed.

  Lemma vec_forall_cml X (L : nat -> list X) n (v : vec X n) :
    cumulative L -> (forall x, vec_in x v -> exists m, x el L m) -> exists m, v el vecs_from _ (L m) n.
  Proof.
    intros HL Hv. induction v; cbn.
    - exists 0. tauto.
    - destruct IHv as [m H], (Hv h) as [m' H']. 1,3: eauto using vec_inB.
      + intros x Hx. apply Hv. now right.
      + exists (m + m'). in_collect (pair h v). 1: apply (cum_ge' (n:=m')); intuition lia.
      apply vecs_from_correct. rewrite <- vecs_from_correct in H. intros x Hx.
      apply (cum_ge' (n:=m)). all: eauto. lia.
  Qed.

  Lemma enum_term :
    list_enumerator__T L_term term.
  Proof with try (eapply cum_ge'; eauto; lia).
    intros t. induction t using term_rect.
    - exists (S x); cbn. apply in_app_iff. right. now left.
    - apply vec_forall_cml in H as [m H]. 2: exact L_term_cml. destruct (enum_Funcs' F) as [m' H'].
      exists (S (m + m')); cbn. in_app 3. eapply in_concat_iff. eexists. split. 2: in_collect F...
      apply in_map. rewrite <- vecs_from_correct in H |-*. intros x H''. specialize (H x H'')...
  Qed.

  Lemma enumT_term :
    enumerable__T term.
  Proof.
    eapply list_enumerator_enumerable. apply enum_term.
  Qed.

  Fixpoint L_form {ff : falsity_flag} n : list form :=
    match n with
    | 0 => match ff with falsity_on => [falsity] | falsity_off => [] end
    | S n => L_form n
              ++ concat ([ [ atom P v | v ∈ vecs_from _ (L_term n) (ar_preds P) ] | P ∈ list_Preds n])
              ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (L_form n × L_form n) ] | op ∈ list_binop n])
              ++ [ t == t' | (t, t') ∈ (L_term n × L_term n) ]
              ++ concat ([ [ quant op phi | phi ∈ L_form n ] | op ∈ list_quantop n])
    end.

  Lemma L_form_cml {ff : falsity_flag} :
    cumulative L_form.
  Proof.
    intros ?; cbn; eauto.
  Qed.

  Lemma enum_form {ff : falsity_flag} :
    list_enumerator__T L_form form.
  Proof with (try eapply cum_ge'; eauto; lia).
    intros phi. induction phi.
    - exists 1. cbn; eauto.
    - destruct (enum_Preds' P) as [m Hm], (vec_forall_cml term L_term _ v) as [m' Hm']; eauto using enum_term.
      exists (S (m + m')); cbn. in_app 2. eapply in_concat_iff. eexists. split.
      2: in_collect P... eapply in_map. rewrite <- vecs_from_correct in *. intuition...
    - destruct (enum_binop' b0) as [m Hm], IHphi1 as [m1], IHphi2 as [m2]. exists (1 + m + m1 + m2). cbn.
      in_app 3. apply in_concat. eexists. split. apply in_map... in_collect (pair phi1 phi2)...
    - destruct (enum_term t) as [n Hn], (enum_term t0) as [n' Hn']. exists (S (n + n')). cbn.
      in_app 4. apply in_map_iff. exists (t, t0). split; trivial. apply in_prod_iff. split...
    - destruct (enum_quantop' q) as [m Hm], IHphi as [m' Hm']. exists (1 + m + m'). cbn.
      in_app 5. apply in_concat. eexists. split. apply in_map... in_collect phi...
  Qed.

  Lemma enumT_form :
    enumerable__T form.
  Proof.
    eapply list_enumerator_enumerable. apply enum_form.
  Qed.

End Enumerability.

Variable surj_form_ : { Φ : nat -> form & surj Φ }.
Variable enumerable_Q_prv : forall Φ : nat -> form, enumerable (fun n => Q ⊢I (Φ n)).
