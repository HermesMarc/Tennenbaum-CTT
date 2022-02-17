Require Import Synthetic Dec.
Require Export List Lia.
Export List.ListNotations.

Module ListAutomationNotations.

  Notation "x 'el' L" := (In x L) (at level 70).
  Notation "A '<<=' B" := (incl A B) (at level 70).

  Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).

  Notation "[ s | p ∈ A ',' P ]" :=
    (map (fun p => s) (filter (fun p => if Dec P then true else false) A)) (p pattern).
  Notation "[ s | p ∈ A ]" :=
    (map (fun p => s) A) (p pattern).

End ListAutomationNotations.
Import ListAutomationNotations.

Require Import FOL Peano Deduction DecidabilityFacts ListEnumerabilityFacts CantorPairing Tarski.
Require Import Equations.Equations.
Require Import EqdepFacts.

Lemma in_filter_iff X x p (A : list X) :
  x el filter p A <-> x el A /\ p x = true.
Proof. 
  induction A as [|y A]; cbn.
  - tauto.
  - destruct (p y) eqn:E; cbn;
      rewrite IHA; intuition; subst; auto. congruence.
Qed.

Lemma in_concat_iff A l (a:A) : a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
  induction l; cbn.
  - intuition. now destruct H. 
  - rewrite in_app_iff, IHl. clear. firstorder subst. auto.
Qed.

Ltac in_collect a :=
  eapply in_map_iff; exists a; split; [ eauto | match goal with [ |- In _ (filter _ _) ] =>  eapply in_filter_iff; split; [ try (rewrite !in_prod_iff; repeat split) | eapply Dec_auto; repeat split; eauto ] | _ => try (rewrite !in_prod_iff; repeat split) end ].

Lemma to_dec (P : Prop) `{Dec.dec P} :
  P <-> is_true (Dec P).
Proof.
  split; destruct (Dec P); cbn in *; firstorder congruence.
Qed.

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

End Enumerability.

Definition L_term' :
  nat -> list term.
Proof.
  apply L_term. exact (fun _ => [Zero; Succ; Plus; Mult]).
Defined.

Lemma enum_term' :
  list_enumerator__T L_term' term.
Proof.
  apply enum_term.
  - intros []; exists 0; cbn; tauto.
  - intros n. exists nil. auto.
Qed.

Definition L_form' {ff : falsity_flag} :
  nat -> list form.
Proof.
  apply L_form.
  - exact (fun _ => [Zero; Succ; Plus; Mult]).
  - exact (fun _ => []).
  - exact (fun _ => [Conj; Disj; Impl]).
  - exact (fun _ => [All; Ex]).
Defined.

Lemma enum_form' {ff : falsity_flag} :
  list_enumerator__T L_form' form.
Proof.
  apply enum_form.
  1,3,5,7: intros []; exists 0; cbn; tauto.
  all: intros n; exists nil; auto.
Qed.

Lemma list_enumerator_enumerator__T X L :
  list_enumerator__T L X -> { f | forall x : X, exists n : nat, f n = Some x }.
Proof.
  intros H. exists (fun n => let (n, m) := decode n in nth_error (L n) m).
  intros x. rewrite list_enumerator_to_enumerator. apply H.
Qed.

Theorem surj_form_ :
  { Φ : nat -> form & surj Φ }.
Proof.
  edestruct list_enumerator_enumerator__T as [e He].
  - apply enum_form'.
  - exists (fun n => match e n with Some phi => phi | None => ⊥ end).
    intros phi. destruct (He phi) as [n Hn]. exists n. now rewrite Hn.
Qed.

Lemma dec_vec_in X n (v : vec X n) :
  (forall x, vec_in x v -> forall y, Dec.dec (x = y)) -> forall v', Dec.dec (v = v').
Proof with subst; try (now left + (right; intros[=])).
  intros Hv. induction v; intros v'; dependent elimination v'...
  destruct (Hv h (vec_inB h v) h0)... edestruct IHv.
  - intros x H. apply Hv. now right.
  - left. f_equal. apply e.
  - right. intros H. inversion H. resolve_existT. tauto.
Qed.

Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
  intros v. refine (dec_vec_in _ _ _ _).
Qed.

Section EqDec.
  
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Hypothesis eq_dec_Funcs : eq_dec syms.
  Hypothesis eq_dec_Preds : eq_dec preds.
  Hypothesis eq_dec_binop : eq_dec binop.
  Hypothesis eq_dec_quantop : eq_dec quantop.

  Instance dec_term : eq_dec term.
  Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
    intros t. induction t as [ | ]; intros [|? v']...
    - decide (x = n)... 
    - decide (F = f)... destruct (dec_vec_in _ _ _ X v')...
  Qed.

  Instance dec_falsity : eq_dec falsity_flag.
  Proof.
    intros b b'. unfold Dec.dec. decide equality.
  Qed.

  Lemma eq_dep_falsity b phi psi :
    eq_dep falsity_flag (@form Σ_funcs Σ_preds ops) b phi b psi <-> phi = psi.
  Proof.
    rewrite <- eq_sigT_iff_eq_dep. split.
    - intros H. resolve_existT. reflexivity.
    - intros ->. reflexivity.
  Qed.

  Lemma dec_form_dep {b1 b2} phi1 phi2 : dec (eq_dep falsity_flag (@form _ _ _) b1 phi1 b2 phi2).
  Proof with subst; try (now left + (right; intros ? % eq_sigT_iff_eq_dep; resolve_existT; congruence)).
    unfold dec. revert phi2; induction phi1; intros; try destruct phi2.
    all: try now right; inversion 1. now left.
    - decide (b = b0)... decide (P = P0)... decide (v = v0)... right.
      intros [=] % eq_dep_falsity. resolve_existT. tauto.
    - decide (b = b1)... decide (b0 = b2)... destruct (IHphi1_1 phi2_1).
      + apply eq_dep_falsity in e as ->. destruct (IHphi1_2 phi2_2).
        * apply eq_dep_falsity in e as ->. now left.
        * right. rewrite eq_dep_falsity in *. intros [=]. now resolve_existT.
      + right. rewrite eq_dep_falsity in *. intros [=]. now repeat resolve_existT.
    - decide (b = b0)... decide (t = t1)... decide (t0 = t2)...
    - decide (b = b0)... decide (q = q0)... destruct (IHphi1 phi2).
      + apply eq_dep_falsity in e as ->. now left.
      + right. rewrite eq_dep_falsity in *. intros [=]. now resolve_existT.
  Qed.

  Lemma dec_form {ff : falsity_flag} : eq_dec form.
  Proof.
    intros phi psi. destruct (dec_form_dep phi psi); rewrite eq_dep_falsity in *; firstorder.
  Qed.

End EqDec.

Instance dec_form' {b : falsity_flag} :
  eq_dec form.
Proof.
  apply dec_form; intros x y; unfold Dec.dec; decide equality.
Qed.

Instance list_in_dec X x (A : list X) :
  eq_dec X -> Dec.dec (x el A).
Proof.
  intros d. induction A; cbn.
  - now right.
  - destruct IHA, (d a x); firstorder.
Qed.

Section Enumerability.

  Fixpoint L_ded {p : peirce} {b : falsity_flag} (A : list form) (n : nat) : list form :=
    match n with
    | 0 => A
    | S n =>   L_ded A n ++
    (* II *)   concat ([ [ phi --> psi | psi ∈ L_ded (phi :: A) n ] | phi ∈ L_form' n ]) ++
    (* IE *)   [ psi | (phi, psi) ∈ (L_ded A n × L_form' n) , (phi --> psi el L_ded A n) ] ++
    (* AllI *) [ ∀ phi | phi ∈ L_ded (map (subst_form ↑) A) n ] ++
    (* AllE *) [ phi[t..] | (phi, t) ∈ (L_form' n × L_term' n), (∀ phi) el L_ded A n ] ++
    (* ExI *)  [ ∃ phi | (phi, t) ∈ (L_form' n × L_term' n), (phi[t..]) el L_ded A n ] ++
    (* ExE *)  [ psi | (phi, psi) ∈ (L_form' n × L_form' n),
                     (∃ phi) el L_ded A n /\ psi[↑] el L_ded (phi::(map (subst_form ↑) A)) n ] ++
    (* Exp *)  (match b with falsity_on => fun A =>
                [ phi | phi ∈ L_form' n, ⊥ el @L_ded p falsity_on A n ]
                | _ => fun _ => nil end A) ++
    (* Pc *)   (if p then
                [ (((phi --> psi) --> phi) --> phi) | (pair phi psi) ∈ (L_form' n × L_form' n)]
                else nil) ++
    (* CI *)   [ phi ∧ psi | (phi, psi) ∈ (L_ded A n × L_ded A n) ] ++
    (* CE1 *)  [ phi | (phi, psi) ∈ (L_form' n × L_form' n), phi ∧ psi el L_ded A n] ++
    (* CE2 *)  [ psi | (phi, psi) ∈ (L_form' n × L_form' n), phi ∧ psi el L_ded A n] ++
    (* DI1 *)  [ phi ∨ psi | (phi, psi) ∈ (L_form' n × L_form' n), phi el L_ded A n] ++
    (* DI2 *)  [ phi ∨ psi | (phi, psi) ∈ (L_form' n × L_form' n), psi el L_ded A n] ++
    (* DE *)   [ theta | (phi, (psi, theta)) ∈ (L_form' n × (L_form' n × L_form' n)),
                     theta el L_ded (phi::A) n /\ theta el L_ded (psi::A) n /\ phi ∨ psi el L_ded A n]
    end.

  Ltac inv_collect :=
    progress repeat (match goal with
     | [ H : ?x el concat _ |- _ ] => eapply in_concat_iff in H as (? & ? & ?)
     | [ H : ?x el map _ _ |- _ ] => let x := fresh "x" in eapply in_map_iff in H as (x & ? & ?)
     | [ x : ?A * ?B |- _ ] => destruct x; subst
     | [ H : ?x el filter _ _ |- _ ] => let H' := fresh "H" in eapply in_filter_iff in H as (? & H' % to_dec)
     | [ H : ?x el list_prod _ _ |- _ ] => eapply in_prod_iff in H
     | [ H : _ el _ ++ _ |- _ ] => try eapply in_app_iff in H as []
     | [ H : _ el _ :: _ |- _ ] => destruct H
     end; intuition; subst).

  Lemma enum_prv {p : peirce} {b : falsity_flag} A :
    list_enumerator (L_ded A) (prv A).
  Proof with try (eapply cum_ge'; eauto; lia).
    split.
    - rename x into phi. induction 1; try congruence; subst.
      + destruct IHprv as [m1], (enum_form' phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 2.
        eapply in_concat_iff. eexists. split. 2:in_collect phi... in_collect psi...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (enum_form' psi) as [m3]; eauto.
        exists (1 + m1 + m2 + m3).
        cbn. in_app 3. in_collect (phi, psi)...
      + destruct IHprv as [m]. exists (1 + m). cbn. in_app 4. in_collect phi...
      + destruct IHprv as [m1], (enum_term' t) as [m2], (enum_form' phi) as [m3]. exists (1 + m1 + m2 + m3).
        cbn. in_app 5. in_collect (phi, t)...
      + destruct IHprv as [m1], (enum_term' t) as [m2], (enum_form' phi) as [m3]. exists (1 + m1 + m2 + m3).
        cbn. in_app 6. in_collect (phi, t)...
      + destruct IHprv1 as [m1], IHprv2 as [m2], (enum_form' phi) as [m4], (enum_form' psi) as [m5].
        exists (1 + m1 + m2 + m4 + m5). cbn. in_app 7. cbn. in_collect (phi, psi)...
      + destruct IHprv as [m1], (enum_form' phi) as [m2]. exists (1 + m1 + m2). cbn. in_app 8. in_collect phi...
      + now exists 0.
      + destruct IHprv1 as [m1], IHprv2 as [m2]. exists (1 + m1 + m2). cbn. in_app 10. in_collect (phi, psi)...
      + destruct IHprv as [m1], (enum_form' phi) as [m2], (enum_form' psi) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 11. in_collect (phi, psi)...
      + destruct IHprv as [m1], (enum_form' phi) as [m2], (enum_form' psi) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 12. in_collect (phi, psi)...
      + destruct IHprv as [m1], (enum_form' phi) as [m2], (enum_form' psi) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 13. in_collect (phi, psi)...
      + destruct IHprv as [m1], (enum_form' phi) as [m2], (enum_form' psi) as [m3].
        exists (1 + m1 + m2 + m3). cbn. in_app 14. in_collect (phi, psi)...
      + destruct IHprv1 as [m1], IHprv2 as [m2], IHprv3 as [m3], (enum_form' phi) as [m4], (enum_form' psi) as [m5], (enum_form' theta) as [m6].
        exists (1 + m1 + m2 + m3 + m4 + m5 + m6). cbn. in_app 15. cbn. in_collect (phi, (psi, theta))...
      + destruct (enum_form' phi) as [m1], (enum_form' psi) as [m2]. exists (1 + m1 + m2). cbn. in_app 9. in_collect (phi, psi)...
    - intros [m]; induction m in A, x, H |-*; cbn in *.
      + now apply Ctx.
      + destruct p, b; inv_collect. all: eauto 3; try now destruct H.
        * eapply IE; apply IHm; eauto.
        * eapply ExE; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply ExE; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply ExE; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
        * eapply IE; apply IHm; eauto.
        * eapply ExE; apply IHm; eauto.
        * eapply DE; apply IHm; eauto.
  Qed.

End Enumerability.

Lemma list_enumerator_enumerator X (p : X -> Prop) L :
  list_enumerator L p -> { f | forall x : X, p x <-> exists n : nat, f n = Some x }.
Proof.
  intros H. exists (fun n => let (n, m) := decode n in nth_error (L n) m).
  intros x. rewrite list_enumerator_to_enumerator. apply H.
Qed.

Theorem enumerable_Q_prv (Φ : nat -> form) :
  enumerable (fun n => Q ⊢I (Φ n)).
Proof.
  edestruct list_enumerator_enumerator as [e He].
  - unshelve eapply enum_prv.
    + exact intu.
    + exact Q.
  - exists (fun n => let (n, k) := decode n in match e n with Some psi => if Dec (psi = Φ k) then Some k else None | _ => None end).
    intros k. split; intros H.
    + apply He in H as [n Hn]. exists (code (n, k)). rewrite inv_dc, Hn. now destruct Dec.
    + destruct H as [n H]. destruct (decode n) as [n' k']. destruct (e n') as [psi |] eqn : Hn.
      * destruct Dec; try congruence. apply He. exists n'. congruence.
      * congruence.
Qed.
  
