Require Import Vector List Lia.

Require Import Coq.Vectors.Vector.
Definition vec := t.

Require Import Equations.Equations.

(** * Proposed new definition of First Order Logic in Coq *)

(**

Renaming table w.r.t. the three existing developments

new name     | TRAKH name     | completeness name
--------------------------------------------------
syms         | syms           | Funcs
ar_syms      | ar_syms        | fun_ar
var          | in_var         | var_term
func         | in_fot         | Func
preds        | rels           | Preds
ar_preds     | ar_rels        | pred_ar
binop        | fol_bop        | -
quantop      | fol_qop        | -
fal          | fol_false      | Fal
atom         | fol_atom       | Pred
bin          | fol_bin        | Impl / ...
quant        | fol_quant      | All / ...

 *)


(* Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
        | 0 => x
        | S n => xi n
        end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

(* Signatures are a record to allow for easier definitions of general transformations on signatures *)

Class funcs_signature :=
  { syms : Type; ar_syms : syms -> nat }.

Coercion syms : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; ar_preds : preds -> nat }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  (* We use the stdlib definition of vectors to be maximally compatible  *)

  Unset Elimination Schemes.

  Inductive term  : Type :=
  | var : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.

  Set Elimination Schemes.

  Fixpoint subst_term (σ : nat -> term) (t : term) : term :=
    match t with
    | var t => σ t
    | func f v => func f (map (subst_term σ) v)
    end.

  Context {Σ_preds : preds_signature}.

  (* We use a flag to switch on and off a constant for falisity *)

  Inductive falsity_flag := falsity_off | falsity_on.
  Existing Class falsity_flag.
  Existing Instance falsity_on | 1.
  Existing Instance falsity_off | 0.

  (* Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)
  Class operators := {binop : Type ; quantop : Type}.
  Context {ops : operators}.
  
  (* Formulas have falsity as fixed constant -- we could parametrise against this in principle *)
  Inductive form : falsity_flag -> Type :=
  | falsity : form falsity_on
  | atom {b} : forall (P : preds), vec term (ar_preds P) -> form b
  | bin {b} : binop -> form b -> form b -> form b
  | eq {b} : term -> term -> form b
  | quant {b} : quantop -> form b -> form b.
  Arguments form {_}.

  Lemma form_ind_falsity_on :
    forall f : form -> Type,
      f falsity ->
      (forall P (t : vec term (ar_preds P)), f (atom P t)) ->
      (forall (b : binop) (φ : form), f φ -> forall ψ : form, f ψ -> f (bin b φ ψ)) ->
      (forall t s, f (eq t s) ) ->
      (forall (q : quantop) (φ : form), f φ -> f (quant q φ)) ->
      forall (φ : form), f φ.
  Proof.
    intros. specialize (form_rect (fun ff => match ff with falsity_on => f | _ => fun _ => True end)).
    intros H'. apply H' with (f5 := falsity_on); clear H'. all: intros; try destruct b; trivial.
    all: intuition eauto 2.    
  Qed.

  
  Definition up (σ : nat -> term) := scons (var 0) (funcomp (subst_term (funcomp var S)) σ).

  Fixpoint subst_form `{falsity_flag} (σ : nat -> term) (phi : form) : form :=
    match phi with
    | falsity => falsity
    | atom P v => atom P (map (subst_term σ) v)
    | bin op phi1 phi2 => bin op (subst_form σ phi1) (subst_form σ phi2)
    | eq s t => eq (subst_term σ s) (subst_term σ t)
    | quant op phi => quant op (subst_form (up σ) phi)
    end.

  Fixpoint form_depth `{falsity_flag} phi :=
    match phi with
    | falsity => 0
    | atom P v => 0
    | bin op phi1 phi2 => S (form_depth phi1 + form_depth phi2)
    | eq s t => 0
    | quant op phi => S (form_depth phi)
    end.


  (* Induction principle for terms *)

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type :=
  | vec_inB {n} (v : t A n) : vec_in a (cons A a n v)
  | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
  Hint Constructors vec_in : core.
  
  Lemma term_rect' (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. fix strong_term_ind' 1. destruct t as [n|F v].
    - apply f1.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (var x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (var x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2. eapply term_rect'.
    - apply f1.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.


  
End fix_signature.



(* Setting implicit arguments is crucial  *)
(* We can write term both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Arguments subst_term {_} _ _.

(* Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
Arguments form  _ _ _ _, _ _ {_ _}, {_ _ _ _}, {_ _ _} _.
Arguments atom  _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments bin   _ _ _ _, _ _ {_ _}, {_ _ _ _}.
Arguments quant _ _ _ _, _ _ {_ _}, {_ _ _ _}.

Arguments up         _, {_}.
Arguments subst_form _ _ _ _, _ _ {_ _}, {_ _ _ _}.




(* Substitution Notation *)

Declare Scope subst_scope.
Open Scope subst_scope.

Notation "$ x" := (var x) (at level 3, format "$ '/' x") : subst_scope.
Notation "t `[ sigma ]" := (subst_term sigma t) (at level 7, left associativity, format "t '/' `[ sigma ]") : subst_scope.
Notation "phi [ sigma ]" := (subst_form sigma phi) (at level 7, left associativity, format "phi '/' [ sigma ]") : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 70, right associativity) : subst_scope.
Notation "f >> g" := (funcomp g f) (at level 50) : subst_scope.
Notation "s '..'" := (scons s var) (at level 4, format "s ..") : subst_scope.
Notation "↑" := (S >> var) : subst_scope.



(** ** Substituion lemmas *)

Ltac cbns :=
    cbn; repeat (match goal with [ |- context f[subst_form ?sigma ?phi] ] => change (subst_form sigma phi) with (phi[sigma]) end).

Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Lemma subst_term_ext (t : term) sigma tau :
    (forall n, sigma n = tau n) -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now apply map_ext_in.
  Qed.

  Lemma subst_term_id (t : term) sigma :
    (forall n, sigma n = var n) -> t`[sigma] = t.
  Proof.
    intros H. induction t; cbn.
    - now apply H.
    - f_equal. now erewrite map_ext_in, map_id.
  Qed.

  Lemma subst_term_var (t : term) :
    t`[var] = t.
  Proof.
    now apply subst_term_id.
  Qed.

  Lemma subst_term_comp (t : term) sigma tau :
    t`[sigma]`[tau] = t`[sigma >> subst_term tau].
  Proof.
    induction t; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. now apply map_ext_in.
  Qed.

  Lemma subst_term_shift (t : term) s :
    t`[↑]`[s..] = t.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. now intros [|].
  Qed.

  Lemma up_term (t : term) xi :
    t`[↑]`[up xi] = t`[xi]`[↑].
  Proof.
    rewrite !subst_term_comp. apply subst_term_ext. reflexivity.
  Qed.

  Lemma up_ext sigma tau :
    (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_var sigma :
    (forall n, sigma n = var n) -> forall n, up sigma n = var n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_funcomp sigma tau :
    forall n, (up sigma >> subst_term (up tau)) n = up (sigma >> subst_term tau) n.
  Proof.
    intros [|]; cbn; trivial.
    setoid_rewrite subst_term_comp.
    apply subst_term_ext. now intros [|].
  Qed.

  Lemma subst_ext {ff : falsity_flag} (phi : form) sigma tau :
    (forall n, sigma n = tau n) -> phi[sigma] = phi[tau].
  Proof.
    induction phi in sigma, tau |- *; cbns; intros H.
    - reflexivity.
    - f_equal. apply map_ext. intros s. now apply subst_term_ext.
    - now erewrite IHphi1, IHphi2.
    - f_equal; now apply subst_term_ext.
    - erewrite IHphi; trivial. now apply up_ext.
  Qed.

  Lemma subst_id {ff : falsity_flag} (phi : form) sigma :
    (forall n, sigma n = var n) -> phi[sigma] = phi.
  Proof.
    induction phi in sigma |- *; cbns; intros H.
    - reflexivity.
    - f_equal. erewrite map_ext; try apply map_id. intros s. now apply subst_term_id.
    - now erewrite IHphi1, IHphi2.
    - f_equal; now apply subst_term_id.
    - erewrite IHphi; trivial. now apply up_var.
  Qed.

  Lemma subst_var {ff : falsity_flag} (phi : form) :
    phi[var] = phi.
  Proof.
    now apply subst_id.
  Qed.

  Lemma subst_comp {ff : falsity_flag} (phi : form) sigma tau :
    phi[sigma][tau] = phi[sigma >> subst_term tau].
  Proof.
    induction phi in sigma, tau |- *; cbns.
    - reflexivity.
    - f_equal. rewrite map_map. apply map_ext. intros s. apply subst_term_comp.
    - now rewrite IHphi1, IHphi2.
    - f_equal; now apply subst_term_comp.
    - rewrite IHphi. f_equal. now apply subst_ext, up_funcomp.
  Qed.

  Lemma subst_shift {ff : falsity_flag} (phi : form) s :
    phi[↑][s..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [|].
  Qed.

  Lemma up_form {ff : falsity_flag} xi psi :
    psi[↑][up xi] = psi[xi][↑].
  Proof.
    rewrite !subst_comp. apply subst_ext. reflexivity.
  Qed.


  Fixpoint iter {X: Type} f n (x : X) :=
    match n with
      0 => x
    | S m => f (iter f m x)
    end.
  

  Lemma iter_switch {X} f n (x : X) :
    f (iter f n x) = iter f n (f x).
  Proof.
    induction n. reflexivity.
    cbn. now rewrite IHn.
  Qed.


  Lemma up_decompose {ff : falsity_flag} sigma phi : 
    phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.

  
End Subst.



(** ** Bounded formulas *)

Section Bounded.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Inductive bounded_t n : term -> Prop :=
  | bounded_var x : n > x -> bounded_t n $x
  | bouded_func f v : (forall t, Vector.In t v -> bounded_t n t) -> bounded_t n (func f v).

  Inductive bounded : forall {ff}, nat -> form ff -> Prop :=
  | bounded_atom ff n P v : (forall t, Vector.In t v -> bounded_t n t) -> @bounded ff n (atom P v)
  | bounded_bin binop ff n phi psi : @bounded ff n phi -> @bounded ff n psi -> @bounded ff n (bin binop phi psi)
  | bounded_eq ff n s t : bounded_t n s -> bounded_t n t -> @bounded ff n (eq s t)
  | bounded_quant quantop ff n phi : @bounded ff (S n) phi -> @bounded ff n (quant quantop phi)
  | bounded_falsity n : @bounded falsity_on n falsity.

  Arguments bounded {_} _ _.

  Definition bounded_L {ff : falsity_flag} n A :=
    forall phi, List.In phi A -> bounded n phi.

  Lemma bounded_subst_t n t sigma tau :
    (forall k, n > k -> sigma k = tau k) -> bounded_t n t -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction 1; cbn; auto.
    f_equal. now apply Vector.map_ext_in.
  Qed.

  Lemma bounded_subst {ff : falsity_flag} {n phi sigma tau} :
    bounded n phi -> (forall k, n > k -> sigma k = tau k) -> phi[sigma] = phi[tau].
  Proof.
    induction 1 in sigma, tau |- *; cbn; intros HN; trivial.
    - f_equal. apply Vector.map_ext_in. intros t Ht.
      eapply bounded_subst_t; try apply HN. now apply H.
    - now rewrite (IHbounded1 sigma tau), (IHbounded2 sigma tau).
    - f_equal; eapply bounded_subst_t; eauto.
    - f_equal. apply IHbounded. intros [|k] Hk; cbn; trivial.
      unfold funcomp. rewrite HN; trivial. lia.
  Qed.

  Lemma bounded_up_t {n t k} :
    bounded_t n t -> k >= n -> bounded_t k t.
  Proof.
    induction 1; intros Hk; constructor; try lia. firstorder.
  Qed.

  Lemma bounded_up {ff : falsity_flag} {n phi k} :
    bounded n phi -> k >= n -> bounded k phi.
  Proof.
    induction 1 in k |- *; intros Hk; constructor; eauto.
    - intros t Ht. eapply bounded_up_t; eauto.
    - eapply bounded_up_t; eauto.
    - eapply bounded_up_t; eauto.
    - apply IHbounded. lia.
  Qed.

  Derive Signature for In.

  Lemma find_bounded_step n (v : vec term n) :
    (forall t : term, vec_in t v -> {n : nat | bounded_t n t}) -> { n | forall t, In t v -> bounded_t n t }.
  Proof.
    induction v; cbn; intros HV.
    - exists 0. intros t. inversion 1.
    - destruct IHv as [k Hk], (HV h) as [l Hl]; try left.
      + intros t Ht. apply HV. now right.
      + exists (k + l). intros t H. depelim H; cbn in *.
        * injection H. intros _ <-. apply (bounded_up_t Hl). lia.
        * injection H0. intros -> % Eqdep_dec.inj_pair2_eq_dec _; try decide equality.
          apply (bounded_up_t (Hk t H)). lia.
  Qed.

  Lemma find_bounded_t t :
    { n | bounded_t n t }.
  Proof.
    induction t using term_rect.
    - exists (S x). constructor. lia.
    - apply find_bounded_step in X as [n H]. exists n. now constructor.
  Qed.

  Lemma find_bounded {ff : falsity_flag} phi :
    { n | bounded n phi }.
  Proof.
    induction phi.
    - exists 0. constructor.
    - destruct (find_bounded_step _ v) as [n Hn].
      + eauto using find_bounded_t.
      + exists n. now constructor.
    - destruct IHphi1 as [n Hn], IHphi2 as [k Hk]. exists (n + k).
      constructor; eapply bounded_up; try eassumption; lia.
    - destruct (find_bounded_t t) as [n Hn], (find_bounded_t t0) as [l Hl].
      exists (n + l). constructor; eapply bounded_up_t; eauto; lia.
    - destruct IHphi as [n Hn]. exists n. constructor. apply (bounded_up Hn). lia.
  Qed.

  Lemma find_bounded_L {ff : falsity_flag} A :
    { n | bounded_L n A }.
  Proof.
    induction A; cbn.
    - exists 0. intros phi. inversion 1.
    - destruct IHA as [k Hk], (find_bounded a) as [l Hl].
      exists (k + l). intros t [<-|H]; eapply bounded_up; try eassumption; try (now apply Hk); lia.
  Qed.

  Ltac invert_bounds :=
    inversion 1; subst;
    repeat match goal with
             H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H; try decide equality
           end; subst.

  Lemma vec_cons_inv X n (v : Vector.t X n) x y :
    In y (Vector.cons X x n v) -> (y = x) \/ (In y v).
  Proof.
    inversion 1; subst.
    - now left.
    - apply EqDec.inj_right_pair in H3 as ->. now right.
  Qed.


  Definition dec (P : Prop) := {P} + {~P}.
  
  Lemma vec_all_dec X n (v : vec X n) (P : X -> Prop) :
    (forall x, vec_in x v -> dec (P x)) -> dec (forall x, In x v -> P x).
  Proof.
    induction v; intros H.
    - left. intros x. inversion 1.
    - destruct (H h) as [H1|H1], IHv as [H2|H2]; try now left.
      + intros x Hx. apply H. now right.
      + intros x Hx. apply H. now right.
      + left. intros x [<-| Hx] % vec_cons_inv; intuition.
      + right. contradict H2. intros x Hx. apply H2. now right.
      + intros x Hx. apply H. now right.
      + right. contradict H1. apply H1. now left.
      + right. contradict H1. apply H1. now left.
  Qed.

  Context {sig_funcs_dec : EqDec Σ_funcs}.
  Context {sig_preds_dec : EqDec Σ_preds}.

  Lemma bounded_t_dec n t :
    dec (bounded_t n t).
  Proof.
    pattern t; revert t. apply term_rect.
    - intros x. destruct (Compare_dec.gt_dec n x) as [H|H].
      + left. now constructor.
      + right. inversion 1; subst. tauto.
    - intros F v X. apply vec_all_dec in X as [H|H].
      + left. now constructor.
      + right. inversion 1; subst. apply EqDec.inj_right_pair in H3 as ->. tauto.
  Qed.

End Bounded.

Ltac solve_bounds :=
  repeat constructor; try lia; try inversion X; intros;
  match goal with
  | H : Vector.In ?x (@Vector.cons _ ?y _ ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H
  | H : Vector.In ?x (@Vector.nil _) |- _ => try inversion H
  | _ => idtac
  end.