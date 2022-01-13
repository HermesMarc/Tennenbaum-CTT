Require Import FOL Deduction Tarski DecidabilityFacts NumberTheory.
Require Import List Lia.
Import Vector.VectorNotations.

Require Import Equations.Equations Equations.Prop.DepElim.


(* For Definitions, my reference was the treatment of Peter Smith in "Introduction to Gödel's Theorems"
 (page 37) *)

Existing Instance falsity_on.

(** * Peano Arithmetic *)

(** ** Non-logical symbols used in the language of PA *)

Inductive PA_funcs : Type :=
  Zero : PA_funcs
| Succ : PA_funcs
| Plus : PA_funcs
| Mult : PA_funcs.

Definition PA_funcs_ar (f : PA_funcs ) :=
match f with
 | Zero => 0
 | Succ => 1
 | Plus => 2
 | Mult => 2
 end.

Inductive PA_preds : Type := .

Definition PA_preds_ar (P : PA_preds) :=
match P with
 | _ => 0
end.


Instance PA_funcs_signature : funcs_signature :=
{| syms := PA_funcs ; ar_syms := PA_funcs_ar |}.

Instance PA_preds_signature : preds_signature :=
{| preds := PA_preds ; ar_preds := PA_preds_ar |}.


Arguments Vector.cons {_} _ {_} _, _ _ _ _.



Declare Scope PA_Notation.
Open Scope PA_Notation.

Notation "'zero'" := (func Zero ([])) (at level 1) : PA_Notation.
Notation "'σ' x" := (func Succ ([x])) (at level 37) : PA_Notation.
Notation "x '⊕' y" := (func Plus ([x ; y]) ) (at level 39) : PA_Notation.
Notation "x '⊗' y" := (func Mult ([x ; y]) ) (at level 38) : PA_Notation.
Notation "x '==' y" := (eq x y) (at level 40) : PA_Notation.
(* Definition syntac_less (x y : term) := (∃ y[↑] == σ (x[↑] ⊕ $0)) : PA_Notation. *)
Notation "x '⧀' y" := (∃ y`[↑] == σ (x`[↑] ⊕ $0)) (at level 40) : PA_Notation.



(* Defines numerals i.e. a corresponding term for every natural number *)
Fixpoint num n :=  
  match n with
    O => zero
  | S x => σ (num x)
  end.






Definition forall_times n (phi : form) := iter (fun psi => ∀ psi) n phi.

(** ** PA Axioms *)

(** *** Basic Axioms *)

Definition ax_zero_succ := ∀  (zero == σ var 0 --> ⊥).
Definition ax_succ_inj :=  ∀∀ (σ $1 == σ $0 --> $1 == $0).
Definition ax_add_zero :=  ∀  (zero ⊕ $0 == $0).
Definition ax_add_rec :=   ∀∀ ((σ $0) ⊕ $1 == σ ($0 ⊕ $1)).
Definition ax_mult_zero := ∀  (zero ⊗ $0 == zero).
Definition ax_mult_rec :=  ∀∀ (σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0).

(** *** Induction Scheme *)

Definition ax_induction (phi : form) :=
  phi[zero..] --> (∀ phi --> phi[σ $0 .: S >> var]) --> ∀ phi.

Definition ax_zero_or_succ := ∀ $0 == zero ∨ ∃ $1 == σ $0.



(** *** Equality Axioms *)

Definition ax_refl :=  ∀   $0 == $0.
Definition ax_sym :=   ∀∀  $1 == $0 --> $0 == $1.
Definition ax_trans := ∀∀∀ $2 == $1 --> $1 == $0 --> $2 == $0.

Definition ax_succ_congr := ∀∀ $0 == $1 --> σ $0 == σ $1.
Definition ax_add_congr := ∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊕ $2 == $1 ⊕ $3.
Definition ax_mult_congr := ∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊗ $2 == $1 ⊗ $3.


Definition EQ :=
  (ax_refl :: ax_sym :: ax_trans :: ax_succ_congr :: ax_add_congr :: ax_mult_congr :: nil)%list.


(** ** Robinson Arithmetic *)
Definition Q := (EQ ++ ax_zero_succ :: ax_succ_inj :: ax_add_zero :: ax_add_rec :: ax_mult_zero :: ax_mult_rec :: ax_zero_or_succ :: nil)%list.


(** ** The Theory PA *)
Inductive PA : form -> Prop :=
| PA_Q : forall ax, List.In ax Q -> PA ax
| PA_induction : forall phi, PA (ax_induction phi).


Notation "x 'i=' y" := (i_P (Σ_funcs:=PA_preds_signature) (P:=Eq) [x ; y]) (at level 30) : PA_Notation.
Notation "'i0'" := (i_f (Σ_funcs:=PA_funcs_signature) (f:=Zero) []) (at level 2) : PA_Notation.
Notation "'iσ' d" := (i_f (Σ_funcs:=PA_funcs_signature) (f:=Succ) [d]) (at level 37) : PA_Notation.
Notation "x 'i⊕' y" := (i_f (Σ_funcs:=PA_funcs_signature) (f:=Plus) [x ; y]) (at level 39) : PA_Notation.
Notation "x 'i⊗' y" := (i_f (Σ_funcs:=PA_funcs_signature) (f:=Mult) [x ; y]) (at level 38) : PA_Notation.


(** ** PA Models *)

Section Models.


  Variable D : Type.
  Variable I : interp D.

  Notation "x 'i⧀' y" := (exists d : D, y = iσ (x i⊕ d) ) (at level 40).



  Definition theory := form -> Prop.
  Definition in_theory (T : theory) phi := T phi.

  Notation "phi ∈ T" := (in_theory T phi) (at level 70).
  Notation "A ⊏ T" := (forall phi, In phi A -> phi ∈ T) (at level 70).
  Definition PAsat phi := exists A, A ⊏ PA /\ forall rho, (forall α, In α A -> rho ⊨ α) -> rho ⊨ phi.



  Fixpoint inu n := 
    match n with
    | 0 => i0
    | S x => iσ (inu x)
    end.


  
  Fact eval_num sigma n : 
    eval sigma (num n) = inu n.
  Proof.
    induction n.
    - reflexivity.
    - cbn. now rewrite IHn.
  Qed.


  Lemma num_subst : 
    forall n rho, (num n)`[rho] = num n.
  Proof.
    induction n.
    - reflexivity.
    - intros rho. cbn. now rewrite IHn.
  Qed.


  Lemma switch_num alpha rho n : 
    rho ⊨ alpha[(num n)..] <-> ((inu n).:rho) ⊨ alpha.
  Proof.    
    split; intros H.
    - erewrite <-eval_num. apply sat_single, H.
    - apply sat_single. now rewrite eval_num.
  Qed.

  
  Lemma switch_up_num α rho x d : 
    (d.:rho) ⊨ (α [up (num x)..]) <-> (d.:((inu x).:rho)) ⊨ α.
  Proof.
    rewrite sat_comp. apply sat_ext.
    intros [|[]]; try reflexivity.
    cbn. now rewrite num_subst, eval_num.
  Qed.



  Lemma eq_sym : forall rho a b, rho ⊨ (a == b) -> rho ⊨ (b == a).
  Proof.
    intros. now cbn in *.
  Qed.
  
  Lemma eq_trans : forall rho a b c, rho ⊨ (a == b) /\ rho ⊨ (b == c) -> rho ⊨ (a == c).
  Proof.
    intros ????. cbn in *. intros []. congruence.
  Qed.

  Notation "⊨ phi" := (forall rho, rho ⊨ phi) (at level 21).




  Section PA_Model.

    Context {axioms : forall ax, PA ax -> ⊨ ax}. 


    (* provide all axioms in a more useful form *)

    Lemma zero_succ x : i0 = iσ x -> False.
    Proof.
      assert (⊨ ax_zero_succ) as H.
      apply axioms; constructor.
      firstorder.
      specialize (H (fun _ => i0) x).
      apply H.
    Qed.

    Lemma succ_inj x y : iσ y = iσ x -> y = x.
    Proof.
      assert (⊨ ax_succ_inj ) as H.
      apply axioms; constructor.
      firstorder.
      specialize (H (fun _ => i0) y x).
      apply H.
    Qed.

    Lemma succ_inj' x y : iσ y = iσ x <-> y = x.
    Proof.
      split.
      apply succ_inj. now intros ->.
    Qed.


    Lemma add_zero d : i0 i⊕ d = d.
    Proof.
      assert (⊨ ax_add_zero) as H.
      apply axioms; constructor.
      firstorder.
      specialize (H (fun _ => i0) d).
      apply H.
    Qed.

    Lemma add_rec n d : (iσ n) i⊕ d = iσ (n i⊕ d). 
    Proof.
      assert (⊨ ax_add_rec) as H.
      apply axioms; constructor.
      firstorder.
      specialize (H (fun _ => i0) d n).
      apply H.
    Qed.

    Lemma mult_zero d : i0 i⊗ d = i0.
    Proof.
      assert (⊨ ax_mult_zero) as H.
      apply axioms; constructor.
      firstorder.
      specialize (H (fun _ => i0) d).
      apply H.
    Qed.

    Lemma mult_rec n d : (iσ d) i⊗ n = n i⊕ (d i⊗ n).
    Proof.
      assert (⊨ ax_mult_rec) as H.
      apply axioms; constructor.
      firstorder.
      specialize (H (fun _ => i0) d n).
      apply H.
    Qed.



    Section Induction.
      
      Notation "phi [[ d ]] " := (forall rho, (d.:rho) ⊨ phi) (at level 19).

      Variable phi : form.
      Variable pred : bounded 1 phi.
      
      Lemma induction1 : phi[[i0]] -> ⊨ phi[zero..].
      Proof.
        intros H0 rho.
        apply sat_single. apply H0.
      Qed.

      Lemma induction2 :
        (forall n, phi[[n]] -> phi[[iσ n]]) -> ⊨ (∀ phi --> phi[σ $ 0 .: S >> var]).
      Proof.
        intros IH rho d Hd.
        eapply sat_comp, sat_ext.
        instantiate (1 := ((iσ d).:rho)).
        intros []; now cbn.
        apply IH. intros ?.
        eapply bound_ext. apply pred. 2 : apply Hd.
        intros []; intros.
        reflexivity. lia.
      Qed.


      Theorem induction : phi[[i0]] -> (forall n, phi[[n]] -> phi[[iσ n]] ) -> forall n, phi[[n]].
      Proof.
        assert (⊨ ax_induction phi) as H.
        apply axioms. apply PA_induction.
        intros ??? rho.
        specialize (H rho). 
        apply H.
        now apply induction1.
        now apply induction2.
      Qed.  

    End Induction.



    Lemma inu_inj x y : inu x = inu y <-> x = y.
    Proof.
      split.
      induction x in y |-*; destruct y; auto; cbn.
      - now intros ?%zero_succ.
      - intros H. symmetry in H. now apply zero_succ in H.
      - now intros <-%succ_inj%IHx.
      - congruence.
    Qed.


    Lemma inu_add_hom x y : inu (x + y) = inu x i⊕ inu y.
    Proof.
      induction x; cbn.
      - now rewrite add_zero.
      - now rewrite add_rec, IHx.
    Qed.


    Lemma inu_mult_hom x y : inu (x * y) = inu x i⊗ inu y.
    Proof.
      induction x; cbn.
      - now rewrite mult_zero.
      - now rewrite inu_add_hom, IHx, mult_rec.
    Qed.



    Lemma add_zero_r n : n i⊕ i0 = n.
    Proof.
      pose (phi := $0 ⊕ zero == $0). 
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds. 
      - intros ?. cbn. now rewrite add_zero.
      - intros x IH rho. 
        specialize (IH (fun _ => i0)); cbn in *.
        now rewrite add_rec, IH. 
      - now specialize (H n (fun _ => i0)). 
    Qed. 


    Lemma mult_zero_r n : n i⊗ i0 = i0.
    Proof.
      pose (phi := $0 ⊗ zero == zero). 
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds. 
      - intros ?. cbn. now rewrite mult_zero.
      - intros x IH rho. 
        specialize (IH (fun _ => i0)); cbn in *.
        now rewrite mult_rec, IH, add_zero. 
      - now specialize (H n (fun _ => i0)).
    Qed. 


    Lemma add_rec_r n d : n i⊕ (iσ d) = iσ (n i⊕ d). 
    Proof.
      pose (phi := ∀ $1 ⊕ (σ $0) == σ ($1 ⊕ $0) ).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ??. cbn. now rewrite !add_zero.
      - intros x IH rho y. cbn.
        specialize (IH (fun _ => i0) y); cbn in *.
        now rewrite !add_rec, IH.
      - now specialize (H n (fun _ => i0) d); cbn in *.
    Qed.


    Lemma add_comm n d : n i⊕ d = d i⊕ n.
    Proof.
      pose (phi := ∀ $0 ⊕ $1 == $1 ⊕ $0).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ??; cbn. now rewrite add_zero, add_zero_r.
      - intros x IH rho.
        specialize (IH (fun _ => i0)); cbn in *.
        intros y. now rewrite add_rec, add_rec_r, IH.
      - now specialize (H n (fun _ => i0) d); cbn in *.
    Qed.


    Lemma add_asso x y z : (x i⊕ y) i⊕ z = x i⊕ (y i⊕ z).
    Proof.
      pose (phi := ∀∀ ($2 ⊕ $1) ⊕ $0 == $2 ⊕ ($1 ⊕ $0) ).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ???. cbn. now rewrite !add_zero.
      - intros X IH rho Y Z. cbn.
        specialize (IH (fun _ => i0) Y); cbn in *.
        now rewrite !add_rec, IH.
      - now specialize (H x (fun _ => i0) y z); cbn in *.
    Qed.


    Lemma mult_rec_r n d : n i⊗ (iσ d) = n i⊕ (n i⊗ d) . 
    Proof.
      pose (phi := ∀ $1 ⊗ (σ $0) == $1 ⊕ ($1 ⊗ $0) ).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ??. cbn. now rewrite !mult_zero, add_zero.
      - intros x IH rho y. cbn.
        specialize (IH (fun _ => i0) y); cbn in *.
        rewrite !mult_rec, IH, <- !add_asso.
        rewrite add_rec, <- add_rec_r. now rewrite (add_comm y).
      - now specialize (H n (fun _ => i0) d); cbn in *.
    Qed.


    Lemma mult_comm n d : n i⊗ d = d i⊗ n.
    Proof.
      pose (phi := ∀ $0 ⊗ $1 == $1 ⊗ $0).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ??; cbn. now rewrite mult_zero, mult_zero_r.
      - intros x IH rho.
        specialize (IH (fun _ => i0)); cbn in *.
        intros y. now rewrite mult_rec, mult_rec_r, IH.
      - now specialize (H n (fun _ => i0) d); cbn in *.
    Qed.


    Lemma distributive x y z : (x i⊕ y) i⊗ z = (x i⊗ z) i⊕ (y i⊗ z).
    Proof.
      pose (phi := ∀∀ ($1 ⊕ $0) ⊗ $2 == ($1 ⊗ $2) ⊕ ($0 ⊗ $2) ).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ???. cbn. now rewrite !mult_zero_r, add_zero.
      - intros X IH rho Y Z. cbn.
        specialize (IH (fun _ => i0) Y); cbn in *.
        rewrite mult_rec_r, IH.
        rewrite <- add_asso, (add_comm Y Z), (add_asso Z Y).
        rewrite <- mult_rec_r.
        rewrite add_comm, <-add_asso, (add_comm _ Z).
        rewrite <- mult_rec_r.
        now rewrite add_comm.
      - now specialize (H z (fun _ => i0) x y); cbn in *.
    Qed.


    Lemma mult_asso x y z : (x i⊗ y) i⊗ z = x i⊗ (y i⊗ z).
    Proof.
      pose (phi := ∀∀ ($2 ⊗ $1) ⊗ $0 == $2 ⊗ ($1 ⊗ $0) ).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ???. cbn. now rewrite !mult_zero.
      - intros X IH rho Y Z. cbn.
        specialize (IH (fun _ => i0) Y); cbn in *.
        now rewrite !mult_rec, <-IH, distributive.
      - now specialize (H x (fun _ => i0) y z); cbn in *.
    Qed.


    Lemma nolessthen_zero d : ~ d i⧀ i0.
    Proof. now intros [? []%zero_succ]. Qed.


    Lemma zero_or_succ : forall d, d = i0 \/ exists x, d = iσ x.
    Proof.
      pose (phi := $0 == zero ∨ ∃ $1 == σ $0).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros rho. cbn. now left.
      - intros n IH rho. cbn. right. exists n. reflexivity.
      - intros d. now specialize (H d (fun _ => i0)); cbn in *.
    Qed.

    Lemma eq_dec : forall x y : D, x = y \/ x <> y.
    Proof.
      pose (phi := ∀ $1 == $0 ∨ ($1 == $0 --> ⊥)).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros rho d. cbn.
        destruct (zero_or_succ d) as [|[x ->]].
        + now left.
        + right. apply zero_succ.
      - intros n IH rho. cbn.
        intros d. destruct (zero_or_succ d) as [-> | [x ->]].
        + right. intros ?. eapply zero_succ. eauto.
        + destruct (IH (fun _ => i0) x); cbn in H.
          left. now rewrite H.
          right. intros ?%succ_inj. auto.
      - intros x y. 
        now specialize (H x (fun _ => i0) y); cbn in *.
    Qed.

    Lemma sum_is_zero x y : x i⊕ y = i0 -> x = i0 /\ y = i0.
    Proof.
      intros H.
      destruct (zero_or_succ x) as [-> |[? ->]], (zero_or_succ y) as [-> |[? ->]]; auto.
      - repeat split. now rewrite add_zero in H.
      - repeat split. rewrite add_rec in H. symmetry in H.
        now apply zero_succ in H.
      - split; rewrite add_rec in H; symmetry in H; now apply zero_succ in H.
    Qed.

    
    Lemma lt_SS x y : (iσ x) i⧀ (iσ y) <-> x i⧀ y.
    Proof.
      split; intros [k Hk]; exists k.
      - apply succ_inj in Hk. now rewrite <-add_rec.
      - now rewrite Hk, add_rec. 
    Qed.

    Lemma trichotomy x y : x i⧀ y \/ x = y \/ y i⧀ x.
    Proof.
      pose (phi := ∀ ($1 ⧀ $0) ∨ ($1 == $0 ∨ $0 ⧀ $1)).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros rho d; cbn. destruct (zero_or_succ d) as [-> | [k ->] ].
        + now right; left.
        + left. exists k. now rewrite add_zero.
      - intros n IH rho d. cbn. destruct (zero_or_succ d) as [-> | [k ->] ].
        + right; right. exists n. now rewrite add_zero.
        + specialize (IH (fun _ => i0) k); cbn in IH.
          rewrite !lt_SS. intuition congruence. 
      - now specialize (H x (fun _ => i0) y); cbn in H.
    Qed.



    Lemma add_eq x y t : x i⊕ t = y i⊕ t -> x = y.
    Proof.
      pose (phi := ∀∀ $0 ⊕ $2 == $1 ⊕ $2 --> $0 == $1  ).
      assert (forall n rho, (n.:rho) ⊨ phi).
      apply induction. repeat solve_bounds.
      - intros ???. cbn. now rewrite !add_zero_r.
      - intros T IH rho Y X; cbn in *.
        rewrite !add_rec_r, <-!add_rec.
        now intros ?%IH%succ_inj.
      - now specialize (H t (fun _ => i0) y x); cbn in *.
    Qed.


    Lemma lt_neq x y : x i⧀ y -> x = y -> False.
    Proof.
      intros [k Hk] ->. revert Hk.
      rewrite <-add_rec_r, <-(add_zero_r y) at 1.
      rewrite !(add_comm y).
      intros H%add_eq. revert H.
      apply zero_succ.
    Qed.


    Notation "x 'i≤' y" := (exists d : D, y = x i⊕ d)  (at level 40).

    Lemma lt_le_equiv1 x y : x i⧀ iσ y <-> x i≤ y.
    Proof.
      split; intros [k Hk].
      - exists k. now apply succ_inj in Hk.
      - exists k. congruence.
    Qed.



    Lemma lt_S d e : d i⧀ (iσ e) <-> d i⧀ e \/ d = e.
    Proof.
      pose (Φ := ∀ $0 ⧀ σ $1 <--> $0 ⧀ $1 ∨ $0 == $1).
      assert (H: forall d rho, (d .: rho)⊨ Φ).
      apply induction.
      repeat solve_bounds; cbn in H.
      1,2 : apply vec_cons_inv in H; destruct H as [-> |]; solve_bounds.
      - intros rho x. cbn; destruct (zero_or_succ x) as [-> | [x' ->]]; cbn; split.
        + intros _. now right.
        + intros _. exists i0. now rewrite add_zero.
        + rewrite lt_SS. now intros ?%nolessthen_zero.
        + intros [?%nolessthen_zero | E]. tauto.
          symmetry in E. now apply zero_succ in E.
      - intros y IH rho x; cbn; destruct (zero_or_succ x) as [-> | [x' ->]].
        + split.
        ++ intros _. left. exists y. now rewrite add_zero.
        ++ intros _. exists (iσ y). now rewrite add_zero.
        + rewrite !lt_SS, !succ_inj'.
          specialize (IH rho x'). apply IH.
      - specialize (H e (fun _ => d) d). apply H.
    Qed.

    Lemma lt_le_trans {x z} y : x i⧀ y -> y i≤ z -> x i⧀ z.
    Proof.
      intros [k1 H1] [k2 H2]. exists (k1 i⊕ k2). rewrite H2, H1.
      now rewrite add_rec, add_asso.
    Qed.

    Lemma le_le_trans {x z} y : x i≤ y -> y i≤ z -> x i≤ z.
    Proof.
      intros [k1 H1] [k2 H2]. exists (k1 i⊕ k2). rewrite H2, H1.
      now rewrite add_asso.
    Qed.

    Lemma add_lt_mono x y t : x i⧀ y -> x i⊕ t i⧀ y i⊕ t.
    Proof.
      intros [k Hk]. exists k. rewrite Hk.
      now rewrite add_rec, !add_asso, (add_comm k t).
    Qed.

    Lemma add_le_mono x y t : x i≤ y -> x i⊕ t i≤ y i⊕ t.
    Proof.
      intros [k Hk]. exists k. rewrite Hk.
      now rewrite !add_asso, (add_comm k t).
    Qed.

    Lemma mult_le_mono x y t : x i≤ y -> x i⊗ t i≤ y i⊗ t.
    Proof.
      intros [k Hk]. exists (k i⊗ t). rewrite Hk.
      now rewrite distributive. 
    Qed.



    Section Euclid.

      (** ** Euclidean Lemma *)

      Lemma iEuclid : 
        forall x q, exists d r, x = d i⊗ q i⊕ r /\ (i0 i⧀ q -> r i⧀ q).
      Proof.
        intros x q.
        destruct (zero_or_succ q) as [-> | [q_ ->]].
        - exists i0, x. split.
          + rewrite mult_zero, add_zero. reflexivity.
          + now intros ?%nolessthen_zero.
        - pose (phi := ∀∃∃ $3 == $1 ⊗ (σ $2) ⊕ $0 ∧ (zero ⧀ (σ $2) --> $0 ⧀ (σ $2) ) ).
          assert (forall n rho, (n.:rho) ⊨ phi).
          apply induction. cbn. cbn in *. repeat solve_bounds.
          + intros rho d. cbn. exists i0, i0. fold i0. split.
            * now rewrite mult_zero, add_zero.
            * tauto.
          + intros x' IH rho q'. cbn.
            destruct (IH rho q') as [d' [r' [H ]]]. cbn in *.
            destruct (eq_dec r' q') as [<- | F].
            * exists (iσ d'), i0. split.
              rewrite add_zero_r, H.
              now rewrite <-add_rec_r, mult_rec, add_comm.
              tauto.
            * exists d', (iσ r'). split.
              now rewrite H, <-add_rec_r.
              intros _. rewrite lt_SS.
              assert (r' i≤ q') as G.
              { rewrite <-lt_le_equiv1.
                apply H0. exists q'. now rewrite add_zero. }
              destruct (trichotomy r' q') as [h |[h|h] ]; intuition.
              exfalso. specialize (lt_le_trans _ h G).
              intros. now apply (lt_neq q' q').
          + destruct (H x (fun _ => i0) q_) as [d [r [H1 H2]]]. cbn in H1, H2.
            exists d, r. split; auto.
      Qed.

      Lemma iFac_unique1 d q1 r1 q2 r2 : r1 i⧀ d ->
            r1 i⊕ q1 i⊗ d = r2 i⊕ q2 i⊗ d -> q1 i⧀ q2 -> False.
      Proof.
        intros H1 E H. revert E. apply lt_neq.
        apply lt_le_trans with (d i⊕ q1 i⊗ d).
        - now apply add_lt_mono.
        - rewrite <- !mult_rec.
          apply le_le_trans with (q2 i⊗ d).
          + apply mult_le_mono.
            destruct H as [k ->].
            exists k. now rewrite add_rec.
          + pattern (q2 i⊗ d) at 2.
            rewrite <-(add_zero (q2 i⊗ d)).
            apply add_le_mono.
            exists r2. now rewrite add_zero.
      Qed.


      (** ** Uniqueness for the Euclidean Lemma *)
      
      Lemma iFac_unique q d1 r1 d2 r2 : r1 i⧀ q -> r2 i⧀ q ->
            r1 i⊕ d1 i⊗ q = r2 i⊕ d2 i⊗ q -> d1 = d2 /\ r1 = r2.
      Proof.
        intros H1 H2 E.
        assert (d1 = d2) as ->.
        - destruct (trichotomy d1 d2) as [ H | [ | H ]]; auto.
          + exfalso. eapply iFac_unique1. 2: apply E. all: tauto.
          + exfalso. eapply iFac_unique1. symmetry in E.
            3: apply H. apply H2. eauto.
        - repeat split. now apply add_eq in E.
      Qed.


    End Euclid. 



    Lemma lessthen_num : forall n d, d i⧀ inu n -> exists k, k < n /\ d = inu k.
    Proof.
      induction n ; intros d H.
      - now apply nolessthen_zero in H.
      - destruct (zero_or_succ d) as [-> | [e ->]].
        exists 0; split; auto; lia.
        cbn in H; apply ->lt_SS in H.
        apply IHn in H.
        destruct H as [k []].
        exists (S k); split. lia. cbn; congruence.
    Qed.


    Lemma iEuclid' : forall x y, 0 < y -> exists a b, b < y /\ x = a i⊗ inu y i⊕ inu b.
      Proof.
        intros x y.
        destruct y as [|y]. lia.
        destruct (iEuclid x (inu (S y))) as (a & b & H).
        intros Hy.
        enough (Hlt : forall x y, x < y -> inu x i⧀ inu y).
        apply Hlt, H, lessthen_num in Hy.
        destruct Hy as [r [Hr ->]].
        exists a, r. split.
        apply Hr. apply H.
        intros n m [k <-]%lt_nat_equiv.
        exists (inu k); cbn. now rewrite inu_add_hom.
      Qed.

  End PA_Model.


End Models.



Arguments PAsat {_ _} _.
Notation "'PA⊨' phi" := (forall D (I : interp D) rho, (forall psi : form, PA psi -> rho ⊨ psi) -> rho ⊨ phi) (at level 30).

(** ** Standard Model of PA *)

Section StandartModel.

  Definition interp_nat : interp nat.
  Proof.
    split.
    - destruct f; intros v.
      + exact 0.
      + exact (S (Vector.hd v) ).
      + exact (Vector.hd v + Vector.hd (Vector.tl v) ).
      + exact (Vector.hd v * Vector.hd (Vector.tl v) ).
    - destruct P.
  Defined.


  (* We now show that there is a model in which all of PA's axioms hold. *)
  Lemma PA_std_axioms :
    forall rho ax, PA ax -> @sat _ _ nat interp_nat _ rho ax. 
  Proof.
    intros rho ax [a H | H].
    repeat (destruct H as [<-| H]); cbn ; try congruence.
    intros []. auto. 
    - right. exists n; auto. 
    - destruct H.
    - intros H0 IH. intros d. induction d.
      + apply sat_single in H0. apply H0.
      + apply IH in IHd. 
        eapply sat_comp, sat_ext in IHd.
        apply IHd. intros []; now cbn.
  Qed.

  Lemma Q_std_axioms :
    forall rho ax, In ax Q -> @sat _ _ nat interp_nat _ rho ax. 
  Proof.
    intros rho ax H.
    repeat (destruct H as [<-| H]); cbn ; try congruence.
    - intros []; auto. right. exists n; auto. 
    - destruct H.
  Qed.



  Fact inu_nat_id : forall n, @inu nat interp_nat n = n.
  Proof.
    induction n; cbn; congruence.
  Qed.


End StandartModel.



Arguments inu {_ _} _.



Section ND.

  Variable p : peirce.

  Fixpoint iter {X: Type} f n (x : X) :=
    match n with
      0 => x
    | S m => f (iter f m x)
    end.

  Fact iter_switch {X} f n x : f (@iter X f n x) = iter f n (f x).
  Proof. induction n; cbn; now try rewrite IHn. Qed.


  Lemma subst_up_var k x sigma :
    x < k -> (var x)`[iter up k sigma] = var x.
  Proof.
    induction k in x, sigma |-*.
    - now intros ?%PeanoNat.Nat.nlt_0_r.
    - intros H.
      destruct (Compare_dec.lt_eq_lt_dec x k) as [[| <-]|].
      + cbn [iter]. rewrite iter_switch. now apply IHk.
      + destruct x. reflexivity.
        change (iter _ _ _) with (up (iter up (S x) sigma)).
        change (var (S x)) with ((var x)`[↑]).
        rewrite up_term, IHk. reflexivity. constructor.
      + lia.
  Qed.


  Lemma subst_bounded_term t sigma k : 
    bounded_t k t -> t`[iter up k sigma] = t.
  Proof.
    induction 1.
    - now apply subst_up_var.
    - cbn. f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in. auto.
  Qed.


  Lemma subst_closed_term t sigma :
    bounded_t 0 t -> t`[sigma] = t.
  Proof.
    intros H0.
    refine (_ (subst_bounded_term t sigma 0 H0)).
    now cbn.
  Qed.


  Lemma subst_bounded k phi sigma : 
    bounded k phi -> phi[iter up k sigma] = phi.
  Proof.
    induction 1 in sigma |-*; cbn.
    - f_equal.
      rewrite <-(Vector.map_id _ _ v) at 2.
      apply Vector.map_ext_in.
      intros t Ht. apply subst_bounded_term. auto.
    - now rewrite IHbounded1, IHbounded2.
    - f_equal; now apply subst_bounded_term.
    - f_equal.
      change (up _) with (iter up (S n) sigma).
      apply IHbounded.
    - reflexivity.
  Qed.


  Definition exist_times n (phi : form) := iter (fun psi => ∃ psi) n phi.


  Lemma up_decompose sigma phi : 
    phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.


  Lemma subst_exist_prv {sigma N Gamma} phi :
    Gamma ⊢ phi[sigma] -> bounded N phi -> Gamma ⊢ exist_times N phi. 
  Proof.
    induction N in phi, sigma |-*; intros; cbn.
    - erewrite <-(subst_bounded 0); eassumption.
    - rewrite iter_switch. eapply (IHN (S >> sigma)).
      cbn. eapply (ExI (sigma 0)).
      now rewrite up_decompose.
      now apply bounded_S_exists.
  Qed.


  Lemma subst_forall_prv phi {N Gamma} :
    Gamma ⊢ (forall_times N phi) -> bounded N phi -> forall sigma, Gamma ⊢ phi[sigma].
  Proof.
    induction N in phi |-*; intros ?? sigma; cbn in *.
    - change sigma with (iter up 0 sigma).
      now rewrite (subst_bounded 0).
    - specialize (IHN (∀ phi) ).
      rewrite <-up_decompose.
      apply AllE. apply IHN.
      unfold forall_times. now rewrite <-iter_switch.
      now apply bounded_S_forall.
  Qed.

End ND.



Fixpoint join {X n} (v : Vector.t X n) (rho : nat -> X) :=
    match v with
    | Vector.nil _ => rho
    | Vector.cons _ x n w  => join w (x.:rho)
    end.

Notation "v '∗' rho" := (join v rho) (at level 20).

 
Section Q_prv.

  Variable p : peirce.

  Variable Gamma : list form.
  Variable G : incl Q Gamma.

  Arguments Weak {_ _ _ _}, _.


  Lemma reflexivity t : Gamma ⊢ (t == t).
  Proof.
    apply (Weak Q).
    pose (sigma := [t] ∗ var ).
    change (Q ⊢ _) with (Q ⊢ ($0 == $0)[sigma]).
    eapply (@subst_forall_prv _ _ 1).
    apply Ctx. 
    - now left.
    - repeat solve_bounds.
    - assumption.
  Qed.


  Lemma symmetry x y : Gamma ⊢ (x == y) -> Gamma ⊢ (y == x).
  Proof.
    apply IE. apply (Weak Q).
    pose (sigma := [x ; y] ∗ var ).
    change (Q ⊢ _) with (Q ⊢ ($1 == $0 --> $0 == $1)[sigma]).
    apply (@subst_forall_prv _ _ 2).
    apply Ctx.
    - do 1 right; now left.
    - repeat solve_bounds.
    - assumption.
  Qed.


  Lemma transitivity x y z :
    Gamma ⊢ (x == y) -> Gamma ⊢ (y == z) -> Gamma ⊢ (x == z).
  Proof.
    intros H. apply IE. revert H; apply IE.
    apply Weak with Q.
    pose (sigma := [x ; y ; z] ∗ var).
    change (Q ⊢ _) with (Q ⊢ ($2 == $1 --> $1 == $0 --> $2 == $0)[sigma]).
    apply (@subst_forall_prv _ _ 3).
    apply Ctx.
    - do 2 right; now left.
    - repeat solve_bounds.
    - assumption.
  Qed.


  Lemma eq_succ x y : Gamma ⊢ (x == y) -> Gamma ⊢ (σ x == σ y).
  Proof.
    apply IE. apply Weak with Q.
    pose (sigma := [y ; x] ∗ var ).
    change (Q ⊢ _) with (Q ⊢ ($0 == $1 --> σ $0 == σ $1)[sigma]).
    apply (@subst_forall_prv _ _ 2).
    apply Ctx.
    - do 3 right; now left.
    - repeat solve_bounds.
    - assumption.
  Qed.


  Lemma eq_add {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊕ y1 == x2 ⊕ y2).
  Proof.
    intros H; apply IE. revert H; apply IE.
    apply Weak with Q.
    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (Q ⊢ _) with (Q ⊢ ($0 == $1 --> $2 == $3 --> $0 ⊕ $2 == $1 ⊕ $3)[sigma]).
    apply (@subst_forall_prv _ _ 4).
    apply Ctx.
    - do 4 right; now left.
    - repeat solve_bounds.
    - assumption.
  Qed.


  Lemma eq_mult {x1 y1 x2 y2} :
    Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊗ y1 == x2 ⊗ y2).
  Proof.
    intros H; apply IE. revert H; apply IE.
    apply Weak with Q.
    pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
    change (Q ⊢ _) with (Q ⊢ ($0 == $1 --> $2 == $3 --> $0 ⊗ $2 == $1 ⊗ $3)[sigma]).
    apply (@subst_forall_prv _ _ 4).
    apply Ctx.
    - do 5 right; now left.
    - repeat solve_bounds.
    - assumption.
  Qed.


  Lemma Zero_succ x : Gamma ⊢ ¬ zero == σ x.
  Proof.
    apply Weak with Q.
    pose (sigma := [x] ∗ var).
    change (Q ⊢ _) with (Q ⊢ (¬ zero == σ $0)[sigma]).
    apply (@subst_forall_prv _ _ 1).
    apply Ctx.
    - do 6 right; now left.
    - repeat solve_bounds.
    - assumption.
  Qed.


  Lemma Succ_inj x y : Gamma ⊢ σ x == σ y -> Gamma ⊢ x == y.
  Proof.
    intros H; eapply IE. 2: apply H.
    apply Weak with Q.
    pose (sigma := [x ; y] ∗ var).
    change (Q ⊢ _) with (Q ⊢ (σ $1 == σ $0 --> $1 == $0)[sigma]).
    apply (@subst_forall_prv _ _ 2).
    apply Ctx.
    - do 7 right; now left.
    - repeat solve_bounds.
    - assumption.
  Qed.



  Lemma Add_rec x y : Gamma ⊢ ( (σ x) ⊕ y == σ (x ⊕ y) ).
  Proof.
    apply Weak with Q.
    pose (sigma := [y ; x] ∗ var).
    change (Q ⊢ _) with (Q ⊢ (σ $0 ⊕ $1 == σ ($0 ⊕ $1))[sigma]).
    apply (@subst_forall_prv _ _ 2).
    apply Ctx. 
    - do 9 right; now left.
    - repeat solve_bounds.
    - assumption.
  Qed.

  (** * Homomorphism Properties of Numerals *)

  Lemma num_add_homomorphism  x y : Gamma ⊢ ( num x ⊕ num y == num (x + y) ).
  Proof.
    induction x; cbn.
    - pose (phi := zero ⊕ $0 == $0).
      apply (@AllE _ _ _ _ _ _ phi ).
      apply Weak with Q.
      apply Ctx. do 8 right; now left.
      assumption.
    - eapply transitivity.
      apply Add_rec.
      now apply eq_succ.
  Qed.


  Lemma Mult_rec x y : Gamma ⊢ ( (σ x) ⊗ y == y ⊕ (x ⊗ y) ).
  Proof.
    apply Weak with Q.
    pose (sigma := [x ; y] ∗ var).
    change (Q ⊢ _) with (Q ⊢ ((σ $1) ⊗ $0 == $0 ⊕ ($1 ⊗ $0))[sigma]).
    eapply (@subst_forall_prv _ _ 2).
    apply Ctx. 
    - do 11 right; now left.
    - repeat solve_bounds.
    - assumption. 
  Qed.


  Lemma num_mult_homomorphism (x y : nat) : Gamma ⊢ ( num x ⊗ num y == num (x * y) ).
  Proof.
    induction x; cbn.
    - pose (phi := zero ⊗ $0 == zero).
      apply (@AllE _ _ _ _ _ _ phi).
      apply Weak with Q. apply Ctx; do 10 right; now left.
      assumption.
    - eapply transitivity.
      apply Mult_rec.
      eapply transitivity.
      2: apply num_add_homomorphism.
      apply eq_add. apply reflexivity. apply IHx.
  Qed.


  Lemma num_lt_prv x y : x < y <-> Gamma ⊢ (num x ⧀ num y).
  Proof.
    split.
    - intros H.
      change (Gamma ⊢ exist_times 1 ( (num y)`[↑] == σ ((num x)`[↑] ⊕ $0))).
      specialize H as [k <-]%lt_nat_equiv.
      pose (sigma := [num x ; num k] ∗ var).
      eapply subst_exist_prv with (sigma := sigma).
      cbn. rewrite !num_subst.
      apply eq_succ, symmetry.
      apply num_add_homomorphism.
      solve_bounds.
  Abort.


End Q_prv.


Section Q_prv.

  Variable p : peirce.

  Variable Gamma : list form.
  Variable G : incl Q Gamma.


  Lemma better_leibniz sigma phi rho A : (forall n, A ⊢ (sigma n == rho n)) -> A ⊢ phi[sigma] -> A ⊢ phi[rho].
  Proof.
  Abort.


  Derive Signature for Vector.t.
  
  Lemma vec_nil_eq X (v : vec X 0) :
    v = Vector.nil X.
  Proof.
    depelim v. reflexivity.
  Qed.

  Lemma vec_inv1 X (v : vec X 1) :
    v = [ Vector.hd v ].
  Proof.
    repeat depelim v. cbn. reflexivity.
  Qed.

  Lemma vec_inv2 X (v : vec X 2) :
    v = [ Vector.hd v ; Vector.hd (Vector.tl v) ].
  Proof.
    repeat depelim v. cbn. reflexivity.
  Qed.

  Lemma map_hd X Y n (f : X -> Y) (v : vec X (S n)) :
    Vector.hd (Vector.map f v) = f (Vector.hd v).
  Proof.
    depelim v. reflexivity.
  Qed.

  Lemma map_tl X Y n (f : X -> Y) (v : vec X (S n)) :
    Vector.tl (Vector.map f v) = Vector.map f (Vector.tl v).
  Proof.
    depelim v. reflexivity.
  Qed.

  Lemma vec_in_hd X n (v : vec X (S n)) :
    vec_in (Vector.hd v) v.
  Proof.
    depelim v. constructor.
  Qed.

  Lemma vec_in_hd_tl X n (v : vec X (S (S n))) :
    vec_in (Vector.hd (Vector.tl v)) v.
  Proof.
    depelim v. constructor. depelim v. constructor.
  Qed.

  Lemma in_hd X n (v : vec X (S n)) :
    Vector.In (Vector.hd v) v.
  Proof.
    depelim v. constructor.
  Qed.

  Lemma in_hd_tl X n (v : vec X (S (S n))) :
    Vector.In (Vector.hd (Vector.tl v)) v.
  Proof.
    depelim v. constructor. depelim v. constructor.
  Qed.


  (** * Closed terms are numerals. *)

  Lemma closed_term_is_num s : bounded_t 0 s -> { n & Gamma ⊢ s == num n }.
  Proof.
    pattern s; revert s. apply term_rect.
    - intros ? H. exists 0. inversion H; lia.
    - intros [] v N H; cbn in v.
      + exists 0. rewrite (vec_nil_eq _ v).
        now apply reflexivity.
      + rewrite (vec_inv1 _ v).
        destruct (N (Vector.hd v)) as [n Hn].
        apply vec_in_hd.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd. decide equality.
        exists (S n); cbn. now apply eq_succ.
      + rewrite (vec_inv2 _ v).
        remember (Vector.hd v) as x eqn:Hx.
        remember (Vector.hd (Vector.tl v)) as y eqn:Hy.
        destruct (N x) as [n Hn].
        rewrite Hx. apply vec_in_hd.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd. decide equality.
        destruct (N y) as [m Hm].
        rewrite Hy. apply vec_in_hd_tl.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd_tl. decide equality.
        exists (n + m).
        eapply transitivity.
        3 : apply num_add_homomorphism.
        all: try assumption.
        now apply eq_add.
      + rewrite (vec_inv2 _ v).
        remember (Vector.hd v) as x eqn:Hx.
        remember (Vector.hd (Vector.tl v)) as y eqn:Hy.
        destruct (N x) as [n Hn].
        rewrite Hx. apply vec_in_hd.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd. decide equality.
        destruct (N y) as [m Hm].
        rewrite Hy. apply vec_in_hd_tl.
        inversion H. subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2 as ->.
        apply H1. apply in_hd_tl. decide equality.
        exists (n * m).
        eapply transitivity.
        3 : apply num_mult_homomorphism.
        all: try assumption.
        now apply eq_mult.
  Qed.


  Fact num_eq x y : x = y -> Gamma ⊢ num x == num y.
  Proof.
    intros ->. now apply reflexivity.
  Qed.

  Lemma num_neq x : forall y, x <> y -> Gamma ⊢ ¬ num x == num y.
  Proof.
    induction x as [| x IHx].
    - intros [] neq.
      + congruence.
      + now apply Zero_succ.
    - intros [|y] neq.
      + apply II. eapply IE with (phi := num 0 == num (S x)).
        eapply Weak with Gamma. now apply Zero_succ.
        firstorder.
        apply symmetry; [now right; apply G|].
        apply Ctx. now left.
      + apply II. eapply IE with (phi := num x == num y).
        { eapply Weak with Gamma. apply IHx. 
          - lia. 
          - now right. }
        apply Succ_inj. 
        ++ now right; apply G.
        ++ apply Ctx. now left.
  Qed. 


  Lemma num_eq_dec x y : { Gamma ⊢ num x == num y } + { Gamma ⊢ ¬ num x == num y }.
  Proof.
    destruct (dec_eq_nat x y); [left|right].
    - now apply num_eq.
    - now apply num_neq.
  Qed.  


  (** * Provability of equality for closed terms is decidable. *)
  
  Lemma term_eq_dec s t : 
    bounded_t 0 s -> bounded_t 0 t -> { Gamma ⊢ s == t } + { Gamma ⊢ ¬ s == t }.
  Proof.
    intros Hs Ht.
    destruct (closed_term_is_num s Hs) as [n Hn], (closed_term_is_num t Ht) as [m Hm].
    destruct (num_eq_dec n m) as [H|H].
    - left. eapply transitivity; eauto 1.
      eapply transitivity; eauto 1.
      apply symmetry; assumption.
    - right.
      apply II. eapply IE.
      apply Weak with Gamma; try apply H; firstorder.
      eapply transitivity. shelve.
      2 : eapply Weak with Gamma; try apply Hm.
      eapply transitivity. shelve.
      eapply Weak with Gamma. apply symmetry in Hn. apply Hn.
      assumption. shelve.
      apply Ctx. Unshelve.
      + now left.
      + now right.
      + right. now apply G.
      + right. now apply G.
      + now right.
  Qed.


  Lemma num_lt x y :
    x < y -> Gamma ⊢ num x ⧀ num y.
  Proof.
    intros [k Hk]%lt_nat_equiv.
    apply ExI with (t := num k). cbn.
    rewrite !num_subst, <-Hk. cbn.
    apply eq_succ. easy.
    apply symmetry, num_add_homomorphism; easy.
  Qed.

  Lemma not_lt_zero_prv' :
  Q ⊢ ∀ ¬ $0 ⧀ num 0.
  Proof.
    apply AllI, II. eapply ExE.
    - apply Ctx. now left.
    - cbn -[Q]. eapply IE.
      + pose (s := $1 ⊕ $0).
        apply Zero_succ with (x := s).
        right; now right.
      + apply Ctx. now left.
  Qed.

  Lemma not_lt_zero_prv t :
    Q ⊢ ¬ t ⧀ num 0.
  Proof.
    change (Q ⊢ (¬ $0 ⧀ num 0)[t..]).
    apply AllE, not_lt_zero_prv'.
  Qed.

  Lemma Faster3 :
    forall A, Q <<= A ++ map (subst_form ↑) Q.
  Proof.
    intros A; induction A; cbn -[Q].
    - firstorder.
    - right. now apply IHA.
  Qed.

  Lemma num_nlt x :
    forall y, ~ (x < y) -> Q ⊢ ¬ num x ⧀ num y.
  Proof.
    induction x as [| x IHx].
    - intros [] ineq.
      + apply not_lt_zero_prv.
      + lia.
    - intros [|y] ineq.
      + apply not_lt_zero_prv.
      + assert (~ x < y) as H % IHx by lia.
        apply II. eapply IE.
        { eapply Weak; [apply H | now right]. }
        eapply ExE.
        * apply Ctx. now left.
        * apply ExI with (t := $0).
          cbn -[Q]. rewrite !num_subst.
          eapply transitivity. right; now right.
          2 : {apply Add_rec. right; now right. }
          apply Succ_inj. right; now right.
          apply Ctx. now left.
  Qed. 

  Lemma num_lt_dec x y :
    { Gamma ⊢ num x ⧀ num y } + { Gamma ⊢ ¬ num x ⧀ num y }.
  Proof.
    destruct (lt_dec x y); [left|right].
    - now apply num_lt.
    - apply Weak with Q; [now apply num_nlt | assumption].
  Qed.


  Lemma term_lt_dec s t :
    map (subst_form ↑) Gamma = Gamma -> bounded_t 0 s -> bounded_t 0 t -> { Gamma ⊢ s ⧀ t } + { Gamma ⊢ ¬ s ⧀ t }.
  Proof.
    intros HG Hs Ht.
    destruct (closed_term_is_num s Hs) as [n Hn], (closed_term_is_num t Ht) as [m Hm].
    destruct (num_lt_dec n m) as [H|H].
    - left. eapply ExE. apply H.
      apply ExI with (t0:=$0).
      rewrite !num_subst, HG. cbn.
      repeat rewrite (subst_closed_term t), (subst_closed_term s); auto. 
      eapply transitivity.
      2 : { eapply Weak. apply Hm. now right. }
      now right; apply G.
      apply symmetry. now right; apply G.
      pose (j := σ (num n ⊕ $0)).
      eapply transitivity with (y:= j); unfold j. now right; apply G.
      apply eq_succ. now right; apply G.
      apply eq_add. now right; apply G.
      eapply Weak. apply Hn. now right.
      apply reflexivity. now right; apply G.
      apply symmetry. now right; apply G.
      apply Ctx; now left.
    - right. apply II. eapply IE.
      eapply Weak. apply H. now right.
      eapply ExE. apply Ctx; now left.
      apply ExI with (t0:=$0).
      cbn. rewrite !num_subst.
      repeat rewrite (subst_closed_term t), (subst_closed_term s), HG; auto.
      apply symmetry in Hm; auto.
      apply symmetry in Hn; auto.
      eapply transitivity.
      2 : { eapply Weak. apply Hm. right; now right. }
      now right; right; apply G.
      apply symmetry. now right; right; apply G.
      pose (j := σ (s ⊕ $0)).
      eapply transitivity with (y:= j); unfold j. 
      now right; right; apply G.
      apply eq_succ. now right; right; apply G.
      apply eq_add. now right; right; apply G.
      eapply Weak. apply Hn. now right; right.
      apply reflexivity. now right; right; apply G.
      apply symmetry. now right; right; apply G.
      apply Ctx; now left.
  Qed.


End Q_prv.
