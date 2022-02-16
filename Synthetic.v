Require Import Setoid.
Require Import ConstructiveEpsilon.


Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Definition surj {X Y} (f : X -> Y) := forall y, exists x, f x = y.
Definition inj {X Y} (f : X -> Y) := forall x x', f x = f x' -> x = x'.  

Definition definite P := P \/ ~P.
Definition Definite {X} p := forall x : X, definite (p x).
Definition LEM := forall P, definite P.
Definition stable P := ~~P -> P.
Definition Stable {X} p := forall x : X, stable (p x).
Definition DNE := forall P, stable P.
Definition MP := forall (f : nat -> nat), stable (exists n, f n = 0).
Definition UC X Y := forall R, (forall x:X, exists! y:Y, R x y) -> exists f, forall x, R x (f x).

Fact LEM_DNE :
  (LEM <-> DNE) /\ (DNE -> MP).
Proof.
  unfold LEM, DNE, MP. repeat split.
  - intros lem p. now destruct (lem p).
  - intros dne p. apply dne. unfold definite; tauto.
  - intros dne f. apply dne.
Qed.


Fact DN_remove {A B} : 
  ~~A -> (A -> ~B) -> ~B.
Proof. tauto. Qed.

Fact DN_chaining {A B : Prop} : 
  ~ ~ A -> ~ ~(A -> B) -> ~ ~ B.
Proof. tauto. Qed.

Fact DN {A : Prop} :
  A -> ~~A.
Proof. tauto. Qed.

Fact NNN_N A :
  ~~~A <-> ~A.
Proof. tauto. Qed.

Fact DN_forall_stable {X} p :
  Stable p -> (forall x : X, ~~p x) -> forall x, p x.
Proof. unfold Stable; firstorder. Qed.



Definition decider {X} p f := forall x : X, p x <-> f x = true.
Definition Dec {X} p := inhabited(forall x : X, {p x} + {~p x}).
Definition Dec_sigT {X} p := forall x : X, {p x} + {~p x}.
Definition dec (P : Prop) := {P} + {~P}.
Definition witnessing {X} (p : X -> Prop) := ex p -> sigT p.
Definition enumerable {X} p := exists f : nat -> option X, forall x, p x <-> exists n, f n = Some x.

Definition convering X Y (f :  X -> option Y) := forall y, exists x, f x = Some y.
Definition covers X Y := sigT (convering X Y). 
Definition quasi_convering X Y (f :  X -> option Y) := forall y, ~~ exists x, f x = Some y.
Definition quasi_covers X Y := ex (quasi_convering X Y).

Definition Enumerable X := exists f : nat -> option X, forall x, exists n, f n = Some x.
Definition Discrete X := Dec (fun p : X * X => fst p = snd p).
Definition Separated X := Dec (fun p : X * X => fst p <> snd p).
Definition Markov X := forall p : X -> Prop, Dec p -> (~~ ex p) -> ex p.
Definition Witnessing X := forall p : X -> Prop, Dec_sigT p -> witnessing p.


Fact Dec_decider {X} p :
  Dec p <-> ex (@decider X p).
Proof.
  split.
  - intros [D].
    exists (fun x => if D x then true else false).
    intros x. destruct (D x); cbn; intuition congruence.
  - intros [f decf]. constructor. intros x.
    specialize (decf x). 
    destruct (f x) eqn:Hx; [left; tauto|right].
    now intros ?%decf.
Qed.

Fact Dec_decider_nat p :
  Dec p -> exists f : nat -> nat, forall x : nat, p x <-> f x = 0.
Proof.
  intros [f decf]%Dec_decider.
  exists (fun n => if f n then 0 else 1).
  intros x. specialize (decf x).
  destruct (f x) eqn:Hx; try tauto.
  rewrite decf. split; congruence.
Qed.


Fact Dec_sigT_decider {X} p :
  Dec_sigT p <=> sigT (@decider X p).
Proof.
  split.
  - intros D.
    exists (fun x => if D x then true else false).
    intros x. destruct (D x); cbn; intuition congruence.
  - intros [f decf]. intros x.
    specialize (decf x). 
    destruct (f x) eqn:Hx; [left; tauto|right].
    now intros ?%decf.
Qed.


Fact dec_Dec_sig_T P :
  dec P <=> Dec_sigT (fun _ : True => P).
Proof.
  split.
  - intros []; now constructor.
  - intros []; unfold dec; tauto.
Qed.


Lemma DN_Dec_equiv X (p : X -> Prop) :
  ~ ~ Dec p <-> ((Dec_sigT p -> False) -> False).
Proof.
  split.
  - intros nnH. apply (DN_remove nnH). 
    intros [H]. intros nH. apply nH. 
    intros x. apply H.
  - intros nnH nH. apply nnH. intros H.
    apply nH. constructor. apply H.
Qed.


Definition Witnessing_nat : Witnessing nat.
Proof.
  intros p Dec_p H.
  specialize (constructive_indefinite_ground_description_nat p Dec_p H). 
  intros [x Hx]. now exists x.
Defined.


Fact Discrete_sum {X} :
  Discrete X <-> inhabited(forall x y : X, {x = y} + {~ x = y}).
Proof.
  split; intros [H]; constructor.
  - intros x y. destruct (H (x,y)); cbn in *; tauto.
  - intros [x y]; cbn. destruct (H x y); tauto.
Qed.


Fact Separated_sum {X} :
  Separated X <-> inhabited(forall x y : X, {~ x = y} + {~~ x = y}).
Proof.
  split; intros [H]; constructor.
  - intros x y. destruct (H (x,y)); cbn in *; tauto.
  - intros [x y]; cbn. destruct (H x y); tauto.
Qed.


Fact enumerable_nat p :
  enumerable p -> exists f, forall x : nat, p x <-> exists n : nat, f n = S x.
Proof. 
  intros [f Hf].
  exists (fun n => match f n with Some x => S x | _ => 0 end).
  intros x. rewrite Hf. split; intros [n Hn]; exists n. 
  - now rewrite Hn.
  - destruct (f n); congruence.
Qed.


Fact enumerable_equiv X :
  Enumerable X <-> enumerable (fun x : X => True).
Proof.
  split; intros [g Hg]; exists g; firstorder.
Qed.


Fact MP_Markov_nat :
  MP <-> Markov nat.
Proof.
  split.
  - intros mp p [Dec_p] nnH.
    specialize (mp (fun x => if Dec_p x then 0 else 1)).
    destruct mp as [n Hn].
    + apply (DN_chaining nnH), DN.
      intros [n Hn]. exists n.
      destruct (Dec_p n) eqn:fn; congruence.
    + exists n. destruct (Dec_p n) eqn:?; congruence.
  - intros markov f.
    refine (markov (fun n => f n = 0) _).
    constructor; intros ?.
    decide equality.
Qed.


Fact MP_Dec_stable :
  MP -> forall (p : nat -> Prop), Dec p -> stable (ex p).
Proof.
  intros mp p [f Hf]%Dec_decider nnH.
  destruct (mp (fun n => if f n then 0 else 1)) as [y Hy].
  - apply (DN_chaining nnH), DN. intros [y Hy].
    exists y. apply Hf in Hy. now destruct (f y).
  - exists y. apply Hf. now destruct (f y).
Qed.


Fact Witnessing_covers {X Y} :
  Witnessing X -> covers X Y -> Witnessing Y.
Proof.
  intros WO_X [g Hg] p Dec_p H.
  enough (exists x, match g x with Some y => p y | _ => False end) as [x Gx]%WO_X.
  - destruct (g x); now eauto.
  - intros x. destruct (g x); auto.
  - destruct H as [x' ], (Hg x') as [x Hx].
    exists x. now rewrite Hx.
Qed.
