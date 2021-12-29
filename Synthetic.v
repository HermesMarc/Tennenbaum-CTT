Require Import Setoid.
Require Import ConstructiveEpsilon.


Definition iffT (X Y : Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition definite P := P \/ ~P.
Definition Definite {X} p := forall x : X, definite (p x).
Definition LEM := forall P, definite P.
Definition stable P := ~~P -> P.
Definition Stable {X} p := forall x : X, stable (p x).
Definition DNE := forall P, stable P.
Definition MP := forall (f : nat -> nat), stable (exists n, f n = 0).


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
Definition  quasi_covers X Y := ex (quasi_convering X Y).

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
Admitted.


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


Fact Markov_quasi_covers {X Y} :
  Markov X -> quasi_covers X Y -> Discrete Y -> Markov Y.
Proof.
Admitted.


