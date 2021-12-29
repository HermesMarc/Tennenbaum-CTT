Require Import CantorPairing Synthetic.
Require Import Lia.


Lemma Dec_sigT_transport {X} p q :
  Dec_sigT p -> (forall x : X, p x <-> q x) -> Dec_sigT q.
Proof.
  intros Dec_p Equiv. intros x.
  destruct (Dec_p x) as [H|H];
  [left | right]; firstorder.
Qed.

Lemma Dec_transport {X} p q :
  Dec p -> (forall x : X, p x <-> q x) -> Dec q.
Proof.
  intros [Dec_p] Equiv. 
  constructor. intros x.
  destruct (Dec_p x) as [H|H];
  [left | right]; firstorder.
Qed.



Lemma dec_eq_nat (x y : nat) : dec (x = y).
Proof.
  unfold dec; decide equality.
Defined.

Lemma lt_dec x y : dec (x < y).
Proof.
  induction y in x |-*.
  - right. lia.
  - destruct x.
    left. lia.
    destruct (IHy x).
    left; lia. right; lia.
Qed.

Lemma dec_conj A B : dec A -> dec B -> dec (A /\ B).
Proof.
  intros [][]; unfold dec; intuition.
Defined.

Lemma dec_disj A B : dec A -> dec B -> dec (A \/ B).
Proof.
  intros [][]; unfold dec; intuition.
Defined.


Lemma dec_imp A B : dec A -> dec B -> dec (A -> B).
Proof.
  intros [][]; unfold dec; intuition.
Defined.

Lemma dec_neg A : dec A -> dec (~ A).
Proof.
  intros []; unfold dec; now (left + right).
Defined.

Lemma neg_and A B : dec A -> dec B -> ~(A /\ B) -> (~A \/ ~B).
Proof.
  intros [][] ?; tauto.
Defined.

Lemma neg_imp A B : dec A -> dec B -> ~(A -> B) -> A /\ ~B.
Proof.
  intros [][] ?; tauto.
Qed.


Hint Resolve neg_and neg_imp dec_eq_nat dec_conj dec_disj dec_imp dec_neg : decs.

(** * Decidability of bounded quantifiers. *)

Lemma dec_lt_bounded_sig N (p : nat -> Type) :
  (forall x, p x + (p x -> False)) -> { x & ((x < N) * p x)%type } + (forall x, x < N -> p x -> False).
Proof.
  intros Dec_p. induction N.
  right. intros []; lia.
  destruct (IHN) as [IH | IH].
  - left. destruct IH as [x Hx].
    exists x. split. destruct Hx. lia. apply Hx.
  - destruct (Dec_p N) as [HN | HN]. 
    + left. exists N. split. lia. apply HN.
    + right. intros x Hx.
      assert (x = N \/ x < N) as [->|] by lia; auto.
      now apply IH.
Defined.


Lemma dec_lt_bounded_exist' N p :
  Dec_sigT p -> (exists x, x < N /\ p x) + (forall x, x < N -> ~ p x).
Proof.
  intros Dec_p. induction N.
  right. intros []; lia.
  destruct (IHN) as [IH | IH].
  - left. destruct IH as [x Hx].
    exists x. split. lia. apply Hx.
  - destruct (Dec_p N) as [HN | HN]. 
    + left. exists N. split. lia. apply HN.
    + right. intros x Hx.
      assert (x = N \/ x < N) as [->|] by lia; auto.
Defined.


Lemma dec_lt_bounded_exist N p :
  Dec_sigT p -> dec (exists x, x < N /\ p x).
Proof.
  intros Dec_p.
  destruct (dec_lt_bounded_exist' N p Dec_p).
  now left. right. firstorder.
Defined.


Lemma dec_lt_bounded_forall N p :
  Dec_sigT p -> dec (forall x, x < N -> p x).
Proof.
  intros Dec_p. induction N.
  left. lia.
  destruct (Dec_p N) as [HN | HN].
  - destruct (IHN) as [IH | IH].
    +  left. intros x Hx.
    assert (x = N \/ x < N) as [->|] by lia; auto.
    + right. intros H. apply IH.
      intros x Hx. apply H. lia.
  - right. intros H. apply HN.
    apply H. lia. 
Defined.


Lemma neg_lt_bounded_forall N p : 
  Dec_sigT p -> (~ forall x, x < N -> p x) -> exists x, x < N /\ ~ p x. 
Proof.
  intros Hp H.
  induction N. exfalso. apply H; lia.
  destruct (Hp N).
  - destruct IHN as [n ]. 
    + intros H1. apply H. intros.
      assert (x = N \/ x < N) as [->|] by lia. 
      auto. now apply H1.
    + exists n. intuition lia. 
  - exists N. auto.
Qed.



(** ** The product type for Nat is witnessing. *)

Theorem ProductWO (p : nat -> nat -> Prop) : 
  ( forall x y, dec (p x y) ) -> (exists x y, p x y) -> { x & { y & p x y }}.
Proof.
  intros Dec_p H.
  pose (P n := let (x, y) := decode n in p x y).
  assert ({n & P n}) as [n Hn].
  apply Witnessing_nat.
  - intros n.
    destruct (decode n) as [x y] eqn:E.
    destruct (Dec_p x y); (left + right); unfold P; now rewrite E.
  - destruct H as (x & y & H).
    exists (code (x, y)). unfold P.
    now rewrite inv_dc.
  - destruct (decode n) as [x y] eqn:E.
    exists x, y. unfold P in Hn; now rewrite E in Hn.
Qed.
