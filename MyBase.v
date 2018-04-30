From Coq Require Import ssreflect ssrfun ssrbool Lists.List String Basics.
Bind Scope MyListScope with list.
Reserved Notation "a ∈ b" (at level 1, no associativity).
Reserved Notation "a ∉ b" (at level 1, no associativity).
Notation "a ∈ b" := (In a b) : MyListScope.
Notation "a ∉ b" := (~ In a b) : MyListScope.
Open Scope MyListScope.
Lemma or_not_iff : forall (a b : Prop), (~(a \/ b)) <-> ((~a) /\ (~b)).
  intros a b.
  unfold not.
  split.
  - intros H.
    split.
    all:intros; refine (H _).
    + now left.
    + now right.
  - intros H H0.
    inversion H.
    now case H0.
Qed.
Definition distinct {A} (l1 l2 :list A) :=
  forall (dec : forall (a1 a2:A), {a1=a2}+{a1<>a2}) (l1 l2 : list A) e,
    (e ∈ l1 -> e ∉ l2) /\ (e ∈ l2 -> (e ∉ l1)).

Notation α := "α"%string.
Notation α1 := "α1"%string.
Notation α2 := "a2"%string.
Notation β := "β"%string.
Notation β1 := "β1"%string.
Notation β2 := "β2"%string.
Notation γ := "γ"%string.
Notation γ1 := "γ1"%string.
Notation γ2 := "γ2"%string.
Ltac done := subst; (eassumption || easy || congruence || tauto || (econstructor; done)).

Ltac inv H := inversion H; subst; clear H.

