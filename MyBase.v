From Coq Require Import ssreflect ssrfun ssrbool Lists.List String Basics.
Require Import Omega.
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

Ltac ApplyOneHypothesis := multimatch goal with H: _ |- _  => eapply H; clear H end.

Ltac InvertReflections := repeat match goal with
                                 | H : reflect _ true |- _ => inversion H; clear H
                                 | H : reflect _ false |- _ => inversion H; clear H
                                 end.

Ltac elim_sumbool e := move/sumboolP: e.
Ltac elim_sumbools dec := repeat match goal with
                                 | H : context[dec _ _] |- _ => move/sumboolP in H
                                 end.

Ltac split_iff := match goal with H: iff _ _ |- _ => case H end.
Ltac split_iffs := repeat split_iff.

Ltac program_equiv_case_analysis :=
  lazymatch goal with
  | |- context[(if (_ ?e) then _ else _)] => destruct e eqn:?; simpl
  | |- context[(if ?e then _ else _)] => destruct e eqn:?; simpl
  | |- context[(match ?e with _ => _ end)] => destruct e eqn:?; simpl
  end.

Ltac program_equiv := repeat program_equiv_case_analysis.

Ltac done_rec := 
  intros; subst; simpl in *; InvertReflections; split_iffs; (
    match goal with
    | H : _ |- ~ _ => (progress inversion 1); done_rec
    | R : reflect ?e _, H : ?e |- _ => move/R in H; done_rec
    | |- iff _ _ => split; inversion 1; done_rec
    end
    || eassumption || easy || congruence || (intuition (eauto 4; fail) || omega)
    || ((progress ApplyOneHypothesis); done_rec)
    || (econstructor; done_rec)).

Ltac done := subst; simpl in *; repeat (program_equiv; intro); done_rec.

Ltac inv H := inversion H; subst; clear H.

Ltac dec_cases dec s l := match l with
                          | ?s0::?l0 => case (dec s s0); dec_cases dec s l0
                          | nil => idtac
                          end.

Fixpoint concatenation (l : list string) :=
  match l with
  | nil => ""%string
  | cons s l' => (s ++ (concatenation l'))%string
  end.

Theorem appendEmpty s : (s ++ "")%string = s. 
  by induction s.
Qed.

Theorem appendSomething s s' : s' <> ""%string -> (s ++ s')%string <> s.
  by induction s.
Qed.

Theorem appendAssociative s s' s'' : ((s ++ s') ++ s'')%string = (s ++ (s' ++ s''))%string.
  by induction s.
Qed.

Theorem diffLenDiffStr s : forall s', (String.length s) <> (String.length s') -> s <> s'.
  by induction s.
Qed.

Theorem sumAppendLength s s' : String.length (s ++ s') = String.length s + String.length s'.
  by induction s.
Qed.

Theorem concatenationLength {l s} : s ∈ l -> (String.length s) <= (String.length (concatenation l)).
  by elim: l => //= a l imp; rewrite sumAppendLength; case => [-> | /imp ne].
Qed.

Theorem concatenationNotAny {l s0 s} : (0 < (String.length s0)) -> s ∈ l -> s <> ((concatenation l) ++ s0)%string.
  by move=> size /concatenationLength H; apply diffLenDiffStr; rewrite sumAppendLength.
Qed.

Theorem concatNotIn l : forall s, (0 < (String.length s)) -> ~ ((concatenation l) ++ s)%string ∈ l.
    by move => s lt /concatenationNotAny H.
Qed.

Theorem ListFinite (l : list string) : exists x, ~ (x ∈ l).
  by exists ((concatenation l) ++ "x")%string; apply/concatNotIn.
Qed.


