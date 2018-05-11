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

Ltac done := intros; subst; simpl; InvertReflections; (
               match goal with
               | H : _ |- ~ _ => (progress inversion 1); done
               | R : reflect ?e _, H : ?e |- _ => move/R: H; done
               end
               || eassumption || easy || congruence || (intuition (eauto 4; fail) || omega)
               || ((progress ApplyOneHypothesis); done)
               || (econstructor; done)).

Ltac inv H := inversion H; subst; clear H.

Ltac dec_cases dec s l := match l with
                          | ?s0::?l0 => case (dec s s0); dec_cases dec s l0
                          | nil => idtac
                          end.

Ltac program_equiv_case_analysis :=
  match goal with
  | |- context[(if (is_left ?e) then _ else _)] => case e => ?; simpl
  | |- context[(if ?e then _ else _)] => destruct e; simpl
  | |- context[(match ?e with _ => _ end)] => destruct e; simpl
  end.

Ltac program_equiv := repeat program_equiv_case_analysis.

Fixpoint concatenation (l : list string) :=
  match l with
  | nil => ""%string
  | cons s l' => (s ++ (concatenation l'))%string
  end.

Theorem appendEmpty s : (s ++ "")%string = s. 
  elim: s => //=.
Qed.

Theorem appendSomething s s' : s' <> ""%string -> (s ++ s')%string <> s.
  elim: s => //=; move=> a s H /H; done.
Qed.

Theorem appendAssociative s s' s'' : ((s ++ s') ++ s'')%string = (s ++ (s' ++ s''))%string.
  elim: s => //=.
Qed.

Theorem diffLenDiffStr s : forall s', (String.length s) <> (String.length s') -> s <> s'.
  induction s; destruct 2; done.
Qed.

Theorem sumAppendLength s s' : String.length (s ++ s') = String.length s + String.length s'.
  elim: s => //=.
Qed.

Theorem concatenationLength {l s} : s ∈ l -> (String.length s) <= (String.length (concatenation l)).
  elim: l => //=.
  move=> a l imp; rewrite sumAppendLength; case => [-> | /imp ne].
  - exact: Plus.le_plus_l.
  - rewrite PeanoNat.Nat.add_comm; exact: Plus.le_plus_trans.
Qed.

Theorem concatenationNotAny {l s0 s} : (0 < (String.length s0)) -> s ∈ l -> s <> ((concatenation l) ++ s0)%string.
Proof with done.
  move=> size /concatenationLength H.
  pose (sumAppendLength (concatenation l) s0).
  pose (Plus.plus_le_lt_compat _ _ _ _ H size).
  rewrite <- e in l0.
  apply diffLenDiffStr.
  rewrite <- plus_n_O in l0.
  exact (PeanoNat.Nat.lt_neq _ _ l0).
Qed.

Theorem concatNotIn l : forall s, (0 < (String.length s)) -> ~ ((concatenation l) ++ s)%string ∈ l.
  move => s lt /concatenationNotAny H.
  move/(_ s lt) in H.
  done.
Qed.

Theorem ListFinite (l : list string) : exists x, ~ (x ∈ l).
  exists ((concatenation l) ++ "x")%string; exact: concatNotIn.
Qed.


