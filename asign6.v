From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Setoid.
Require Import FunInd.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Bool.Bool.
Require Import EqNat.
Require Import Coq.Init.Logic.
Require Import Coq.Program.Equality.
Require Import MyBase.
Require Import lang.
Require Import hoas.
Require Import static_semantics.
Require Import dynamic_semantics.
Require Import TypingContexts.
Open Scope LangContext_scope.

Lemma Weakening {Γ1 e τ Γ2} (sub: Γ1 ⊆ Γ2) : Γ1 ⊢ e ∷ τ -> Γ2 ⊢ e ∷ τ.
  by rewrite sub.
Qed.

Ltac weakening := apply/Weakening/(SubContextConsRight (SubContextRefl _)).

Lemma OtherWeakening {s e} (sNotIn : s ∉f e) : forall {Γ τ} (typechecks1 : Γ ⊢ e ∷ τ) {τ'}, (ConsEnv s τ' Γ) ⊢ e ∷ τ.
  elim: sNotIn; intros; match goal with H: _ ⊢ _ ∷ _ |- _ => inv H end.
  all: try done.
  all: econstructor; first done.
  - by apply/(EquivContextAlsoTypechecks (H _ _ type1 τ'))/EquivContextP => ? /=; program_equiv.
  - by apply/(EquivContextAlsoTypechecks type1)/EquivContextP => ? /=; program_equiv.
  - by apply/(EquivContextAlsoTypechecks type1)/EquivContextP => ? /=; program_equiv.
Qed.

Hint Resolve (@OtherWeakening).
Hint Resolve (@Weakening).

Lemma Substitution {e1 Γ1 τ1} (typechks1 : Γ1 ⊢ e1 ∷ τ1) : forall e2 e3 Γ2 τ2 s,
  (s ∷ τ2 ∈ Γ1) -> Γ2 ⊢ e2 ∷ τ2 -> Γ1 ≡ Γ2 % s -> [e2 / s] e1 = e3 -> Γ2 ⊢ e3 ∷ τ1.
  elim: typechks1; intros; match goal with | H : [ _ / _ ] _ = _ |- _ => inversion H end; subst.
  1,4,5,7,8: done.
  - by move/InContextP in H; move/InContextP in H0.
  - by move/(InterpretCongMod H2 neq) in H.
  - by have: s ∷ τ2 ∈ (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) /\
             (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ2)) ⊢ e2 ∷ τ2 by done.
Qed.

Lemma CannonicalForms {e τ} :
  NullEnv ⊢ e ∷ τ -> (𝕍 e) ->
  match τ with
  | NatType => exists n, e = (NatExpr n)
  | (AbsType τ1 τ2) => exists f x body, f<>x /\ (e = (AbsExpr f x τ1 τ2 body))
  end.
  by case.
Qed.

Lemma TypedEvalContextInversion {Γ E τ0 τ} : Γ ⊢ E {τ0} ∷ τ -> exists x, x ∉ Γ /\ (ConsEnv x τ0 Γ) ⊢ E[x] ∷ τ.
  by destruct 1; simpl; first by destruct (ContextFinite Γ).
Qed.

Lemma DecompositionOfTypes E : forall Γ e0 τ, Γ ⊢ E[e0] ∷ τ -> exists τ1, Γ ⊢ e0 ∷ τ1 /\ Γ ⊢ E {τ1} ∷ τ.
  induction E; intros; simpl in *; first done.
  all:inversion H.
  - by move/IHE: type1 => [τx [? b]]; move:(TypedEvalContextInversion b) => [? [? ?]].
  - by move/IHE: type2 => [τx [? b]]; move:(TypedEvalContextInversion b) => [? [? ?]].
  - by move/IHE: type1 => [τx [? b]]; move:(TypedEvalContextInversion b) => [? [? ?]].
  - by inversion type1; move/IHE: type2 => [τx [? b]]; move:(TypedEvalContextInversion b) => [? [? ?]].
Qed.

Definition CanStep e := exists e', e ⥛ e'.
Definition CanStepβ e := exists E e0 e1, e=E[e0] /\ e0 ⥛β e1.
Definition NotStuck e := 𝕍 e \/ (CanStep e).
Definition NotStuckβ e := 𝕍 e \/ (CanStepβ e).

Hint Constructors EvaluationContext.

Lemma Progressβ : forall {e τ} (ety: NullEnv ⊢ e ∷ τ), NotStuckβ e.
  elim => //=.
  - move=> x τ; inversion 1; inversion H1.
  - move => e1 H1 e2 H2 τ; inversion 1; right.
    move/(_ NatType type1): H1 => [/(CannonicalForms type1)-[n1 ->]| [E1 [e11 [e12 [-> step1]]]]].
    all:move/(_ NatType type2): H2 => [/(CannonicalForms type2)-[n2 ->]| [E2 [e21 [e22 [-> step2]]]]].
    + by exists Hole; exists (AddExpr n1 n2); exists (NatExpr (n1 + n2)).
    + by exists (EvalContextRAdd n1 E2).
    + by exists (EvalContextLAdd E1 n2).
    + by exists (EvalContextLAdd E1 (E2 [e21])).
  - move => e1 H1 e2 H2 τ; inversion 1; right.
    move/(_ (AbsType τ1 τ) type1): H1
    => [/(CannonicalForms type1)-[f [x [body [nefx ->]]]] | [E1 [e11 [e12 [-> step1]]]]].
    all:move/(_ τ1 type2): H2 => [v2| [E2 [e21 [e22 [-> step2]]]]].
    + exists Hole; exists (AppExpr (AbsExpr f x τ1 τ body) e2); simpl.
      move:(@CASAlways e2 x body (AlwaysSafeToSubInto _ _)) => [body' eq].
      move:(@CASAlways (AbsExpr f x τ1 τ body) f body' (AlwaysSafeToSubInto _ _)) => [body'' eq'].
      done.
    + by exists (EvalContextRApp f x τ1 τ body E2).
    + by exists (EvalContextLApp E1 e2).
    + by exists (EvalContextLApp E1 (E2 [e21])).
Qed.

Lemma Progress {e} : forall {τ} (etyp: NullEnv ⊢ e ∷ τ), (NotStuck e).
  by move=> τ /Progressβ; move=> [v | [E [e0 [e1 [-> bstep]]]]].
Qed.

Hint Resolve Progress.

Lemma βPreservation {e e'} (estep : e ⥛β e') : forall τ (etyp : NullEnv ⊢ e ∷ τ),  NullEnv ⊢ e' ∷ τ.
  induction estep; move=> τ0; inversion 1; first done.
  subst; inversion type1; subst.
  (have: ((ConsEnv f (τ1 → τ0) NullEnv) ⊢ e ∷ τ1) by done) => ?.
  by apply/Substitution; first by apply/Substitution.
Qed.

Lemma Preservation {e e'} (estep : e ⥛ e') τ (etyp : NullEnv ⊢ e ∷ τ) : NullEnv ⊢ e' ∷ τ.
  inversion estep; subst.
  move: (DecompositionOfTypes E e1 etyp) => [? [/(βPreservation betaStep) ? ?]].
  exact/InterpretTypedEvalContext.
Qed.

Hint Resolve Preservation.

Lemma Safety {e τ} (etyp : NullEnv ⊢ e ∷ τ) {e'} (estep : e ⥛* e') : (NotStuck e').
  by induction estep.
Qed.


