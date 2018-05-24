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

Lemma CannonicalForms {Γ e τ} :
  Γ ⊢ e ∷ τ -> forall (v: 𝕍 e),
  match τ with
  | NatType => exists n, e = (NatExpr n)
  | (AbsType τ1 τ2) => exists f x body, f<>x /\ (e = (AbsExpr f x τ1 τ2 body))
  end.
  by case.
Qed.

Ltac Cannonicalize := repeat (match goal with
                              | V: 𝕍 ?e, T: _ ⊢ ?e ∷ _ |- _ =>
                                move: (CannonicalForms T V); intro; destruct V eqn:?
                              end).

Lemma TypedEvalContextInversion {Γ E τ0 τ} : Γ ⊢ E {τ0} ∷ τ -> exists x, x ∉ Γ /\ (ConsEnv x τ0 Γ) ⊢ E[x] ∷ τ.
  by induction 1; simpl; first by destruct (ContextFinite Γ).
Qed.

Lemma TypedBinopExprInversion {Γ f e1 e2 τ} : Γ ⊢ (BinExpr f e1 e2) ∷ τ -> exists τ1 τ2, Γ ⊢ e1 ∷ τ1 /\ Γ ⊢ e2 ∷ τ2.
  by inversion 1.
Qed.

Lemma DecompositionOfTypes E : forall Γ e0 τ, Γ ⊢ E[e0] ∷ τ -> exists τ1, Γ ⊢ e0 ∷ τ1 /\ Γ ⊢ E {τ1} ∷ τ.
  induction E; intros; simpl in *; first done.
  all: inversion H.
  - by move/IHE: type1 => [τx [? b]]; move:(TypedEvalContextInversion b) => [? [? ?]].
  - by move/IHE: type1 => [τx [? b]]; move:(TypedEvalContextInversion b) => [? [? ?]].
  - move/IHE: type2 => [τx [? b]]; move:(TypedEvalContextInversion b) => [? [? ?]].
    by Cannonicalize.
  - move/IHE: type2 => [τx [? b]]; move:(TypedEvalContextInversion b) => [? [? ?]].
    Cannonicalize; first done.
    intros; elim_exists.
    destruct H5.
    injection H6.
    done.
Qed.

Definition CanStep e := exists e', e ⥛ e'.
Definition CanStepEβ e := exists E e0 e1, e=E[e0] /\ e0 ⥛β e1.
Definition CanStepβ e := exists e', e ⥛β e'.
Definition NotStuck e := 𝕍 e \/ (CanStep e).
Definition NotStuckEβ e := 𝕍 e \/ (CanStepEβ e).
Definition NotStuckβ e := 𝕍 e \/ (CanStepβ e).

Hint Constructors EvaluationContext.

Ltac CAS := apply/CASAlways/AlwaysSafeToSubInto.

Lemma ProgressApp {Γ e1 e2 τ} : Γ ⊢ (BinExpr AppExpr e1 e2) ∷ τ -> (𝕍 e1) -> (𝕍 e2) -> exists e, (BinExpr AppExpr e1 e2) ⥛β e.
  inversion 1.
  move/(CannonicalForms type1) => [f [x [body [? ?]]]] v2.
  have: exists b, [e2 / x] body = b by CAS.
  move => [x0 ?].
  have: exists b, [(AbsExpr f x τ1 τ body) / f] x0 = b by CAS.
  done.
Qed.

Lemma ProgressBin : forall f {e1 e2 Γ τ} (typ: Γ ⊢ (BinExpr f e1 e2) ∷ τ) (v1 : 𝕍 e1) (v2 : 𝕍 e2), NotStuckβ (BinExpr f e1 e2).
  case => e1 e2 Γ τ typ v1 v2.
  - by inversion typ; Cannonicalize.
  - right; exact/ProgressApp.
Qed.

Lemma Progressβ : forall {e τ} (ety: NullEnv ⊢ e ∷ τ), NotStuckEβ e.
  induction e => τ //=.
  - inversion 1; inversion H1.
  - move=>ty; move/TypedBinopExprInversion: (ty) => [τ1 [τ2 [/IHe1-[v1|p1] /IHe2 ns2]]].
    + case: ns2 => [v2|p2].
      * by move: (ProgressBin ty v1 v2) => [//= | [e s]]; right; exists Hole.
      * by move: p2 => [E [e0 [e3 [-> s]]]]; right; exists (EvalContextBinR f v1 E).
    + by move: p1 => [E [e0 [e3 [-> s]]]]; right; exists (EvalContextBinL f E e2).
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

Hint Resolve βPreservation.

Hint Resolve InterpretTypedEvalContext.

Lemma Preservation {e e'} (estep : e ⥛ e') τ (etyp : NullEnv ⊢ e ∷ τ) : NullEnv ⊢ e' ∷ τ.
  by inversion estep; subst; move: (DecompositionOfTypes E e1 etyp).
Qed.

Hint Resolve Preservation.

Lemma Safety {e τ} (etyp : NullEnv ⊢ e ∷ τ) {e'} (estep : e ⥛* e') : (NotStuck e').
  by induction estep.
Qed.


