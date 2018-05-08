From Coq Require Import ssreflect ssrfun ssrbool.
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

Inductive SubContext : ℾ -> ℾ -> Prop :=
| SubIntro {Γ1 Γ2} : (forall {s τ}, s ∷ τ ∈ Γ1 -> s ∷ τ ∈ Γ2) -> SubContext Γ1 Γ2
| SubCons s τ {Γ1 Γ2} : SubContext Γ1 Γ2 -> SubContext (ConsEnv s τ Γ1) (ConsEnv s τ Γ2)
| SubShadow {Γ1 Γ2} Γ' : SubContext Γ1 Γ2 -> SubContext (ShadowEnv Γ1 Γ') (ShadowEnv Γ2 Γ').

Lemma InterpretSubContext {Γ1 Γ2} : SubContext Γ1 Γ2 -> forall {s τ}, s ∷ τ ∈ Γ1 -> s ∷ τ ∈ Γ2.
  induction 1 => s0 τ0; first done.
  all:have: forall τ, ContextLookup s0 Γ1 = Some τ -> ContextLookup s0 Γ2 = Some τ
        by move => ? /InContextP ?; apply/InContextP.
  all:by move=> IH /InContextP in1; apply/InContextP; move: in1 => /=; program_equiv.
Qed.

Lemma SubContextRefl Γ : SubContext Γ Γ. done. Qed.

Lemma SubContextTrans {Γ1 Γ2 Γ3} : SubContext Γ1 Γ2 -> SubContext Γ2 Γ3 -> SubContext Γ1 Γ3.
  by move => /InterpretSubContext ? /InterpretSubContext.
Qed.

Lemma SubEquiv {Γ1 Γ2} : EquivContext Γ1 Γ2 <-> (SubContext Γ1 Γ2 /\ SubContext Γ2 Γ1).
  by move: (@InterpretSubContext) (@InterpretEquivContext Γ1 Γ2).
Qed.

Notation "a ⊆ b" := (SubContext a b) (at level 1, b at next level).

Lemma SubContextConsRight {Γ1 Γ2} : Γ1 ⊆ Γ2 -> forall x τ, x ∉ Γ1 -> Γ1 ⊆ (ConsEnv x τ Γ2).
  move=> /InterpretSubContext equiv s τ /InContextPn nin.
  apply SubIntro => s0 τ0.
  by case: (string_dec s s0) => [<- /InContextP | neq].
Qed.

Lemma Weakening {Γ e τ} (typchecks1 : Γ ⊢ e ∷ τ) : forall {Γ'}, Γ ⊆ Γ' -> Γ' ⊢ e ∷ τ.
  by induction typchecks1 => // Γ'' /InterpretSubContext.
Qed.

Ltac weakening := apply/Weakening/(SubContextConsRight (SubContextRefl _)).

Lemma OtherWeakening {s e} (sNotIn : s ∉f e) : forall {Γ τ} (typechecks1 : Γ ⊢ e ∷ τ) {τ'}, (ConsEnv s τ' Γ) ⊢ e ∷ τ.
  induction sNotIn; intros Γ τ'' typechecks1 τ'; inv typechecks1; econstructor => //=.
  - specialize (IHsNotIn (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) τret type1 τ').
    apply/(EquivContextAlsoTypechecks IHsNotIn)/EquivContextP => s0 /=.
    by program_equiv.
  - apply/(EquivContextAlsoTypechecks type1)/EquivContextP => s0 /=.
    by program_equiv.
  - apply/(EquivContextAlsoTypechecks type1)/EquivContextP => s0 /=.
    by program_equiv.
Qed.

Reserved Notation "a ≡ b % c" (at level 1, b at next level).

Inductive ContextCongruenceModuloS : ℾ -> ℾ -> string -> Prop :=
| CongModIntro Γ1 Γ2 s :
    (forall s', (s=s') \/ (forall τ, s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2)) ->
    (Γ1 ≡ Γ2 % s)
| CongModCons {Γ1 Γ2 s s' τ} : Γ1 ≡ Γ2 % s -> (ConsEnv s' τ Γ1) ≡ (ConsEnv s' τ Γ2) % s
| CongModShad {Γ1 Γ2 Γ' s} : Γ1 ≡ Γ2 % s -> (ShadowEnv Γ1 Γ') ≡ (ShadowEnv Γ2 Γ') % s
where "a ≡ b % c" := (ContextCongruenceModuloS a b c).

Lemma InEquivToNotInEquiv {s Γ1 Γ2} : (forall τ, s ∷ τ ∈ Γ1 <-> s ∷ τ ∈ Γ2) -> (s ∉ Γ1 <-> s ∉ Γ2).
  move=> eq1.
  split => nin1.
  case (InContextOptions Γ2 s) => //=.
  move=> [? /eq1/InContextInverse] //=.
  case (InContextOptions Γ1 s) => //=.
  move=> [? /eq1/InContextInverse] //=.
Qed.

Lemma InterpretCongMod' {Γ1 Γ2 s}
  : Γ1 ≡ Γ2 % s -> forall s', (s=s') \/ (forall τ, s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2).
  intros H s'.
  induction H; first done.
  - decompose [or] IHContextCongruenceModuloS; first done.
    right; split; inversion 1; done.
  - decompose [or] IHContextCongruenceModuloS; first done.
    right; split; inversion 1; done.
Qed.

Lemma CongModP {Γ1 Γ2 s} :
  Γ1 ≡ Γ2 % s <-> (forall s0, (string_dec s s0)||(OptionLType_dec (ContextLookup s0 Γ1) (ContextLookup s0 Γ2))).
  split.
  - move/InterpretCongMod' => cong s0.
    apply/orP.
    case/(_ s0): cong.
    + left; exact/sumboolP.
    + right.
      apply/sumboolP.
      set o := (ContextLookup _ Γ2).
      case E : o.
      * apply/InContextP/b; move/InContextP: E; done.
      * move/InEquivToNotInEquiv in b.
        apply/InContextPn/b; move/InContextPn: E; done.
  - move=> equiv.
    apply CongModIntro.
    move=> s0; case/(_ s0)/orP : equiv.
    + move/sumboolP; done.
    + move/sumboolP => equiv.
      right => τ; split => /InContextP eq; exact/InContextP.
Qed.

Lemma InterpretCongMod {Γ1 Γ2 s}
  : Γ1 ≡ Γ2 % s -> forall {s'}, s<>s' -> (forall τ, s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2).
  intros H s' τ H0.
  edestruct (InterpretCongMod' H s'); done.
Qed.

Lemma CongModRefl Γ s : Γ ≡ Γ % s.
  done.
Qed.

Lemma CongModSymm {Γ1 Γ2 s} : Γ1 ≡ Γ2 % s -> Γ2 ≡ Γ1 % s.
  by move=> /InterpretCongMod' cong; apply/CongModIntro => s0; move/(_ s0): cong => [|].
Qed.

Lemma CongModToEquiv {Γ1 Γ2 s} (cong: Γ1 ≡ Γ2 % s) τ : (EquivContext (ConsEnv s τ Γ1) (ConsEnv s τ Γ2)).
  apply/EquivContextP => s0 /=; case (string_dec s0 s) => //= ne.
  case/CongModP/(_ s0)/orP: cong => /sumboolP //=.
Qed.

Lemma CongModConsLeft {x τ Γ1 Γ2} : Γ1 ≡ Γ2 % x -> (ConsEnv x τ Γ1) ≡ Γ2 % x.
  move => /CongModP cong; apply/CongModP => s0; apply/orP.
  case/(_ s0)/orP: cong => //= /sumboolP eq.
  case (string_dec s0 x);[left | right]; exact/sumboolP.
Qed.

Lemma Substitution {e1 Γ1 τ1} (typechks1 : Γ1 ⊢ e1 ∷ τ1) : forall e2 e3 Γ2 τ2 s,
  (s ∷ τ2 ∈ Γ1) ->
  Γ2 ⊢ e2 ∷ τ2 ->
  Γ1 ≡ Γ2 % s ->
  [e2 / s] e1 = e3 ->
  Γ2 ⊢ e3 ∷ τ1.
  elim: typechks1; intros; match goal with | H : [ _ / _ ] _ = _ |- _ => inversion H end; subst.
  - done.
  - move/InContextP in H; move/InContextP in H0; done.
  - move/(InterpretCongMod H2 neq) in H; done.
  - done.
  - done.
  - have: s ∷ τ2 ∈ (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) by done.
    have: (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ2)) ⊢ e2 ∷ τ2 by exact/OtherWeakening/OtherWeakening.
    have: (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) ≡ (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ2)) % s
      by exact/CongModCons/CongModCons.
    done.
  - have: f ∷ (τarg → τret) ∈ (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) by done.
    have: (EquivContext (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ2)))
      by exact/EquivCons/CongModToEquiv.
    by move/EquivContextAlsoTypechecks.
  - have: x ∷ τarg ∈ (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) by done.
    have: (EquivContext (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ2)))
      by exact/CongModToEquiv/CongModCons.
    by move/EquivContextAlsoTypechecks.
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
  destruct 1; simpl.
  - destruct (ContextFinite Γ) => //=.
  - by have: (ConsEnv x τ Γ) ⊢ e ∷ ℕ by weakening.
  - done.
  - by have: (ConsEnv x τ Γ) ⊢ e ∷ τarg by weakening.
  - by have: (ConsEnv x τ Γ) ⊢ (AbsExpr fn arg τarg τret body) ∷ (τarg → τret) by weakening.
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
Definition NotStuck e := 𝕍 e \/ (CanStep e).

Lemma Progressβ : forall {e τ} (ety: NullEnv ⊢ e ∷ τ), (𝕍 e) \/ (exists E e0 e1, e = E[e0] /\ e0 ⥛β e1).
  elim => //=.
  - move=> x τ; inversion 1; inversion H1.
  - move => e1 H1 e2 H2 τ; inversion 1; right.
    move/(_ NatType type1): H1 => [/(CannonicalForms type1) v1| [E1 [e11 [e12 [-> step1]]]]].
    all:move/(_ NatType type2): H2 => [/(CannonicalForms type2) v2| [E2 [e21 [e22 [-> step2]]]]].
    + move: v1 => [n1 ->]; move: v2 => [n2 ->]; exists Hole; exists (AddExpr n1 n2); exists (NatExpr (n1 + n2)); done.
    + move: v1 => [n1 ->]; exists (EvalContextRAdd n1 E2); exists e21; exists e22; done.
    + move: v2 => [n2 ->]; exists (EvalContextLAdd E1 n2); exists e11; exists e12; done.
    + exists (EvalContextLAdd E1 (E2 [e21])); exists e11; exists e12; done.
  - move => e1 H1 e2 H2 τ; inversion 1; right.
    move/(_ (AbsType τ1 τ) type1): H1 => [/(CannonicalForms type1) v1| [E1 [e11 [e12 [-> step1]]]]].
    all:move/(_ τ1 type2): H2 => [v2| [E2 [e21 [e22 [-> step2]]]]].
    + move: v1 => [f [x [body [nefx ->]]]].
      exists Hole.
      exists (AppExpr (AbsExpr f x τ1 τ body) e2); simpl.
      move:(@CASAlways e2 x body (AlwaysSafeToSubInto _ _)) => [body' eq].
      move:(@CASAlways (AbsExpr f x τ1 τ body) f body' (AlwaysSafeToSubInto _ _)) => [body'' eq'].
      done.
    + move: v1 => [f [x [body [nefx ->]]]]; exists (EvalContextRApp f x τ1 τ body E2); exists e21; exists e22; done.
    + exists (EvalContextLApp E1 e2); exists e11; exists e12; done.
    + exists (EvalContextLApp E1 (E2 [e21])); exists e11; exists e12; done.
Qed.

Lemma Progress {e} : forall {τ} (etyp: NullEnv ⊢ e ∷ τ), (NotStuck e).
  by move=> τ /Progressβ; move=> [v | [E [e0 [e1 [-> bstep]]]]].
Qed.

Lemma βPreservation {e e'} (estep : e ⥛β e') : forall τ (etyp : NullEnv ⊢ e ∷ τ),  NullEnv ⊢ e' ∷ τ.
  induction estep; intros τ0 etyp; inversion etyp; first done.
  subst.
  inversion type1.
  subst.
  apply/Substitution.
  - apply/Substitution.
    + exact type0.
    + done.
    + have: (NullEnv ⊆ (ConsEnv f (τ1 → τ0) NullEnv)) by apply/(SubContextConsRight (SubContextRefl _))/NotInNullEnv.
      move=> sub; exact/Weakening.
    + apply/CongModConsLeft/CongModRefl.
    + done.
  - apply/InConsEnv.
  - exact type1.
  - apply/CongModConsLeft/CongModRefl.
  - done.
Qed.

Lemma Preservation {e e'} (estep : e ⥛ e') : forall τ (etyp : NullEnv ⊢ e ∷ τ),  NullEnv ⊢ e' ∷ τ.
  intros τ etyp.
  inversion estep.
  subst.
  move: (DecompositionOfTypes E e1 etyp) => [τn [typee1 ?]].
  move: (βPreservation betaStep typee1) => etyp1.
  exact/InterpretTypedEvalContext.
Qed.

Lemma Safety {e τ} (etyp : NullEnv ⊢ e ∷ τ) {e'} (estep : e ⥛* e') : (NotStuck e').
  induction estep.
  - exact/Progress.
  - exact/IHestep/Preservation.
Qed.


