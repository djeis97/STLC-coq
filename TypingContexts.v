From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Setoids.Setoid.
Require Import FunInd.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import MyBase.
Require Import lang.
Open Scope MyListScope.

Inductive LangContext : Set :=
| NullEnv : LangContext
| ConsEnv (var : string) (typ : 𝕋) (Γ : LangContext) : LangContext.

Notation ℾ := LangContext.

Bind Scope LangContext_scope with LangContext.

Inductive NotInContext : ℾ -> string -> Prop :=
| NotInNullEnv {s} : s ∉ NullEnv
| NotInConsEnv {s1 s2 τ Γ}
                (diffVars : s1 <> s2)
                (notInSub : s1 ∉ Γ)
  : s1 ∉(ConsEnv s2 τ Γ)
where "a ∉ b" := (NotInContext b a) : LangContext_scope.


Reserved Notation "a ∷ b ∈ c" (at level 1, no associativity, b at next level).
Inductive InContext : ℾ -> string -> 𝕋 -> Prop :=
| InConsEnv {s τ Γ} : s ∷ τ ∈ (ConsEnv s τ Γ)
| InSubConsEnv {s1 τ1 s2 τ2 Γ}
               (diffs : s1 <> s2)
               (inSub : s1 ∷ τ1 ∈ Γ)
  : s1 ∷ τ1 ∈ (ConsEnv s2 τ2 Γ)
where "a ∷ b ∈ c" := (InContext c a b) : LangContext_scope.
Open Scope LangContext_scope.

Hint Constructors InContext NotInContext.

Fixpoint ContextLookup s Γ {struct Γ} :=
  match Γ with
  | NullEnv => None
  | ConsEnv s0 τ Γ0 => if (string_dec s s0) then (some τ) else (ContextLookup s Γ0)
  end.

Functional Scheme ContextLookup_ind
  := Induction for ContextLookup Sort Set.

Lemma InContextPn Γ s : s ∉ Γ <-> (ContextLookup s Γ = None).
  split.
  - by elim => /= *; program_equiv.
  - by functional induction (ContextLookup s Γ) => //= /IHo IH; move/(sumboolP _): e0.
Qed.


Lemma InContextP Γ s τ : s ∷ τ ∈ Γ <-> ContextLookup s Γ = Some τ.
  split.
  - elim => //=; by [move=> *; program_equiv | move=> s0 τ0 Γ1 Γ2 /InContextPn ->].
  - functional induction (ContextLookup s Γ) => //=.
    + by move/(sumboolP _): e0 => ->; case.
    + by move/(sumboolP _): e0 => ? /IHo.
Qed.

Lemma InContextInverse {Γ s τ} : s∷τ ∈ Γ -> s ∉ Γ -> False.
  by rewrite InContextP InContextPn.
Qed.

Lemma InContextOptions Γ s : (exists τ, s∷τ∈Γ) \/ (s∉Γ).
  case E : (ContextLookup s Γ); by [move/InContextP: E | move/InContextPn: E].
Qed.

Lemma InContextUnique {s τ1 τ2 Γ} : forall (τin1: s ∷ τ1 ∈ Γ) (τin2: s ∷ τ2 ∈ Γ), τ1=τ2.
  by rewrite ! InContextP.
Qed.

Lemma InConsEnvInversion {s τ τ' Γ} (inCons: s ∷ τ ∈ (ConsEnv s τ' Γ)) : τ=τ'.
  exact: InContextUnique.
Qed.

Hint Resolve @InConsEnvInversion.

Lemma InSubConsEnvInversion {s s' Γ} (neq : s<>s') {τ τ'} : s ∷ τ ∈ (ConsEnv s' τ' Γ) -> s ∷ τ ∈ Γ.
  by inversion 1.
Qed.

Hint Resolve @InSubConsEnvInversion.

Lemma InConsEnvOptions {s0 τ0 s1 τ1 Γ} (ing: s0 ∷ τ0 ∈ (ConsEnv s1 τ1 Γ)) : (s0 = s1 /\ τ0 = τ1) \/ (s0 <> s1 /\ s0 ∷ τ0 ∈ Γ).
  by case : (string_dec s0 s1) ing.
Qed.

Fixpoint ShadowEnv (Γ1 Γ2 : LangContext) :=
  match Γ2 with
  | NullEnv => Γ1
  | ConsEnv x τ Γ2' => (ConsEnv x τ (ShadowEnv Γ1 Γ2'))
  end.

Functional Scheme ShadowEnv_ind := Induction for ShadowEnv Sort Set.

Lemma ShadowEnvCorrect {Γ1 Γ2} : forall s τ, s ∷ τ ∈ (ShadowEnv Γ1 Γ2) -> s ∷ τ ∈ Γ2 \/ s ∉ Γ2 /\ s ∷ τ ∈ Γ1.
  functional induction (ShadowEnv Γ1 Γ2); first done.
  move=> s τ0; move/(_ s τ0) in IHl.
  by case (string_dec s x) => [-> /InConsEnvInversion| ne /(InSubConsEnvInversion ne)].
Qed.

Inductive EquivContext : ℾ -> ℾ -> Prop :=
| EquivIntro {Γ1 Γ2} (eq: forall s τ, s ∷ τ ∈ Γ1 <-> s ∷ τ ∈ Γ2) : EquivContext Γ1 Γ2
| EquivCons s τ {Γ1 Γ2} (eq: EquivContext Γ1 Γ2) : EquivContext (ConsEnv s τ Γ1) (ConsEnv s τ Γ2).

Fixpoint InterpretEquivContext' {Γ1 Γ2} (eq: EquivContext Γ1 Γ2) {s τ} (in1: s ∷ τ ∈ Γ1) : s ∷ τ ∈ Γ2.
  destruct eq;[done|by decompose [and or] (InConsEnvOptions in1)].
Qed.

Lemma EquivContextRefl Γ : EquivContext Γ Γ. done. Qed.

Fixpoint EquivContextSymm {Γ1 Γ2} (eq: EquivContext Γ1 Γ2) : EquivContext Γ2 Γ1.
  refine (match eq with
          | EquivIntro eq0 => EquivIntro (fun s τ => (symmetry (eq0 s τ)))
          | EquivCons s τ eq0 => EquivCons s τ (EquivContextSymm _ _ eq0)
          end).
Qed.

Lemma InterpretEquivContext {Γ1 Γ2} : EquivContext Γ1 Γ2 -> (forall {s τ}, s ∷ τ ∈ Γ1 <-> s ∷ τ ∈ Γ2).
  by split; apply/InterpretEquivContext';[|apply/EquivContextSymm].
Qed.

Lemma EquivContextTrans {Γ1 Γ2 Γ3} : EquivContext Γ1 Γ2 -> EquivContext Γ2 Γ3 -> EquivContext Γ1 Γ3.
  move=> /InterpretEquivContext ? /InterpretEquivContext ?; exact/EquivIntro.
Qed.

Add Parametric Relation : LangContext EquivContext
    reflexivity proved by EquivContextRefl
    symmetry proved by @EquivContextSymm
    transitivity proved by @EquivContextTrans
      as EquivContext_rel.

Add Parametric Morphism s : (ContextLookup s) with signature (EquivContext) ==> (eq) as ContextLookup_mor.
  move=> Γ1 Γ2 /InterpretEquivContext/(_ s).
  case: (InContextOptions Γ1 s) => [[τ i] | /InContextPn ne].
  + by move/(_ τ) => [/(_ i)/InContextP a b]; move/InContextP: i.
  + by case: (InContextOptions Γ2 s) => [[τ0 i0] eq | /InContextPn ne0 //=]; move/eq/InContextP: i0.
Qed.

Lemma EquivContextP Γ1 Γ2 : EquivContext Γ1 Γ2 <-> forall s, ContextLookup s Γ1 = ContextLookup s Γ2.
  split.
  - by move=> eq ?; rewrite eq.
  - by move=> eq; apply EquivIntro => *; rewrite ! InContextP.
Qed.


Lemma EquivContextDoubleElim Γ s τ τ'
  : (EquivContext (ConsEnv s τ (ConsEnv s τ' Γ)) (ConsEnv s τ Γ)).
  by rewrite EquivContextP /= => ?; program_equiv.
Qed.

Lemma EquivContextReorder {Γ1 Γ2 s s'} :
  (EquivContext Γ1 Γ2) -> s<>s' -> forall τ τ', (EquivContext (ConsEnv s τ (ConsEnv s' τ' Γ1)) (ConsEnv s' τ' (ConsEnv s τ Γ2))).
  by move=> /EquivContextP *; apply/EquivContextP =>* /=; program_equiv.
Qed.

Fixpoint ContextVars (Γ : ℾ) :=
  match Γ with
  | NullEnv => nil
  | ConsEnv x τ Γ' => x :: (ContextVars Γ')
  end.

Functional Scheme ContextVars_ind
  := Induction for ContextVars Sort Set.

Theorem ContextDomainIsDomain {Γ x} : (~ x ∈ (ContextVars Γ)) <-> x ∉ Γ.
  by split;[functional induction (ContextVars Γ)|induction 1]; rewrite //= in_app_iff or_not_iff.
Qed.

Theorem ContextFinite Γ : exists x, x ∉ Γ.
  by move:(ListFinite (ContextVars Γ))=>[x /ContextDomainIsDomain].
Qed.

Inductive SubContext : ℾ -> ℾ -> Prop :=
| SubIntro {Γ1 Γ2} : (forall {s τ}, s ∷ τ ∈ Γ1 -> s ∷ τ ∈ Γ2) -> SubContext Γ1 Γ2
| SubCons s τ {Γ1 Γ2} : SubContext Γ1 Γ2 -> SubContext (ConsEnv s τ Γ1) (ConsEnv s τ Γ2).

Fixpoint InterpretSubContext {Γ1 Γ2} (eq : SubContext Γ1 Γ2) {s τ} (in1: s ∷ τ ∈ Γ1) {struct eq} : s ∷ τ ∈ Γ2.
  destruct eq;[done|by decompose [and or] (InConsEnvOptions in1)].
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

Add Parametric Relation : LangContext SubContext
    reflexivity proved by SubContextRefl
    transitivity proved by @SubContextTrans
      as SubContext_rel.

Reserved Notation "a ≡ b % c" (at level 1, b at next level).

Inductive ContextCongruenceModuloS : ℾ -> ℾ -> string -> Prop :=
| CongModIntro {Γ1 Γ2 s} (eq: forall s', (s=s') \/ (forall τ, s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2)) : (Γ1 ≡ Γ2 % s)
| CongModCons {Γ1 Γ2 s} s' τ (eq: Γ1 ≡ Γ2 % s) : (ConsEnv s' τ Γ1) ≡ (ConsEnv s' τ Γ2) % s
where "a ≡ b % c" := (ContextCongruenceModuloS a b c).

Lemma InEquivToNotInEquiv {s Γ1 Γ2} (eq1: forall τ, s ∷ τ ∈ Γ1 <-> s ∷ τ ∈ Γ2) : (s ∉ Γ1 <-> s ∉ Γ2).
  by split => nin1; [case (InContextOptions Γ2 s)|case (InContextOptions Γ1 s)] => //=; move=> [? /eq1/InContextInverse].
Qed.

Fixpoint InterpretCongMod' {Γ1 Γ2 s} (cong: Γ1 ≡ Γ2 % s) s' {struct cong} : (s=s') \/ (forall τ, s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2).
  refine (match cong with
          | CongModIntro eq => (eq s')
          | @CongModCons Γ10 Γ20 s00 s0 τ0 eq =>
            match (InterpretCongMod' Γ10 Γ20 s00 eq s') with
            | or_introl rewr => (or_introl rewr)
            | or_intror rewr => (or_intror (fun τ0 => let: (conj rewr1 rewr2) := (rewr τ0) in _))
            end
          end).
  split; move/InConsEnvOptions => [[-> ->]| []]; eauto.
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

Lemma InterpretCongMod {Γ1 Γ2 s} (congMod: Γ1 ≡ Γ2 % s) {s'} (neq: s<>s') τ : s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2.
  by edestruct (InterpretCongMod' congMod s').
Qed.

Lemma CongModRefl Γ s : Γ ≡ Γ % s. done. Qed.

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

Hint Constructors EquivContext ContextCongruenceModuloS SubContext.
Hint Resolve (@SubContextConsRight).
Hint Resolve (@SubContextRefl).
Hint Resolve (@CongModToEquiv).
Hint Resolve (@CongModConsLeft).
Hint Resolve (@CongModRefl).