From Coq Require Import ssreflect ssrfun ssrbool.
Require Import FunInd.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import MyBase.
Require Import lang.
Require Import hoas.
Open Scope MyListScope.

Inductive LangContext : Set :=
| NullEnv : LangContext
| ConsEnv (var : string) (typ : 𝕋) (Γ : LangContext) : LangContext
| ShadowEnv (Γ1 : LangContext) (Γ2 : LangContext) : LangContext.
Notation ℾ := LangContext.

Bind Scope LangContext_scope with LangContext.

Inductive NotInContext : ℾ -> string -> Prop :=
| NotInNullEnv {s} : s ∉ NullEnv
| NotInConsEnv {s1 s2 τ Γ}
                (diffVars : s1 <> s2)
                (notInSub : s1 ∉ Γ)
  : s1 ∉(ConsEnv s2 τ Γ)
| NotInShadowEnv {s Γ1 Γ2}
                  (notInLeft : s ∉ Γ1)
                  (notInRight : s ∉ Γ2)
  : s ∉ (ShadowEnv Γ1 Γ2)
where "a ∉ b" := (NotInContext b a) : LangContext_scope.


Reserved Notation "a ∷ b ∈ c" (at level 1, no associativity, b at next level).
Inductive InContext : ℾ -> string -> 𝕋 -> Prop :=
| InConsEnv {s τ Γ} : s ∷ τ ∈ (ConsEnv s τ Γ)
| InSubConsEnv {s1 τ1 s2 τ2 Γ}
               (diffs : s1 <> s2)
               (inSub : s1 ∷ τ1 ∈ Γ)
  : s1 ∷ τ1 ∈ (ConsEnv s2 τ2 Γ)
| InShadowEnvRight {s τ Γ1 Γ2}
                   (inRight : s ∷ τ ∈ Γ2)
  : s ∷ τ ∈ (ShadowEnv Γ1 Γ2)
| InShadowEnvLeft {s τ Γ1 Γ2}
                  (notInRight : s ∉ Γ2)
                  (inLeft : s ∷ τ ∈ Γ1)
  : s ∷ τ ∈ (ShadowEnv Γ1 Γ2)
where "a ∷ b ∈ c" := (InContext c a b) : LangContext_scope.
Open Scope LangContext_scope.

Fixpoint ContextLookup s Γ :=
  match Γ with
  | NullEnv => None
  | ConsEnv s0 τ Γ0 =>
    if (string_dec s s0) then
      Some τ
    else ContextLookup s Γ0
  | ShadowEnv Γ0 Γ1 =>
    if (ContextLookup s Γ1) is Some τ then
      Some τ
    else ContextLookup s Γ0
  end.

Functional Scheme ContextLookup_ind
  := Induction for ContextLookup Sort Set.

Lemma InContextPn Γ s : s ∉ Γ <-> (ContextLookup s Γ = None).
  split.
  - elim => //=.
    + move => s1 s2. case (string_dec s1 s2); cbn; done.
    + move => s0 Γ1 Γ2 notInLeft H notInRight H0; rewrite H; rewrite H0; done.
  - functional induction (ContextLookup s Γ) => //=.
    move/IHo => IH; move/(sumboolP (string_dec s s0)): e0; done.
Qed.


Lemma InContextP Γ s τ : s ∷ τ ∈ Γ <-> ContextLookup s Γ = Some τ.
  split.
  - elim => //=.
    + move => s0; case (string_dec s0 s0); cbn; done.
    + move => s1 τ1 s2; case (string_dec s1 s2); cbn; done.
    + intros s0 τ0 Γ1 Γ2 inRight H; rewrite H; cbn; done.
    + move => s0 τ0 Γ1 Γ2 /InContextPn ->; done.
  - functional induction (ContextLookup s Γ) => //=.
    + move/(sumboolP (string_dec s s0)): e0 => ->; case => ->; done.
    + move/IHo => inSub; move/(sumboolP (string_dec s s0)): e0; done.
    + move/InContextPn : e0 => notInLeft; move/IHo0; done.
Qed.

Lemma InContextInverse {Γ s τ} : s∷τ ∈ Γ -> s ∉ Γ -> False.
  move => /InContextP a /InContextPn b; done.
Qed.

Lemma InContextOptions Γ s : (exists τ, s∷τ∈Γ) \/ (s∉Γ).
  case E : (ContextLookup s Γ).
  - move/InContextP: E => //=.
  - move/InContextPn: E => //=.
Qed.

Lemma InContextUnique {s τ1 τ2 Γ} : forall (τin1: s ∷ τ1 ∈ Γ) (τin2: s ∷ τ2 ∈ Γ), τ1=τ2.
  move => /InContextP a /InContextP b; done.
Qed.

Lemma InConsEnvInversion {s τ τ' Γ} : s ∷ τ ∈ (ConsEnv s τ' Γ) -> τ=τ'.
  move=> ?; exact: InContextUnique.
Qed.

Lemma InSubConsEnvInversion {s s' Γ} (neq : s<>s') {τ τ'}
  : s ∷ τ ∈ (ConsEnv s' τ' Γ) -> s ∷ τ ∈ Γ.
  inversion 1 => //.
Qed.

Inductive EquivContext : ℾ -> ℾ -> Prop :=
| EquivIntro {Γ1 Γ2} : (forall s τ, s ∷ τ ∈ Γ1 <-> s ∷ τ ∈ Γ2) -> EquivContext Γ1 Γ2
| EquivCons s τ {Γ1 Γ2} : EquivContext Γ1 Γ2 -> EquivContext (ConsEnv s τ Γ1) (ConsEnv s τ Γ2)
| EquivShadow {Γ1 Γ2} Γ' : EquivContext Γ1 Γ2 -> EquivContext (ShadowEnv Γ1 Γ') (ShadowEnv Γ2 Γ').

Lemma InterpretEquivContext' {Γ1 Γ2} : EquivContext Γ1 Γ2 -> forall {s τ}, s ∷ τ ∈ Γ1 -> s ∷ τ ∈ Γ2.
Proof with done.
  elim => //.
  - move=> s0 τ0 Γ0 Γ3 EquivSub IH s1 τ1; case: (string_dec s1 s0) => [-> | neq] inH.
    + rewrite (InContextUnique inH (@InConsEnv s0 τ0 Γ0))...
    + constructor => //; apply IH.
      pose inSub := InSubConsEnvInversion neq inH...
  - move=> Γ0 Γ3 Γ' EquivSub IH s τ; inversion 1 => //.
Qed.

Lemma EquivContextRefl Γ : EquivContext Γ Γ.
  enough (forall s τ, s ∷ τ ∈ Γ <-> s ∷ τ ∈ Γ); done.
Qed.

Lemma EquivContextSymm {Γ1 Γ2} : EquivContext Γ1 Γ2 -> EquivContext Γ2 Γ1.
  elim; done.
Qed.

Lemma InterpretEquivContext {Γ1 Γ2} : EquivContext Γ1 Γ2 -> (forall {s τ}, s ∷ τ ∈ Γ1 <-> s ∷ τ ∈ Γ2).
  split.
  - exact: InterpretEquivContext'.
  - apply: InterpretEquivContext'; exact: EquivContextSymm.
Qed.

Lemma EquivContextP Γ1 Γ2 : EquivContext Γ1 Γ2 <-> forall s, ContextLookup s Γ1 = ContextLookup s Γ2.
  split.
  - move/InterpretEquivContext => equ s; move/(_ s): equ.
    case: (InContextOptions Γ1 s) => [[τ i] | /InContextPn ne].
    + move/(_ τ) => [/(_ i)/InContextP a b]; move/InContextP: i; done.
    + case: (InContextOptions Γ2 s) => [[τ0 i0] | /InContextPn ne0].
      * move => eq; move/eq/InContextP : i0 => i0; done.
      * done.
  - move=> eq; apply EquivIntro => s τ; split; rewrite 2! InContextP; done.
Qed.

Lemma EquivContextTrans {Γ1 Γ2 Γ3}
  : EquivContext Γ1 Γ2 -> EquivContext Γ2 Γ3 -> EquivContext Γ1 Γ3.
  rewrite 3! EquivContextP; done.
Qed.

Lemma EquivContextDoubleElim Γ s τ τ'
  : (EquivContext (ConsEnv s τ (ConsEnv s τ' Γ)) (ConsEnv s τ Γ)).
  rewrite EquivContextP /= => s0; destruct (string_dec s0 s); cbn; done.
Qed.

Lemma EquivContextReorder {Γ1 Γ2 s s'} :
  (EquivContext Γ1 Γ2) -> s<>s' -> forall τ τ',
      (EquivContext (ConsEnv s τ (ConsEnv s' τ' Γ1)) (ConsEnv s' τ' (ConsEnv s τ Γ2))).
  rewrite EquivContextP => eq neq τ τ0.
  rewrite EquivContextP => s0 /=.
  destruct (string_dec s0 s); destruct (string_dec s0 s') => /=; done.
Qed.

Reserved Notation "a '⊢' b '∷' c" (at level 1, no associativity, b at next level).

Inductive Typechecks : ℾ -> 𝔼 -> 𝕋 -> Prop :=
| NSE {Γ n} : Γ ⊢ (NatExpr n) ∷ NatType
| VSE {Γ s τ} : s∷τ ∈ Γ -> Γ ⊢ s ∷ τ
| ASE {Γ e1 e2}
      (type1 : Γ ⊢ e1 ∷ NatType)
      (type2 : Γ ⊢ e2 ∷ NatType)
  : Γ ⊢ (e1 + e2) ∷ NatType
| PSE {Γ e1 e2 τ1 τ2}
      (type1 : Γ ⊢ e1 ∷ (τ1 → τ2))
      (type2 : Γ ⊢ e2 ∷ τ1)
  : Γ ⊢ (AppExpr e1 e2) ∷ τ2
| BSE {Γ f x τ body τ'}
      (nefx : f <> x)
      (type1 : (ConsEnv x τ (ConsEnv f (τ → τ') Γ)) ⊢ body ∷ τ')
  : Γ ⊢ (AbsExpr f x τ body) ∷ (τ → τ')
where "a '⊢' b '∷' c" := (Typechecks a b c).

Lemma EquivContextAlsoTypechecks {Γ1 e τ} : Γ1 ⊢ e ∷ τ -> forall {Γ2}, EquivContext Γ1 Γ2 -> Γ2 ⊢ e ∷ τ.
  elim; move=> *; econstructor => //.
  match goal with | [ H: (EquivContext _ _) |- _] => apply/(InterpretEquivContext H) end; done.
Qed.

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

Theorem concatenationNotAny {l s} : s ∈ l -> s <> ((concatenation l) ++ "x")%string.
Proof with done.
  move=> /concatenationLength H.
  pose (sumAppendLength (concatenation l) "x").
  simpl in e.
  pose (Lt.le_lt_n_Sm _ _ H).
  rewrite -> PeanoNat.Nat.add_1_r in e.
  rewrite <- e in l0.
  apply diffLenDiffStr.
  exact (PeanoNat.Nat.lt_neq _ _ l0).
Qed.

Theorem concatNotIn l : ~ ((concatenation l) ++ "x")%string ∈ l.
  move => /concatenationNotAny H; done.
Qed.

Theorem ListFinite (l : list string) : exists x, ~ (x ∈ l).
  exists ((concatenation l) ++ "x")%string; apply concatNotIn.
Qed.

Fixpoint ContextVars (Γ : ℾ) :=
  match Γ with
  | NullEnv => nil
  | ConsEnv x τ Γ' => x :: (ContextVars Γ')
  | ShadowEnv Γ1 Γ2 => ((ContextVars Γ1) ++ (ContextVars Γ2))
  end.

Functional Scheme ContextVars_ind
  := Induction for ContextVars Sort Set.

Theorem ContextDomainIsDomain {Γ x} : (~ x ∈ (ContextVars Γ)) <-> x ∉ Γ.
  split.
  - functional induction (ContextVars Γ) => //=.
    + rewrite in_app_iff or_not_iff => [[nin1 nin2]] //=.
  - induction 1 => //=.
    + rewrite in_app_iff or_not_iff //=.
Qed.

Theorem ContextFinite Γ : exists x, x ∉ Γ.
  destruct (ListFinite (ContextVars Γ)).
  exists x; move: H; rewrite ContextDomainIsDomain //=.
Qed.

Reserved Notation "Γ ⊢ e [ τ ] ∷ τ'" (at level 1, e at next level, τ at next level, τ' at next level).

Inductive TypedEvalContext : ℾ -> EvaluationContext -> 𝕋 -> 𝕋 -> Prop :=
| TypedHole Γ τ : Γ ⊢ Hole [τ] ∷ τ
| TypedELAdd {Γ E e1 e2 x τ}
  : Γ ⊢ e2 ∷ ℕ -> x ∉ Γ -> EvaluationContextFillsTo E x e1 ->
    (ConsEnv x τ Γ) ⊢ e1 ∷ ℕ -> Γ ⊢ E [τ] ∷ ℕ ->
    Γ ⊢ (EvalContextLAdd E e2) [τ] ∷ ℕ
| TypedERadd {Γ E n e x τ}
  : x ∉ Γ -> EvaluationContextFillsTo E x e ->
    (ConsEnv x τ Γ) ⊢ e ∷ ℕ -> Γ ⊢ E [τ] ∷ ℕ ->
    Γ ⊢ (EvalContextRAdd n E) [τ] ∷ ℕ
| TypedELApp {Γ E e1 e2 τarg τret x τ}
  : Γ ⊢ e2 ∷ τarg -> x ∉ Γ -> EvaluationContextFillsTo E x e1 ->
    (ConsEnv x τ Γ) ⊢ e1 ∷ (τarg → τret) -> Γ ⊢ E [τ] ∷ (τarg → τret) ->
    Γ ⊢ (EvalContextLApp E e2) [τ] ∷ τret
| TypedERapp {fn arg τarg body τret Γ E e x τ}
  : Γ ⊢ (AbsExpr fn arg τarg body) ∷ (τarg → τret) -> x ∉ Γ -> EvaluationContextFillsTo E x e ->
    (ConsEnv x τ Γ) ⊢ e ∷ τarg -> Γ ⊢ E [τ] ∷ τarg ->
    Γ ⊢ (EvalContextRApp fn arg τarg body E) [τ] ∷ τret
where "Γ ⊢ e [ τ ] ∷ τ1" := (TypedEvalContext Γ e τ τ1).

Lemma InterpretTypedEvalContext {Γ E τ τ1} (Etyp : Γ ⊢ E [τ] ∷ τ1) 
  : forall e e1, Γ ⊢ e ∷ τ -> EvaluationContextFillsTo E e e1 -> Γ ⊢ e1 ∷ τ1.
  induction Etyp; intros e0 e3 etyp ecf; inversion ecf.
  - done.
  - subst.
    econstructor.
    eapply IHEtyp; done.
    assumption.
  - subst.
    econstructor.
    done.
    eapply IHEtyp; done. 
  - subst.
    econstructor.
    eapply IHEtyp; done.
    done.
  - subst.
    econstructor.
    done.
    eapply IHEtyp; done.
Qed.
