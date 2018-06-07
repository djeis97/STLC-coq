From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Setoids.Setoid.
Require Import FunInd.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import MyBase.
Require Import lang.
Require Import hoas.
Require Import TypingContexts.
Open Scope MyListScope.
Open Scope LangContext_scope.

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
  : Γ ⊢ (BinExpr AppExpr e1 e2) ∷ τ2
| BSE {Γ f x τarg τret body}
      (nefx : f <> x)
      (type1 : (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) ⊢ body ∷ τret)
  : Γ ⊢ (AbsExpr f x τarg τret body) ∷ (τarg → τret)
where "a '⊢' b '∷' c" := (Typechecks a b c).

Lemma EquivContextAlsoTypechecks {Γ1 e τ} : Γ1 ⊢ e ∷ τ -> forall {Γ2}, EquivContext Γ1 Γ2 -> Γ2 ⊢ e ∷ τ.
  elim; move=> *; econstructor => //.
  match goal with | [ H: (EquivContext _ _) |- _] => apply/(InterpretEquivContext H) end; done.
Qed.

Hint Resolve (@EquivContextAlsoTypechecks).

Add Parametric Morphism : Typechecks with signature
    EquivContext ==> eq ==> eq ==> Basics.impl as Typechecks_eq_mor.
  rewrite /Basics.impl.
  by move=> *; apply/EquivContextAlsoTypechecks.
Qed.

Add Parametric Morphism : Typechecks with signature
    SubContext ++> eq ==> eq ==> Basics.impl as Typechecks_sub_mor.
  move => Γ1 Γ2 sub e τ.
  rewrite /Basics.impl; move=> typechecks1; move: Γ2 sub.
  by induction typechecks1 => // Γ2 /InterpretSubContext.
Qed.

Fixpoint typchk Γ e :=
Function typchk Γ e :=
  match e with
  | NatExpr _ => Some NatType
  | VarExpr s => ContextLookup s Γ
  | BinExpr AddExpr l r =>
    if ((typchk Γ l), (typchk Γ r)) is (Some τl, Some τr) then
      if LType_dec τl NatType is left eq1 then
        if LType_dec τr NatType is left eq2 then
          Some NatType
        else None
      else None
    else None
  | BinExpr AppExpr f a => if ((typchk Γ f), (typchk Γ a)) is ((Some (AbsType τa0 τret), Some τa1)) then
                            if (LType_dec τa0 τa1) is left eql then
                              Some τret
                            else None
                          else None
  | AbsExpr f x τarg τret body =>
    if (string_dec f x) is right nefx then
      if (typchk (ConsEnv x τarg (ConsEnv f (AbsType τarg τret) Γ)) body) is Some τret0 then
        if (LType_dec τret τret0) is left eq2 then
          Some (AbsType τarg τret)
        else None
      else None
    else None
  end.

Lemma TypechecksP {Γ e τ} : Γ ⊢ e ∷ τ <-> (typchk Γ e = Some τ).
  split.
  - induction 1 => //=; by [apply/InContextP | program_equiv].
Qed.
  - move: τ; functional induction (typchk Γ e) => τ //=; by [case | move/InContextP].

Reserved Notation "Γ ⊢ E { τ } ∷ τ'" (at level 1, E at next level, τ at next level, τ' at next level).

Inductive TypedEvalContext : ℾ -> EvaluationContext -> 𝕋 -> 𝕋 -> Prop :=
| TypedHole Γ τ : Γ ⊢ Hole {τ} ∷ τ
| TypedELAdd {Γ E e τ} : Γ ⊢ e ∷ ℕ -> Γ ⊢ E {τ} ∷ ℕ -> Γ ⊢ (EvalContextBinL AddExpr E e) {τ} ∷ ℕ
| TypedERadd {Γ E n τ} : Γ ⊢ E {τ} ∷ ℕ -> Γ ⊢ (EvalContextBinR AddExpr (NatValue n) E) {τ} ∷ ℕ
| TypedELApp {Γ E e τarg τret τ} : Γ ⊢ e ∷ τarg -> Γ ⊢ E {τ} ∷ (τarg → τret) -> Γ ⊢ (EvalContextBinL AppExpr E e) {τ} ∷ τret
| TypedERapp {fn arg τarg body τret Γ E τ}
  : Γ ⊢ (AbsExpr fn arg τarg τret body) ∷ (τarg → τret) -> Γ ⊢ E {τ} ∷ τarg ->
    Γ ⊢ (EvalContextBinR AppExpr (AbsValue fn arg τarg τret body) E) {τ} ∷ τret
where "Γ ⊢ e { τ } ∷ τ1" := (TypedEvalContext Γ e τ τ1).

Lemma InterpretTypedEvalContext {Γ E τ τ1} (Etyp : Γ ⊢ E {τ} ∷ τ1) {e} : Γ ⊢ e ∷ τ -> Γ ⊢ E[e] ∷ τ1.
  induction Etyp; done.
Qed.
