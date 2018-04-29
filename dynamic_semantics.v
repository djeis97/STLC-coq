Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import MyBase.
Require Import lang.
Require Import hoas.
Require Import static_semantics.
Set Implicit Arguments.
Import ListNotations.
Definition expr_dec : forall e1 e2 : 𝔼, {e1 = e2} + {e1 <> e2}.
decide equality.
- apply string_dec.
- decide equality.
- decide equality.
- apply string_dec.
- apply string_dec.
Qed.

Reserved Notation "a ⥛ b" (at level 1, no associativity).
Reserved Notation "a ⥛β b" (at level 1, no associativity).

Inductive SmallStepsBeta : 𝔼 -> 𝔼 -> Prop :=
| ASSβ n1 n2 : ((NatExpr n1) + (NatExpr n2)) ⥛β (NatExpr (n1 + n2))
| PSSβ f x τ body {e} (v : 𝕍 e) {body' body''}
       (CASx : [ e / x ] body = body')
       (CASf : [ (AbsExpr f x τ body) / f ] body' = body'')
  : (AppExpr (AbsExpr f x τ body) e) ⥛β body''
where "a ⥛β b" := (SmallStepsBeta a b).

Inductive SmallSteps : 𝔼 -> 𝔼 -> Prop :=
| ECSS {E e1 e1' e2 e2'}
       (fillse1 : EvaluationContextFillsTo E e1 e1')
       (fillse2 : EvaluationContextFillsTo E e2 e2')
       (betaStep : e1 ⥛β e2)
  : e1' ⥛ e2'
where "a ⥛ b" := (SmallSteps a b).

Reserved Notation "a ⥛* b" (at level 1, no associativity).

Inductive BigSteps : 𝔼 -> 𝔼 -> Prop :=
| RBS {e} : e ⥛* e
| SBS {e e' e''} (ess : e ⥛ e') (e'bs : e' ⥛* e'') : e ⥛* e''
where "a ⥛* b" := (BigSteps a b).