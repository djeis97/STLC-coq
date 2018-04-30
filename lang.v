From Coq Require Import ssreflect ssrfun ssrbool.
Require Import String.
Require Import List.
Require Import ListSet.
Require Import MyBase.

Inductive LType : Set :=
| NatType : LType
| AbsType (arg ret : LType) : LType.

Inductive Expression : Set :=
| VarExpr (x : string) : Expression
| NatExpr (n : nat) : Expression
| AddExpr (e1 e2 : Expression) : Expression
| AbsExpr (f x : string) (τ : LType) (body : Expression) : Expression
| AppExpr (e1 e2 : Expression) : Expression.

Coercion VarExpr : string >-> Expression.
Coercion NatExpr : nat >-> Expression.
Bind Scope Expression_scope with Expression.
Arguments AddExpr (e1 e2)%Expression_scope.
Notation "a + b" := (AddExpr a b) : Expression_scope.

Inductive LValue : Expression -> Prop :=
| NatValue n: LValue (NatExpr n)
| AbsValue (f x : string) (τ : LType) (body : Expression) : LValue (AbsExpr f x τ body).

Inductive EvaluationContext : Set :=
| Hole : EvaluationContext
| EvalContextLAdd (E : EvaluationContext) (e : Expression) : EvaluationContext
| EvalContextRAdd (n : nat) (E : EvaluationContext) : EvaluationContext
| EvalContextLApp (E : EvaluationContext) (e : Expression) : EvaluationContext
| EvalContextRApp (f x : string) (τ : LType) (body : Expression) (E : EvaluationContext) : EvaluationContext.

Inductive EvaluationContextFillsTo : EvaluationContext -> Expression -> Expression -> Prop :=
| HoleFills {e} : EvaluationContextFillsTo Hole e e
| LAddFillsTo {E e1 e1' e2} (subFills : EvaluationContextFillsTo E e1 e1')
  : EvaluationContextFillsTo (EvalContextLAdd E e2) e1 (e1' + e2)
| RAddFillsTo {n E e2 e2'} (subFills : EvaluationContextFillsTo E e2 e2')
  : EvaluationContextFillsTo (EvalContextRAdd n E) e2 (n + e2')
| LAppFillsTo {E e1 e1' e2} (subFills : EvaluationContextFillsTo E e1 e1')
  : EvaluationContextFillsTo (EvalContextLApp E e2) e1 (AppExpr e1' e2)
| RAppFillsTo {f x τ body E e2 e2'} (subFills : EvaluationContextFillsTo E e2 e2')
  : EvaluationContextFillsTo (EvalContextRApp f x τ body E) e2 (AppExpr (AbsExpr f x τ body) e2').

Lemma EvalContextAlwaysFills {E e} : exists e', EvaluationContextFillsTo E e e'.
Proof with done.
  elim: E.
  - exists e...
  - move=> ? [x ?] e0; exists (AddExpr x e0)...
  - move=> n ? [x ?]; exists (AddExpr n x)...
  - move=> ? [x ?] e0; exists (AppExpr x e0)...
  - move=> f a τ body ? [x ?]; exists (AppExpr (AbsExpr f a τ body) x)...
Qed.

Bind Scope LType_scope with LType.
Notation "'ℕ'" := NatType : LType_scope.
Notation "a → b" := (AbsType a b) (at level 50, left associativity) : LType_scope.

Notation 𝔼 := Expression.
Notation 𝕋 := LType.
Notation 𝕍 := LValue.