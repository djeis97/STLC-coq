From Coq Require Import ssreflect ssrfun ssrbool.
Require Import FunInd.
Require Import String.
Require Import List.
Require Import ListSet.
Require Import MyBase.

Inductive LType : Set :=
| NatType : LType
| AbsType (arg ret : LType) : LType.

Lemma LType_dec : forall (τ1 τ2 : LType), {τ1=τ2} + {τ1 <> τ2}.
  decide equality.
Defined.

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

Reserved Notation "E [ e ]" (at level 1, e at next level).

Fixpoint FillEvaluationContext E e :=
  match E with
  | Hole => e
  | EvalContextLAdd E0 e0 => (AddExpr E0[e] e0)
  | EvalContextRAdd n E0 => (AddExpr n E0[e])
  | EvalContextLApp E0 e0 => (AppExpr E0[e] e0)
  | EvalContextRApp f x τ body E0 =>
    (AppExpr (AbsExpr f x τ body) E0[e])
  end
where "E [ e ]" := (FillEvaluationContext E e).

Functional Scheme FillEvaluationContext_ind
  := Induction for FillEvaluationContext Sort Set.

Bind Scope LType_scope with LType.
Notation "'ℕ'" := NatType : LType_scope.
Notation "a → b" := (AbsType a b) (at level 50, left associativity) : LType_scope.

Notation 𝔼 := Expression.
Notation 𝕋 := LType.
Notation 𝕍 := LValue.