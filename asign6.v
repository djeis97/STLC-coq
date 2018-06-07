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
Defined.

Ltac weakening := apply/Weakening/(SubContextConsRight (SubContextRefl _)).

Lemma OtherWeakening {s e} (sNotIn : s ∉f e) : forall {Γ τ} (typechecks1 : Γ ⊢ e ∷ τ) {τ'}, (ConsEnv s τ' Γ) ⊢ e ∷ τ.
  elim: sNotIn; intros; match goal with H: _ ⊢ _ ∷ _ |- _ => inv H end.
  all: try done.
  all: econstructor; first done.
  - by apply/(EquivContextAlsoTypechecks (H _ _ type1 τ'))/EquivContextP => ? /=; program_equiv.
  - by apply/(EquivContextAlsoTypechecks type1)/EquivContextP => ? /=; program_equiv.
  - by apply/(EquivContextAlsoTypechecks type1)/EquivContextP => ? /=; program_equiv.
Defined.

Hint Resolve (@OtherWeakening).
Hint Resolve (@Weakening).

Hint Resolve InContextUnique.

Lemma Substitution {e1 Γ1 τ1} (typechks1 : Γ1 ⊢ e1 ∷ τ1) : forall e2 e3 Γ2 τ2 s
  (in1: s ∷ τ2 ∈ Γ1) (ty2: Γ2 ⊢ e2 ∷ τ2) (cong: Γ1 ≡ Γ2 % s) (sub: [e2 / s] e1 = e3), Γ2 ⊢ e3 ∷ τ1.
  induction typechks1; intros; inversion sub; subst.
  1,4,5,7,8: done.
  - by have: τ=τ2.
  - by have: s ∷ τ ∈ Γ2 by rewrite -InterpretCongMod.
  - by have: let G Γ := (ConsEnv x τarg (ConsEnv f (τarg → τret) Γ)) in s ∷ τ2 ∈ (G Γ) /\ (G Γ2) ⊢ e2 ∷ τ2.
Defined.

Lemma CannonicalForms {Γ e τ} :
  Γ ⊢ e ∷ τ -> forall (v: 𝕍 e),
  match τ with
  | NatType => {n | e = (NatExpr n)}
  | (AbsType τ1 τ2) => {tup  | match tup with (f, x, body) => f<>x /\ (e = (AbsExpr f x τ1 τ2 body)) end}
  end.
  move/TypechecksP.
  functional inversion 1; try done.
  intros vabs.
  exists (f, x, body).
  done.
  Unshelve.
  all: done.
Defined.

Ltac Cannonicalize := repeat (match goal with
                              | V: 𝕍 ?e, T: _ ⊢ ?e ∷ _ |- _ =>
                                move: (CannonicalForms T V); intro; destruct V eqn:?
                              end).

Lemma TypedEvalContextInversion {Γ E τ0 τ} : Γ ⊢ E {τ0} ∷ τ -> exists x, x ∉ Γ /\ (ConsEnv x τ0 Γ) ⊢ E[x] ∷ τ.
  by induction 1; simpl; first by destruct (ContextFinite Γ).
Defined.

Lemma TypedBinopExprInversion {Γ f e1 e2 τ} : Γ ⊢ (BinExpr f e1 e2) ∷ τ -> {τ1 | Γ ⊢ e1 ∷ τ1} * {τ2 | Γ ⊢ e2 ∷ τ2}.
  move/TypechecksP => typ.
  by functional inversion typ; subst; repeat match goal with H : (typchk _ _) = _ |- _ => move/TypechecksP in H end.
Defined.

Lemma DecompositionOfTypes E : forall Γ e0 τ, Γ ⊢ E[e0] ∷ τ -> exists τ1, Γ ⊢ e0 ∷ τ1 /\ Γ ⊢ E {τ1} ∷ τ.
  induction E; intros; simpl in *; first done.
  all: inversion H.
  1,2: by move/IHE: type1 => [τx [? b]]; move:(TypedEvalContextInversion b).
  1,2: move/IHE: type2 => [τx [? b]]; move:(TypedEvalContextInversion b); Cannonicalize => //=.
  intros; elim_exists.
  inversion CannonicalForms0.
  destruct x1.
  destruct p.
  case: H6 => ?; case.
  done.
Defined.

Definition CanStep e := exists e0, e ⥛ e0.
Definition CanStepβ e := exists e0, e ⥛β e0.
Definition CanStepEβ e := exists E e0, e=E[e0] /\ CanStepβ e0.
Definition NotStuck e := 𝕍 e \/ (CanStep e).
Definition NotStuckβ e := 𝕍 e \/ (CanStepβ e).
Definition NotStuckEβ e := 𝕍 e \/ (CanStepEβ e).

Hint Constructors EvaluationContext.

Ltac CAS := apply/CASAlways/AlwaysSafeToSubInto.

Lemma ProgressApp {Γ e1 e2 τ} : Γ ⊢ (BinExpr AppExpr e1 e2) ∷ τ -> (𝕍 e1) -> (𝕍 e2) -> {e0 | (BinExpr AppExpr e1 e2) ⥛β e0}.
  move/TypechecksP => typ.
  functional inversion typ; subst; repeat (match goal with | H : (typchk _ _) = _ |- _ => move/TypechecksP in H end).
  move/(CannonicalForms H3) => [[[f x] body] [? ?]] v2.
  have: {b | [e2 / x] body = b} by CAS.
  move => [x0 ?].
  have: {b | [(AbsExpr f x τa1 τ body) / f] x0 = b} by CAS.
  move => [x1 ?].
  done.
Defined.

Lemma ProgressBin : forall f {e1 e2 Γ τ} (typ: Γ ⊢ (BinExpr f e1 e2) ∷ τ) (v1 : 𝕍 e1) (v2 : 𝕍 e2), {e0 | (BinExpr f e1 e2) ⥛β e0}.
  move => f e1 e2 Γ τ typ v1 v2.
  move/TypechecksP in typ.
  functional inversion typ; subst; repeat (match goal with | H : (typchk _ _) = _ |- _ => move/TypechecksP in H end).
  - by move: (CannonicalForms H4 v1) (CannonicalForms H5 v2) => [n0 ->] [n1 ->].
  - exact/ProgressApp.
Defined.

Record SteppableDecomposedExpr (e : 𝔼) : Set :=
  mkDecomposed {
      DContext : EvaluationContext ;
      DExpr : 𝔼 ;
      DIsDecomp : e = DContext[DExpr] ;
      DSteps : {e0 | DExpr ⥛β e0}
    }.

Lemma ValDec : forall e, decidable (𝕍 e).
  by case.
Defined.

Program Fixpoint EvalContextDecomp e (nv : ~ 𝕍 e) (τ: {τ | NullEnv ⊢ e ∷ τ}) {struct e} : SteppableDecomposedExpr e :=
  match e with
  | VarExpr _ => _
  | NatExpr n => _
  | AbsExpr _ _ _ _ _ => _
  | BinExpr op l r =>
    match (ValDec l) with
    | left vl => 
      match (ValDec r) with
      | left vr => 
        @mkDecomposed e Hole e _ _
      | right nvr =>
        let decomp := (EvalContextDecomp _ _) in
        @mkDecomposed e (EvalContextBinR op vl (DContext decomp)) (DExpr decomp) _ _
      end
    | right nvl =>
      let decomp := (@EvalContextDecomp l _ _) in
      @mkDecomposed e (EvalContextBinL op (DContext decomp) r) (DExpr decomp) _ _
    end
  end.
Next Obligation.
  suff: forall s τ, NullEnv ⊢ (VarExpr s) ∷ τ -> False by move=> /(_ wildcard' τ).
  move=> s τ0; inversion 1; inversion H3.
Defined.
Next Obligation.
  case (nv (NatValue n)).
Defined.
Next Obligation.
  case (nv (AbsValue _ _ _ _ _)).
Defined.
Next Obligation.
  exact (ProgressBin H vl vr).
Defined.
Next Obligation.
  simpl.
  move/TypedBinopExprInversion in H.
  inversion H.
  inversion H1.
  done.
Defined.
Next Obligation.
  by simpl in *; move/TypedBinopExprInversion in H.
Defined.

Lemma Progressβ {e τ} (ety: NullEnv ⊢ e ∷ τ) : NotStuckEβ e.
  induction e => //=.
  - inversion ety; inversion H1.
  - have: ~ (𝕍 (BinExpr f e1 e2)) by done.
    by move=> nv; destruct (EvalContextDecomp nv ltac:(done)); move: DSteps0 => [e0 step].
Defined.

Lemma Progress {e} : forall {τ} (etyp: NullEnv ⊢ e ∷ τ), (NotStuck e).
    by move=> τ /Progressβ; move=> [v | [E [e0 [-> [e1 bstep]]]]].
Defined.

Hint Resolve Progress.

Lemma βPreservation {e e'} (estep : e ⥛β e') : forall τ (etyp : NullEnv ⊢ e ∷ τ),  NullEnv ⊢ e' ∷ τ.
  induction estep; move=> τ0; inversion 1; first done.
  subst; inversion type1; subst.
  (have: ((ConsEnv f (τ1 → τ0) NullEnv) ⊢ e ∷ τ1) by done) => ?.
  by apply/Substitution; first by apply/Substitution.
Defined.

Hint Resolve βPreservation.

Hint Resolve InterpretTypedEvalContext.

Lemma Preservation {e e'} (estep : e ⥛ e') τ (etyp : NullEnv ⊢ e ∷ τ) : NullEnv ⊢ e' ∷ τ.
  by inversion estep; subst; move: (DecompositionOfTypes E e1 etyp).
Defined.

Hint Resolve Preservation.

Lemma Safety {e τ} (etyp : NullEnv ⊢ e ∷ τ) {e'} (estep : e ⥛* e') : (NotStuck e').
  by induction estep.
Defined.

Lemma Preservation0 {e e0} (estep : e ⥛ e0) : {τ | NullEnv ⊢ e ∷ τ} -> {τ | NullEnv ⊢ e0 ∷ τ}.
  inversion 1.
  econstructor.
  by apply/Preservation.
Defined.

CoInductive Stream (A: Type) : Type :=
| SNil : Stream A
| SCons (e : A) (tl: Stream A) : Stream A.

CoFixpoint Evaluate (e : 𝔼) (τ : {τ | NullEnv ⊢ e ∷ τ}) : Stream 𝔼.
  refine (match (ValDec e) with
          | left v => SNil 𝔼
          | right nv => let decomp := EvalContextDecomp nv τ in
                       let: (exist _ e0 step) := (DSteps decomp) in
                       let newe := (DContext decomp)[e0] in
                       SCons newe (@Evaluate newe (Preservation0 (@ECSS (DContext decomp) (DExpr decomp) e0 step) _))
          end).
  by rewrite <- (DIsDecomp decomp).
Defined.

Fixpoint approx {A} (s : Stream A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | SCons h t => h :: approx t n'
        | SNil _ => nil
      end
  end.

Definition Evaluate0 (e : 𝔼) : Stream 𝔼.
  refine ((match (typchk NullEnv e) as st return ((typchk NullEnv e) = st -> _) with
           | (Some τ) => (fun (eq: (typchk NullEnv e) = (Some τ)) => _)
           | None => (fun (eq: (typchk NullEnv e) = None) => SNil 𝔼)
           end) (eq_refl (typchk NullEnv e))).
  by move/TypechecksP in eq; apply/Evaluate.
Defined.
Set Printing Implicit.
Eval vm_compute in (approx (Evaluate0 (BinExpr AddExpr 5 5)) 3).
match
         (let
          'exist _ e0 step :=
           ProgressBin (iffRL (P:=NullEnv ⊢ (5 + 5) ∷ ℕ) TypechecksP (erefl (Some NatType))) (NatValue 5) (NatValue 5) in
           SCons e0
             (Evaluate
                (exist [eta Typechecks NullEnv e0] NatType
                   (InterpretTypedEvalContext (TypedHole NullEnv ℕ)
                      (βPreservation step (iffRL (P:=NullEnv ⊢ (5 + 5) ∷ ℕ) TypechecksP (erefl (Some NatType))))))))
       with
       | SNil _ => nil
       | SCons h t =>
           h :: match t with
                | SNil _ => nil
                | SCons h0 t0 => h0 :: match t0 with
                                       | SNil _ => nil
                                       | SCons h1 _ => h1 :: nil
                                       end
                end
       end
Eval eta in (match
                  (let 'exist _ e0 step :=
                       ProgressBin (iffRL (P:=NullEnv ⊢ (5 + 5) ∷ ℕ) TypechecksP (erefl (Some NatType))) (NatValue 5) (NatValue 5) in
                   SCons e0
                         (Evaluate
                            (Preservation0 (ECSS step)
                                           (exist (fun x => Typechecks NullEnv Hole [(5 + 5)] x) NatType
                                                  (iffRL (P:=NullEnv ⊢ (5 + 5) ∷ ℕ) TypechecksP (erefl (Some NatType)))))))
          with
          | SNil _ => nil
          | SCons h t => h :: match t with
                             | SNil _ => nil
                             | SCons h0 _ => h0 :: nil
                             end
                end).






