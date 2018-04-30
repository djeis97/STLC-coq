From Coq Require Import ssreflect ssrfun ssrbool.
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

Lemma InContextInverse {Γ s τ} (ing: s∷τ ∈ Γ) (noting: s ∉ Γ) : False.
  induction ing; inversion noting => //.
Qed.

Lemma InContextOptions Γ s : (exists τ, s∷τ∈Γ) \/ (s∉Γ).
  elim: Γ => //.
  - move=> var typ ? [[τ ?] | ?]; case: (string_dec s var) => [ -> | ? ] //.
  - move=> Γ1 [[τ1 ?] | ?] Γ2 [[τ2 ?] | ?] //.
Qed.

Lemma InContextUnique {s τ1 τ2 Γ} (τin1: s ∷ τ1 ∈ Γ) (τin2: s ∷ τ2 ∈ Γ) : τ1=τ2.
  elim: Γ τin1 τin2 => //.
  - move=> var typ Γ impl; inversion 1; inversion 1 => //.
  - move=> Γ1 impl1 Γ2 impl2; inversion 1; inversion 1 => //.
    + case: (InContextInverse inRight notInRight).
    + case: (InContextInverse inRight notInRight).
Qed.

Lemma InConsEnvInversion {s τ τ' Γ} : s ∷ τ ∈ (ConsEnv s τ' Γ) -> τ=τ'.
  move=> ?; exact: InContextUnique.
Qed.

Lemma InSubConsEnvInversion {s s' Γ} (neq : s<>s') {τ τ'} : s ∷ τ ∈ (ConsEnv s' τ' Γ) -> s ∷ τ ∈ Γ.
  inversion 1 => //.
Qed.

Inductive EquivContext : ℾ -> ℾ -> Prop :=
| EquivIntro {Γ1 Γ2} : (forall s τ, s ∷ τ ∈ Γ1 <-> s ∷ τ ∈ Γ2) -> EquivContext Γ1 Γ2
| EquivCons s τ {Γ1 Γ2} : EquivContext Γ1 Γ2 -> EquivContext (ConsEnv s τ Γ1) (ConsEnv s τ Γ2)
| EquivShadow {Γ1 Γ2} Γ' : EquivContext Γ1 Γ2 -> EquivContext (ShadowEnv Γ1 Γ') (ShadowEnv Γ2 Γ').

Lemma InterpretEquivContext' {Γ1 Γ2} : EquivContext Γ1 Γ2 -> forall {s τ}, s ∷ τ ∈ Γ1 -> s ∷ τ ∈ Γ2.
Proof with done.
  elim => //.
  - move=> Γ0 Γ3 rewr s τ; rewrite rewr...
  - move=> s0 τ0 Γ0 Γ3 EquivSub IH s1 τ1; case: (string_dec s1 s0) => [-> | neq] inH.
    + rewrite (InContextUnique inH (@InConsEnv s0 τ0 Γ0))...
    + constructor => //; apply IH.
      pose inSub := InSubConsEnvInversion neq inH...
  - move=> Γ0 Γ3 Γ' EquivSub IH s τ; inversion 1 => //.
    apply IH in inLeft...
Qed.

Lemma EquivContextRefl Γ : EquivContext Γ Γ.
  enough (forall s τ, s ∷ τ ∈ Γ <-> s ∷ τ ∈ Γ); done.
Qed.

Lemma EquivContextSymm {Γ1 Γ2} : EquivContext Γ1 Γ2 -> EquivContext Γ2 Γ1.
  elim; done.
Qed.

Lemma InterpretEquivContext {Γ1 Γ2} : EquivContext Γ1 Γ2 -> forall {s τ}, s ∷ τ ∈ Γ1 <-> s ∷ τ ∈ Γ2.
  move=> H s τ.
  split.
  - exact: InterpretEquivContext'.
  - apply: InterpretEquivContext'; exact: EquivContextSymm.
Qed.

Lemma EquivContextTrans {Γ1 Γ2 Γ3} (e12 : EquivContext Γ1 Γ2) (e23 : EquivContext Γ2 Γ3) : EquivContext Γ1 Γ3.
  constructor => s τ; rewrite (InterpretEquivContext e12); rewrite (InterpretEquivContext e23); done.
Qed.

Lemma EquivContextDoubleElim Γ s τ τ' : (EquivContext (ConsEnv s τ (ConsEnv s τ' Γ)) (ConsEnv s τ Γ)).
  apply EquivIntro => s0 τ0.
  case: (string_dec s0 s) => [-> | ?]; split => ing.
  1,2: by rewrite (InConsEnvInversion ing).
  - constructor => //; exact: (InSubConsEnvInversion _ (InSubConsEnvInversion _ ing)).
  - constructor => //; constructor => //; exact: (InSubConsEnvInversion _ ing).
Qed.

Lemma EquivContextReorder {Γ1 Γ2 s s'} :
  (EquivContext Γ1 Γ2) -> s<>s' -> forall τ τ', (EquivContext (ConsEnv s τ (ConsEnv s' τ' Γ1)) (ConsEnv s' τ' (ConsEnv s τ Γ2))).
Proof with done.
  move=> H neq τ τ'.
  constructor 1 => s0 τ0.
  split; case: (string_dec s0 s) => [-> | nes].
  - move=> inOne; rewrite (InConsEnvInversion inOne); constructor => //; constructor.
  - case: (string_dec s0 s') => [<- | nes'] inOne.
    + inversion inOne => //.
      rewrite (InConsEnvInversion inSub)...
    + inversion inOne => //; inversion inSub => //.
      constructor => //; constructor => //.
      move: inSub0; rewrite (InterpretEquivContext H)...
Admitted.
(*   -  *)
(*     destruct (string_dec s0 s) as [-> | nes]. *)
(*     + rewrite (InConsEnvInversion inOne). *)
(*       apply (InSubConsEnv neq). *)
(*       apply InConsEnv. *)
(*     + destruct (string_dec s0 s') as [-> | nes']. *)
(*       * pose (InSubConsEnvInversion nes inOne). *)
(*         rewrite (InConsEnvInversion i). *)
(*         done. *)
(*       * apply (InSubConsEnv nes'). *)
(*         apply (InSubConsEnv nes). *)
(*         apply (InterpretEquivContext H). *)
(*         exact (InSubConsEnvInversion nes' (InSubConsEnvInversion nes inOne)). *)
(*   - destruct (string_dec s0 s) as [-> | nes]. *)
(*     + rewrite (InConsEnvInversion (InSubConsEnvInversion neq inOne)). *)
(*       apply InConsEnv. *)
(*     + destruct (string_dec s0 s') as [-> | nes']. *)
(*       * rewrite (InConsEnvInversion inOne). *)
(*         apply (InSubConsEnv nes). *)
(*         done. *)
(*       * apply (InSubConsEnv nes). *)
(*         apply (InSubConsEnv nes'). *)
(*         apply (InterpretEquivContext H). *)
(*         exact (InSubConsEnvInversion nes (InSubConsEnvInversion nes' inOne)). *)
(* Qed. *)

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
Proof with done.
  intros H.
  induction H; intros Γ2 equiv.
  - constructor.
  - rewrite (InterpretEquivContext equiv) in H...
  - specialize (IHTypechecks1 Γ2 equiv).
    specialize (IHTypechecks2 Γ2 equiv)...
  - specialize (IHTypechecks1 Γ2 equiv).
    specialize (IHTypechecks2 Γ2 equiv)...
  - specialize (IHTypechecks (ConsEnv x τ (ConsEnv f (τ → τ') Γ2))).
    pose (EquivCons x τ (EquivCons f (τ → τ') equiv)).
    specialize (IHTypechecks e)...
Qed.

Fixpoint concatenation (l : list string) :=
  match l with
  | nil => ""%string
  | cons s l' => (s ++ (concatenation l'))%string
  end.

Theorem appendEmpty s : (s ++ "")%string = s. 
  induction s.
  - simpl.
    reflexivity. 
  - rewrite <- IHs at 2.
    simpl.
    reflexivity.
Qed.

Theorem appendSomething s s' : s' <> ""%string -> (s ++ s')%string <> s.
Proof with congruence.
  intros H.
  induction s.
  - simpl...
  - simpl...
Qed.

Theorem appendAssociative s s' s'' : ((s ++ s') ++ s'')%string = (s ++ (s' ++ s''))%string.
  induction s.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHs.
    reflexivity.
Qed.

Theorem diffLenDiffStr s : forall s', (String.length s) <> (String.length s') -> s <> s'.
  induction s; destruct 2; simpl; contradiction.
Qed.

Theorem sumAppendLength s s' : String.length (s ++ s') = String.length s + String.length s'.
  induction s.
  - simpl.
    reflexivity.
  - simpl.
    congruence.
Qed.

Theorem concatenationLength {l s} : s ∈ l -> (String.length s) <= (String.length (concatenation l)).
  induction l.
  - contradiction.
  - intros H.
    simpl.
    rewrite sumAppendLength.
    inversion H.
    + subst; simpl.
      apply Plus.le_plus_l.
    + specialize (IHl H0).
      rewrite PeanoNat.Nat.add_comm.
      apply Plus.le_plus_trans.
      assumption.
Qed.

Theorem concatenationNotAny {l s} : s ∈ l -> s <> ((concatenation l) ++ "x")%string.
Proof with done.
  intros H.
  pose (concatenationLength H).
  pose (sumAppendLength (concatenation l) "x").
  simpl in e.
  pose (Lt.le_lt_n_Sm _ _ l0).
  rewrite PeanoNat.Nat.add_1_r in e.
  rewrite <- e in l1.
  apply diffLenDiffStr.
  exact (PeanoNat.Nat.lt_neq _ _ l1).
Qed.

Theorem concatNotIn l : ~ ((concatenation l) ++ "x")%string ∈ l.
  unfold not.
  intros H.
  pose (concatenationNotAny H).
  contradiction.
Qed.

Theorem ListFinite (l : list string) : exists x, ~ (x ∈ l).
  exists ((concatenation l) ++ "x")%string.
  apply concatNotIn.
Qed.

Fixpoint ContextVars (Γ : ℾ) :=
  match Γ with
  | NullEnv => nil
  | ConsEnv x τ Γ' => x :: (ContextVars Γ')
  | ShadowEnv Γ1 Γ2 => ((ContextVars Γ1) ++ (ContextVars Γ2))
  end.

Theorem ConcatDomainIsDomain {Γ x} : (~ x ∈ (ContextVars Γ)) <-> x ∉ Γ.
  split.
  - induction Γ; simpl.
    + constructor.
    + intros H.
      rewrite or_not_iff in H.
      inversion H.
      specialize (IHΓ H1).
      done.
    + intros H.
      rewrite in_app_iff in H.
      rewrite or_not_iff in H.
      inversion H.
      specialize (IHΓ1 H0).
      specialize (IHΓ2 H1).
      done.
  - induction Γ; simpl; intros H; unfold not; intro H1.
    + contradiction.
    + inversion H1; inversion H; subst.
      * contradiction.
      * pose (IHΓ notInSub).
        contradiction.
    + inversion H; subst.
      * rewrite in_app_iff in H1.
        inversion H1.
        -- pose (IHΓ1 notInLeft); contradiction.
        -- pose (IHΓ2 notInRight); contradiction.
Qed.

Theorem ContextFinite Γ : exists x, x ∉ Γ.
  pose (ListFinite (ContextVars Γ)).
  inversion e.
  exists x.
  now apply ConcatDomainIsDomain.
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
