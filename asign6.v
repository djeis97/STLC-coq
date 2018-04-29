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
  intros H s τ H0.
  induction H.
  - apply (H s τ).
    assumption.
  - destruct (string_dec s s0) as [-> | neq].
    + rewrite (InContextUnique H0 (InConsEnv)).
      constructor.
    + inversion H0.
      * congruence.
      * specialize (IHSubContext inSub).
        done.
  - inversion H0.
    + done.
    + specialize (IHSubContext inLeft).
      done.
Qed.

Lemma SubContextRefl Γ : SubContext Γ Γ.
  enough (forall s τ, s ∷ τ ∈ Γ -> s ∷ τ ∈ Γ).
  done.
  trivial.
Qed.

Lemma SubContextTrans {Γ1 Γ2 Γ3} : SubContext Γ1 Γ2 -> SubContext Γ2 Γ3 -> SubContext Γ1 Γ3.
  intros H H0.
  constructor.
  intros s τ H1.
  apply (InterpretSubContext H0).
  apply (InterpretSubContext H).
  assumption.
Qed.

Lemma SubEquiv {Γ1 Γ2} : EquivContext Γ1 Γ2 <-> (SubContext Γ1 Γ2 /\ SubContext Γ2 Γ1).
  split.
  - intros H.
    split.
    + apply SubIntro.
      intros s τ H0.
      rewrite <- (InterpretEquivContext H).
      assumption.
    + apply SubIntro.
      intros s τ H0.
      rewrite (InterpretEquivContext H).
      assumption.
  - intros (ab, ba).
    apply EquivIntro.
    intros s τ.
    split.
    + exact (InterpretSubContext ab).
    + exact (InterpretSubContext ba).
Qed.

Notation "a ⊆ b" := (SubContext a b) (at level 1, b at next level).

Lemma SubContextConsRight {Γ1 Γ2} : Γ1 ⊆ Γ2 -> forall x τ, x ∉ Γ1 -> Γ1 ⊆ (ConsEnv x τ Γ2).
  intros H x τ H0.
  apply SubIntro.
  intros s τ0 H1.
  destruct (string_dec s x) as [-> | neq].
  - destruct (InContextInverse H1 H0).
  - pose (InterpretSubContext H H1).
    done.
Qed.


Lemma Strengthening {s e} (notInFV : s ∉f e) : forall {Γ τ' τ} (typechecks1 : (ConsEnv s τ' Γ) ⊢ e ∷ τ), Γ ⊢ e ∷ τ.
  induction notInFV; intros Γ τ' τ'' typechecks1.
  - inversion typechecks1.
    subst.
    constructor.
    refine (InSubConsEnvInversion _ H1).
    congruence.
  - inversion typechecks1.
    subst.
    constructor.
  - inversion typechecks1.
    subst.
    constructor.
    + eapply IHnotInFV1; done.
    + eapply IHnotInFV2; done.
  - inversion typechecks1.
    subst.
    econstructor.
    + eapply IHnotInFV1; done.
    + eapply IHnotInFV2; done.
  - inversion typechecks1.
    subst.
    constructor.
    assumption.
    eapply IHnotInFV.
    enough (EquivContext (ConsEnv x τ (ConsEnv f (τ → τ'0) (ConsEnv s τ' Γ)))
                         (ConsEnv s τ' (ConsEnv x τ (ConsEnv f (τ → τ'0) Γ)))).
    exact (EquivContextAlsoTypechecks type1 H).
    pose (EquivContextReorder (EquivContextRefl (ConsEnv f (τ → τ'0) Γ)) notX τ τ').
    pose (EquivCons x τ (EquivContextReorder (EquivContextRefl Γ) notF (AbsType τ τ'0) τ')).
    exact (EquivContextTrans e0 e).
  - inversion typechecks1.
    subst.
    constructor.
    assumption.
    enough (EquivContext (ConsEnv x τ (ConsEnv f (τ → τ'0) (ConsEnv x τ' Γ))) (ConsEnv x τ (ConsEnv f (τ → τ'0) Γ))).
    exact (EquivContextAlsoTypechecks type1 H).
    pose (EquivCons x τ (EquivContextReorder (EquivContextRefl Γ) nefx (AbsType τ τ'0) τ')).
    pose (EquivContextDoubleElim (ConsEnv f (τ → τ'0) Γ) x τ τ').
    exact (EquivContextTrans e e0).
  - inversion typechecks1.
    subst.
    constructor.
    assumption.
    enough (EquivContext (ConsEnv x τ (ConsEnv f (τ → τ'0) (ConsEnv f τ' Γ))) (ConsEnv x τ (ConsEnv f (τ → τ'0) Γ))).
    exact (EquivContextAlsoTypechecks type1 H).
    exact (EquivCons x τ (EquivContextDoubleElim Γ f (AbsType τ τ'0) τ')).
Qed.

Lemma Weakening {Γ e τ} (typchecks1 : Γ ⊢ e ∷ τ) :
  forall {Γ'}, Γ ⊆ Γ' -> Γ' ⊢ e ∷ τ.
Proof with done.
  induction typchecks1; intros Γ'' Γ''sub.
  - done.
  - refine (VSE (InterpretSubContext Γ''sub _))...
  - refine (ASE (IHtypchecks1_1 _ _)
                (IHtypchecks1_2 _ _))...
  - refine (PSE (IHtypchecks1_1 _ _)
                (IHtypchecks1_2 _ _))...
  - specialize (IHtypchecks1 (ConsEnv x τ (ConsEnv f (τ → τ') Γ''))
                             (SubCons x τ (SubCons f (τ → τ') Γ''sub)))...
Qed.

Lemma OtherWeakening {s e} (sNotIn : s ∉f e) : forall {Γ τ} (typechecks1 : Γ ⊢ e ∷ τ) {τ'}, (ConsEnv s τ' Γ) ⊢ e ∷ τ.
Proof with done.
  induction sNotIn; intros Γ τ'' typechecks1 τ'; inv typechecks1; econstructor; subst.
  - refine (InSubConsEnv _ _)...
  - eapply IHsNotIn1...
  - eapply IHsNotIn2...
  - eapply IHsNotIn1...
  - eapply IHsNotIn2...
  - assumption.
  - specialize (IHsNotIn (ConsEnv x τ (ConsEnv f (τ → τ'0) Γ)) τ'0 type1 τ').
    apply (EquivContextAlsoTypechecks IHsNotIn).
    pose (EquivContextReorder (EquivContextRefl (ConsEnv f (τ → τ'0) Γ)) notX τ τ').
    pose (EquivCons x τ (EquivContextReorder (EquivContextRefl Γ) notF (AbsType τ τ'0) τ')).
    exact (EquivContextSymm (EquivContextTrans e0 e)).
  - assumption.
  - refine (EquivContextAlsoTypechecks type1 _).
    pose (EquivCons x τ (EquivContextReorder (EquivContextRefl Γ) nefx (AbsType τ τ'0) τ')).
    pose (EquivContextDoubleElim (ConsEnv f (τ → τ'0) Γ) x τ τ').
    exact (EquivContextSymm (EquivContextTrans e e0)).
  - assumption.
  - refine (EquivContextAlsoTypechecks type1 _).
    exact (EquivContextSymm (EquivCons x τ (EquivContextDoubleElim Γ f (AbsType τ τ'0) τ'))).
Qed.

Reserved Notation "a ≡ b % c" (at level 1, b at next level).

Inductive ContextCongruenceModuloS : ℾ -> ℾ -> string -> Prop :=
| CongModIntro Γ1 Γ2 s :
    (forall s' τ, (s=s') \/ (s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2)) ->
    (Γ1 ≡ Γ2 % s)
| CongModCons {Γ1 Γ2 s s' τ} : Γ1 ≡ Γ2 % s -> (ConsEnv s' τ Γ1) ≡ (ConsEnv s' τ Γ2) % s
| CongModShad {Γ1 Γ2 Γ' s} : Γ1 ≡ Γ2 % s -> (ShadowEnv Γ1 Γ') ≡ (ShadowEnv Γ2 Γ') % s
where "a ≡ b % c" := (ContextCongruenceModuloS a b c).

Lemma CongModRefl Γ s : Γ ≡ Γ % s.
  apply CongModIntro.
  intros s' τ.
  right.
  reflexivity.
Qed.

Lemma InterpretCongMod' {Γ1 Γ2 s}
  : Γ1 ≡ Γ2 % s -> forall s' τ, (s=s') \/ (s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2).
  intros H s' τ.
  induction H.
  - exact (H s' τ).
  - decompose [or] IHContextCongruenceModuloS.
    + done.
    + right.
      destruct H0.
      split; inversion 1; done.
  - decompose [or] IHContextCongruenceModuloS.
    + done.
    + right.
      destruct H0.
      split; inversion 1; done.
Qed.

Lemma InterpretCongMod {Γ1 Γ2 s}
  : Γ1 ≡ Γ2 % s -> forall {s' τ}, s<>s' -> (s' ∷ τ ∈ Γ1 <-> s' ∷ τ ∈ Γ2).
  intros H s' τ H0.
  destruct (InterpretCongMod' H s' τ); done.
Qed.

Lemma CongModSymm {Γ1 Γ2 s} : Γ1 ≡ Γ2 % s -> Γ2 ≡ Γ1 % s.
  intros H.
  eapply CongModIntro.
  intros s' τ.
  destruct (string_dec s s') as [-> | neq].
  - done.
  - right.
    symmetry.
    apply (InterpretCongMod H neq).
Qed.

Lemma CongModToEquiv {Γ1 Γ2 s} : Γ1 ≡ Γ2 % s -> forall τ, (EquivContext (ConsEnv s τ Γ1) (ConsEnv s τ Γ2)).
  intros H τ.
  eapply EquivIntro.
  intros s0 τ0.
  epose (InterpretCongMod' H).
  - destruct (string_dec s s0) as [-> | neq].
    + split; intros H'; inversion H'; done.
    + destruct (o s0 τ0) as [-> | equiv].
      contradiction.
      split; intros H'; inversion H'; done.
Qed.

Lemma CongModConsLeft {x τ Γ1 Γ2} : Γ1 ≡ Γ2 % x -> (ConsEnv x τ Γ1) ≡ Γ2 % x.
  intros H.
  eapply CongModIntro.
  intros s' τ0.
  destruct (string_dec s' x) as [-> | neq].
  - done.
  - right.
    split.
    + intros H0.
      pose (InSubConsEnvInversion neq H0).
      eapply InterpretCongMod.
      eapply CongModSymm.
      exact H.
      congruence.
      eapply InSubConsEnvInversion.
      exact neq.
      exact H0.
    + intros H0.
      eapply InSubConsEnv.
      done.
      enough (x <> s').
      rewrite (InterpretCongMod H H1).
      done.
      congruence.
Qed.

Lemma Substitution {e1 Γ1 τ1} (typechks1 : Γ1 ⊢ e1 ∷ τ1) : forall e2 e3 Γ2 τ2 s,
  (s ∷ τ2 ∈ Γ1) ->
  Γ2 ⊢ e2 ∷ τ2 ->
  Γ1 ≡ Γ2 % s ->
  [e2 / s] e1 = e3 ->
  Γ2 ⊢ e3 ∷ τ1.
Proof with done.
  intros e2 e3 Γ2 τ2 s H H0 H1 H2.
  dependent induction typechks1. 
  - inversion H2...
  - inversion H3.
    subst.
    rewrite (InContextUnique H H0)...
    rewrite (InterpretCongMod H2 neq) in H...
  - inversion H2.
    subst.
    constructor.
    + eapply IHtypechks1_1.
      exact H.
      exact H0.
      exact H1.
      exact LeftAddCAS.
    + eapply IHtypechks1_2.
      exact H.
      exact H0.
      exact H1.
      exact RightAddCAS.
  - inversion H2.
    subst.
    eapply PSE.
    + eapply IHtypechks1_1.
      exact H.
      exact H0.
      exact H1.
      exact LeftAppCAS.
    + eapply IHtypechks1_2.
      exact H.
      exact H0.
      exact H1.
      exact RightAppCAS.
  - inversion H2.
    subst.
    + eapply BSE.
      assumption.
      eapply IHtypechks1.
      * exact (InSubConsEnv notX (InSubConsEnv notF H)).
      * eapply (OtherWeakening _).
        eapply (OtherWeakening _).
        eassumption.
      * exact (CongModCons (CongModCons H1)).
      * assumption.
    + subst.
      eapply BSE.
      assumption.
      pose (EquivCons x τ (CongModToEquiv H1 (τ → τ'))).
      refine (EquivContextAlsoTypechecks _ _).
      exact typechks1.
      exact e.
    + subst.
      eapply BSE.
      assumption.
      pose (@CongModCons _ _ _ f (τ → τ') H1).
      pose (CongModToEquiv c τ).
      refine (EquivContextAlsoTypechecks _ _).
      exact typechks1.
      exact e.
      Unshelve.
      assumption.
      assumption.
Qed.

Lemma CannonicalForms {e τ} :
  NullEnv ⊢ e ∷ τ -> (𝕍 e) ->
  match τ with
  | NatType => exists n, e = (NatExpr n)
  | (AbsType τ1 τ2) => exists f x body, f<>x /\ (e = (AbsExpr f x τ1 body))
  end.
  intros H H0.
  destruct H.
  - exists n; done.
  - inversion H0.
  - inversion H0.
  - inversion H0.
  - exists f.
    exists x.
    exists body.
    done.
Qed.

Lemma TypedEvalContextInversion {Γ E τ0 τ} (Etype : Γ ⊢ E [τ0] ∷ τ)
  : exists x e, x ∉ Γ /\ EvaluationContextFillsTo E x e /\ (ConsEnv x τ0 Γ) ⊢ e ∷ τ.
  destruct Etype.
  - destruct (ContextFinite Γ).
    exists x.
    exists x.
    done.
  - exists x.
    exists (AddExpr e1 e2).
    epose (Weakening H (SubContextConsRight (SubContextRefl Γ) τ H0)).
    done.
  - exists x.
    exists (AddExpr n e).
    done.
  - exists x.
    exists (AppExpr e1 e2).
    epose (Weakening H (SubContextConsRight (SubContextRefl Γ) τ H0)).
    done.
  - exists x.
    exists (AppExpr (AbsExpr fn arg τarg body) e).
    epose (Weakening H (SubContextConsRight (SubContextRefl Γ) τ H0)).
    done.
Qed.

Lemma DecompositionOfTypes {E} : forall {e0 e1 Γ τ},
    EvaluationContextFillsTo E e0 e1 -> Γ ⊢ e1 ∷ τ -> exists τ1, Γ ⊢ e0 ∷ τ1 /\ Γ ⊢ E [τ1] ∷ τ.
  induction E; intros e0 e1 Γ τ' H H0.
  all:inversion H; subst.
  exists τ'; done.
  all:inversion H0; subst.
  - destruct (IHE e0 e1' Γ NatType subFills type1) as (τ1, (typ1, typ2)).
    exists τ1.
    destruct (TypedEvalContextInversion typ2) as (x, (e2, (notIn, (fills, typ3)))).
    done.
  - destruct (IHE e0 e2' Γ NatType subFills type2) as (τ1, (typ1, typ2)).
    exists τ1.
    destruct (TypedEvalContextInversion typ2) as (x, (e2, (notIn, (fills, typ3)))).
    done.
  - destruct (IHE e0 e1' Γ (AbsType τ1 τ') subFills type1) as (τ2, (typ1, typ2)).
    exists τ2.
    destruct (TypedEvalContextInversion typ2) as (x, (e2, (notIn, (fills, typ3)))).
    done.
  - inversion type1.
    destruct (IHE e0 e2' Γ τ1 subFills type2) as (τ2, (typ1, typ2)).
    exists τ2.
    destruct (TypedEvalContextInversion typ2) as (s, (e2, (notIn, (fills, typ3)))).
    done.
Qed.

Definition CanStep e := exists e', e ⥛ e'.
Definition NotStuck e := 𝕍 e \/ (CanStep e).

Lemma Progress {e} : forall {τ} (etyp: NullEnv ⊢ e ∷ τ), (NotStuck e).
  induction e.
  - intros; subst.
    inversion etyp.
    inversion H1.
  - left; now constructor.
  - intros τ etyp.
    inversion etyp.
    right.
    subst.
    specialize (IHe1 _ type1).
    specialize (IHe2 _ type2).
    destruct IHe1 as [ ve1 | se1 ].
    + destruct (CannonicalForms type1 ve1).
      subst.
      destruct IHe2 as [ ve2 | se2 ].
      * destruct (CannonicalForms type2 ve2).
        exists (NatExpr (x + x0)).
        done.
      * inversion se2.
        inversion H.
        done.
    + inversion se1.
      inversion H.
      exists (AddExpr x e2).
      done.
  - done.
  - intros τ etyp.
    inversion etyp.
    subst.
    specialize (IHe1 _ type1).
    specialize (IHe2 _ type2).
    right.
    destruct IHe1 as [ ve1 | se1 ].
    + destruct (CannonicalForms type1 ve1) as (f1, (x1, (body1, (ne1, eq1)))).
      subst.
      * inversion type1.
        subst.
        destruct IHe2 as [ ve2 | se2 ].
        -- destruct (@CASAlways e2 x1 body1) as (body2, cas1).
           apply AlwaysSafeToSubInto.
           destruct (@CASAlways (AbsExpr f1 x1 τ1 body1) f1 body2) as (body3, cas2).
           apply AlwaysSafeToSubInto.
           exists body3.
           done.
        -- inversion se2.
           inversion H.
           subst.
           exists (AppExpr (AbsExpr f1 x1 τ1 body1) x).
           done.
    + inversion se1.
      inversion H.
      exists (AppExpr x e2).
      done.
Qed.

Lemma βPreservation {e e'} (estep : e ⥛β e') : forall τ (etyp : NullEnv ⊢ e ∷ τ),  NullEnv ⊢ e' ∷ τ.
  induction estep; intros τ0 etyp; inversion etyp.
  - done.
  - subst.
    inversion type1.
    subst.
    eapply Substitution.
    + eapply Substitution.
      * exact type0.
      * apply InConsEnv.
      * eapply Weakening.
        exact type2.
        eapply SubContextConsRight.
        apply SubContextRefl.
        apply (@NotInNullEnv f).
      * eapply CongModConsLeft.
        apply CongModRefl.
      * exact CASx.
    + apply InConsEnv.
    + exact type1.
    + eapply CongModConsLeft.
      apply CongModRefl.
    + exact CASf.
Qed.

Lemma Preservation {e e'} (estep : e ⥛ e') : forall τ (etyp : NullEnv ⊢ e ∷ τ),  NullEnv ⊢ e' ∷ τ.
  intros τ etyp.
  inversion estep.
  subst.
  destruct (DecompositionOfTypes fillse1 etyp) as (τn, (typee1, ?)).
  pose (typee2 := βPreservation betaStep typee1).
  eapply InterpretTypedEvalContext.
  exact H.
  exact typee2.
  exact fillse2.
Qed.

Lemma Safety {e τ} (etyp : NullEnv ⊢ e ∷ τ) {e'} (estep : e ⥛* e') : (NotStuck e').
  induction estep.
  - now apply (Progress etyp).
  - apply (IHestep (Preservation ess etyp)).
Qed.


