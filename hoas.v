Require Import List.
Require Import ListSet.
Require Import String.
Require Import Basics.
Require Import MyBase.
Require Import lang.
Import ListNotations.

Reserved Notation "a '∈f' b" (at level 1, no associativity).
Reserved Notation "a '∉f' b" (at level 1, no associativity).
Reserved Notation "a '∈b' b" (at level 1, no associativity).

Inductive NotInFV : string -> 𝔼 -> Prop :=
| NotFVVarExpr {s1 s2} (neq : s1 <> s2) : s1 ∉f s2
| NotFVNatExpr {s} {n : nat} : s ∉f n
| NotFVAddExpr {s e1 e2} (notInLeft : s ∉f e1) (notInRight : s ∉f e2) : s ∉f (e1 + e2)
| NotFVAppExpr {s e1 e2} (notInLeft : s ∉f e1) (notInRight : s ∉f e2) : s ∉f (AppExpr e1 e2)
| NotFVAbsExpru f x τ body {s} (notF : f <> s) (notX : x <> s) (notInBody : s ∉f body) : s ∉f (AbsExpr f x τ body)
| NotFVAbsExprx f x τ body : x ∉f (AbsExpr f x τ body)
| NotFVAbsExprf f x τ body : f ∉f (AbsExpr f x τ body)
where "s ∉f e" := (NotInFV s e) : FV_scope.

Inductive InFV : string -> 𝔼 -> Prop :=
| FVVarExpr {s} : s ∈f s
| FVAddExprL {s e1 e2} (inSub: s ∈f e1) : s ∈f (e1 + e2)
| FVAddExprR {s e1 e2} (inSub: s ∈f e2) : s ∈f (e1 + e2)
| FVAbsExpr {f x τ body s} (notF : f <> s) (notX : x <> s) (inSub : s ∈f body) : s ∈f (AbsExpr f x τ body)
| FVAppExprL {s e1 e2} (inSub: s ∈f e1) : s ∈f (AppExpr e1 e2)
| FVAppExprR {s e1 e2} (inSub: s ∈f e2) : s ∈f (AppExpr e1 e2)
where "s ∈f e" := (InFV s e) : FV_scope.

Open Scope FV_scope.

Lemma InFVExclusive {s e} : s ∈f e -> s ∉f e -> False.
  induction e.
  all: intros ine notine; inversion ine; inversion notine; done.
Qed.

Lemma InFVOptions s e : s ∈f e \/ s ∉f e.
Proof with done.
  induction e.
  - destruct (string_dec s x)...
  - done.
  - decompose [or] IHe1; decompose [or] IHe2...
  - decompose [or] IHe; destruct (string_dec f s); destruct (string_dec x s)...
  - decompose [or] IHe1; decompose [or] IHe2...
Qed.

Inductive InBV : string -> 𝔼 -> Prop :=
| BVFName {f x τ body} : f ∈b (AbsExpr f x τ body)
| BVArg {f x τ body} : x ∈b (AbsExpr f x τ body)
| BVAddExprL {s e1 e2} (inSub: s ∈b e1) : s ∈b (e1 + e2)
| BVAddExprR {s e1 e2} (inSub: s ∈b e2) : s ∈b (e1 + e2)
| BVAppExprL {s e1 e2} (inSub: s ∈b e1) : s ∈b (AppExpr e1 e2)
| BVAppExprR {s e1 e2} (inSub: s ∈b e2) : s ∈b (AppExpr e1 e2)
where "x ∈b e" := (InBV x e).

Reserved Notation "[ a / s ] b = c" (at level 1, no associativity,
                                     a at next level, s at next level,
                                     b at next level, c at next level).

Inductive CAS : 𝔼 -> string -> 𝔼 -> 𝔼 -> Prop :=
| VarCASeq {s1 s2 e} (eq : s1 = s2) : [e / s1] s2 = e
| VarCASneq {s1 s2 e} (neq : s1 <> s2) : [e / s1] s2 = s2
| NatCAS {e s} (n : nat) : [e / s] n = n
| AddCAS {e s e1 e1' e2 e2'}
          (LeftAddCAS : [e / s] e1 = e1')
          (RightAddCAS : [e / s] e2 = e2')
  : [e / s] (e1 + e2) = (e1' + e2')
| AppCAS {e s e1 e1' e2 e2'}
          (LeftAppCAS : [e / s] e1 = e1')
          (RightAppCAS : [e / s] e2 = e2')
  : [e / s] (AppExpr e1 e2) = (AppExpr e1' e2')
| AbsCASUnbound {e s f x τ body body'}
                (notF : s <> f)
                (notX : s <> x)
                (fNotIn : f ∉f e)
                (xNotIn : x ∉f e)
                (bodyCAS : [e / s] body = body')
  : [e / s] (AbsExpr f x τ body) = (AbsExpr f x τ body')
| AbsCASF {e f x τ body} : [e / f] (AbsExpr f x τ body) = (AbsExpr f x τ body)
| AbsCASX {e f x τ body} : [e / x] (AbsExpr f x τ body) = (AbsExpr f x τ body)
where "[ a / s ] b = c" := (CAS a s b c).

Inductive SafeToSubInto (e : 𝔼) : 𝔼 -> Prop :=
| SafeToSubIntoVarExpr {s : string} : SafeToSubInto e s
| SafeToSubIntoNatExpr {n : nat} : SafeToSubInto e n
| SafeToSubIntoAddExpr (e0 e1 : 𝔼)
                       (safe1 : SafeToSubInto e e0)
                       (safe2 : SafeToSubInto e e1)
  : SafeToSubInto e (e0 + e1)
| SafeToSubIntoAppExpr (e0 e1 : 𝔼)
                       (safe1 : SafeToSubInto e e0)
                       (safe2 : SafeToSubInto e e1)
  : SafeToSubInto e (AppExpr e0 e1)
| SafeToSubIntoAbExpr {f x τ body}
                      (notFIn : f ∉f e)
                      (notXIn : x ∉f e)
                      (safe : SafeToSubInto e body)
  : SafeToSubInto e (AbsExpr f x τ body).

Axiom AlwaysSafeToSubInto : forall e1 e2, SafeToSubInto e1 e2.

Lemma CASAlways {e1 x e} : SafeToSubInto e1 e -> exists e2, [e1 / x] e = e2.
  intros H.
  induction e.
  - destruct (string_dec x x0) as [-> | neq].
    + exists e1; done.
    + exists x0; done.
  - exists n; done.
  - inversion H.
    destruct (IHe1 safe1).
    destruct (IHe2 safe2).
    exists (AddExpr x0 x1).
    done.
  - inversion H.
    destruct (IHe safe).
    destruct (string_dec x f) as [-> | nef].
    + exists (AbsExpr f x0 τ e).
      done.
    + destruct (string_dec x x0) as [-> | nex0].
      * exists (AbsExpr f x0 τ e).
        done.
      * exists (AbsExpr f x0 τ x2).
        done.
  - inversion H.
    destruct (IHe1 safe1).
    destruct (IHe2 safe2).
    exists (AppExpr x0 x1).
    done.
Qed.

Definition substitution_list := list (𝔼 * string).

Definition sub_dec (sub1 sub2 : (𝔼 * string)) : ({sub1 = sub2} + {sub1 <> sub2}).
Proof.
  decide equality.
  - apply string_dec.
  - decide equality.
    + apply string_dec.
    + decide equality.
    + decide equality.
    + apply string_dec.
    + apply string_dec.
Qed.

Inductive MultiCAS : substitution_list -> 𝔼 -> 𝔼 -> Prop :=
| MultiCASNull {e} : MultiCAS nil e e
| MultiCASCons {e s subs e' e'' e'''}
                (MultiCASe'' : (MultiCAS subs e' e''))
                (CASe' : (CAS e s e'' e'''))
  : MultiCAS ((e,s)::subs) e' e'''.

Reserved Notation "a '≡α' b" (at level 1, no associativity).

Inductive AlphaEquiv : 𝔼 -> 𝔼 -> Prop :=
| RAE {e} : e ≡α e 
| AAE {a b c d}
      (AEQac : a ≡α c)
      (AEQbd : b ≡α d)
  : (a + b) ≡α (c + d)
| PAE {a b c d}
      (AEQac : a ≡α c)
      (AEQbd : b ≡α d)
  : (AppExpr a b) ≡α (AppExpr c d)
| BAE {f f1 f2 x x1 x2 τ body1 body1' body2 body2'}
      (FXDiff : f <> x)
      (FFresh1 : f ∉f body1)
      (FFresh2 : f ∉f body2)
      (XFresh1 : x ∉f body1)
      (XFresh2 : x ∉f body2)
      (FCAS1 : [f / f1] body1 = body1')
      (FCAS2 : [f / f2] body2 = body2')
      (AEQ12 : body1' ≡α body2')
  : (AbsExpr f1 x1 τ body1) ≡α (AbsExpr f2 x2 τ body2)
where "a ≡α b" := (AlphaEquiv a b).

Theorem AlphaEquivSymm {e1 e2} : e1 ≡α e2 -> e2 ≡α e1.
  induction 1; done.
Qed.
