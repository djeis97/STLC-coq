From Coq Require Import ssreflect ssrfun ssrbool.
Require Import FunInd.
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
Reserved Notation "a '∉b' b" (at level 1, no associativity).

Inductive NotInFV : string -> 𝔼 -> Prop :=
| NotFVVarExpr {s1 s2} (neq : s1 <> s2) : s1 ∉f s2
| NotFVNatExpr {s} {n : nat} : s ∉f n
| NotFVAddExpr {s e1 e2} (notInLeft : s ∉f e1) (notInRight : s ∉f e2) : s ∉f (e1 + e2)
| NotFVAppExpr {s e1 e2} (notInLeft : s ∉f e1) (notInRight : s ∉f e2) : s ∉f (AppExpr e1 e2)
| NotFVAbsExpru f x τarg τret body {s} (notF : f <> s) (notX : x <> s) (notInBody : s ∉f body) :
    s ∉f (AbsExpr f x τarg τret body)
| NotFVAbsExprx f x τarg τret body : x ∉f (AbsExpr f x τarg τret body)
| NotFVAbsExprf f x τarg τret body : f ∉f (AbsExpr f x τarg τret body)
where "s ∉f e" := (NotInFV s e) : FV_scope.

Inductive InFV : string -> 𝔼 -> Prop :=
| FVVarExpr {s} : s ∈f s
| FVAddExprL {s e1 e2} (inSub: s ∈f e1) : s ∈f (e1 + e2)
| FVAddExprR {s e1 e2} (inSub: s ∈f e2) : s ∈f (e1 + e2)
| FVAbsExpr {f x τarg τret body s} (notF : f <> s) (notX : x <> s) (inSub : s ∈f body) :
    s ∈f (AbsExpr f x τarg τret body)
| FVAppExprL {s e1 e2} (inSub: s ∈f e1) : s ∈f (AppExpr e1 e2)
| FVAppExprR {s e1 e2} (inSub: s ∈f e2) : s ∈f (AppExpr e1 e2)
where "s ∈f e" := (InFV s e) : FV_scope.

Open Scope FV_scope.

Fixpoint InFVb string expr :=
  match expr with
  | VarExpr s => if (string_dec string s) then true else false
  | NatExpr _ => false
  | AddExpr e0 e1 => (InFVb string e0) || (InFVb string e1)
  | AppExpr e0 e1 => (InFVb string e0) || (InFVb string e1)
  | AbsExpr f x _ _ body => if (string_dec string f) then
                             false
                           else if (string_dec string x) then
                                  false
                                else (InFVb string body)
  end.

Functional Scheme InFVb_ind
  := Induction for InFVb Sort Set.

Lemma InFVPn {s e} : reflect s ∉f e (~~ InFVb s e).
  apply/(iffP idP); functional induction (InFVb s e);
    elim_sumbools string_dec => //=; by [move/norP | inversion 1 => //=; apply/norP].
Qed.

Lemma InFVP {s e} : reflect s ∈f e (InFVb s e).
  apply/(iffP idP); functional induction (InFVb s e);
    elim_sumbools string_dec => //=; by [move/orP => [|] | inversion 1 => //=; apply/orP].
Qed.

Lemma InFVExclusive {s e} : s ∈f e -> s ∉f e -> False.
  by move => /InFVP ? /InFVPn/negP.
Qed.

Lemma InFVOptions s e : s ∈f e \/ s ∉f e.
  case E: (InFVb s e); by [move/InFVP: E | move/InFVPn: E].
Qed.

Inductive InBV : string -> 𝔼 -> Prop :=
| BVFName {f x τarg τret body} : f ∈b (AbsExpr f x τarg τret body)
| BVArg {f x τarg τret body} : x ∈b (AbsExpr f x τarg τret body)
| BVBody {s f x τarg τret body} (inSub: s ∈b body) : s ∈b (AbsExpr f x τarg τret body)
| BVAddExprL {s e1 e2} (inSub: s ∈b e1) : s ∈b (e1 + e2)
| BVAddExprR {s e1 e2} (inSub: s ∈b e2) : s ∈b (e1 + e2)
| BVAppExprL {s e1 e2} (inSub: s ∈b e1) : s ∈b (AppExpr e1 e2)
| BVAppExprR {s e1 e2} (inSub: s ∈b e2) : s ∈b (AppExpr e1 e2)
where "x ∈b e" := (InBV x e).

Inductive NotInBV s : 𝔼 -> Prop :=
| NotBVAbsExpr {f x τarg τret body} (notF : s <> f) (notX : s <> x) (notSub : s ∉b body)
  : s ∉b (AbsExpr f x τarg τret body)
| NotBVAddExpr {e1 e2} (nsub1 : s ∉b e1) (nsub2: s ∉b e2)
  : s ∉b (AddExpr e1 e2)
| NotBVAppExpr {e1 e2} (nsub1 : s ∉b e1) (nsub2: s ∉b e2)
  : s ∉b (AppExpr e1 e2)
| NotBVNatExpr (n : nat) : s ∉b n
| NotBVVarExpr (s0 : string) : s ∉b s0
where "s ∉b e" := (NotInBV s e).

Fixpoint InBVb s e :=
  match e with
  | VarExpr s => false
  | NatExpr n => false
  | AddExpr l r => (InBVb s l)||(InBVb s r)
  | AppExpr l r => (InBVb s l)||(InBVb s r)
  | AbsExpr f x τarg τret body =>
    if (string_dec s f) then true
    else if (string_dec s x) then true
         else (InBVb s body)
  end.

Functional Scheme InBVb_ind
  := Induction for InBVb Sort Set.

Lemma InBVPn s e : reflect (s ∉b e) (~~ InBVb s e).
  apply/(iffP idP); functional induction (InBVb s e);
    elim_sumbools string_dec => //=; by [move/norP | inversion 1 => //=; apply/norP].
Qed.

Lemma InBVP s e : reflect (s ∈b e) (InBVb s e).
  apply/(iffP idP); functional induction (InBVb s e);
    elim_sumbools string_dec => //=; by [move/orP => [|] | inversion 1 => //=; apply/orP].
Qed.

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
| AbsCASUnbound {e s f x τarg τret body body'}
                (notF : s <> f)
                (notX : s <> x)
                (fNotIn : f ∉f e)
                (xNotIn : x ∉f e)
                (bodyCAS : [e / s] body = body')
  : [e / s] (AbsExpr f x τarg τret body) = (AbsExpr f x τarg τret body')
| AbsCASF {e f x τarg τret body} : [e / f] (AbsExpr f x τarg τret body) = (AbsExpr f x τarg τret body)
| AbsCASX {e f x τarg τret body} : [e / x] (AbsExpr f x τarg τret body) = (AbsExpr f x τarg τret body)
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
| SafeToSubIntoAbExpr {f x τarg τret body}
                      (notFIn : f ∉f e)
                      (notXIn : x ∉f e)
                      (safe : SafeToSubInto e body)
  : SafeToSubInto e (AbsExpr f x τarg τret body).

Axiom AlwaysSafeToSubInto : forall e1 e2, SafeToSubInto e1 e2.

Lemma CASAlways {e1 x e} : SafeToSubInto e1 e -> exists e2, [e1 / x] e = e2.
  elim.
  - move=> x0; case: (string_dec x x0) => [-> | neq].
    + exists e1 => //.
    + exists x0 => //.
  - move=> n; exists n => //.
  - move=> e0 e2 ? [x0 ?] ? [x1 ?]; exists (AddExpr x0 x1) => //.
  - move=> e0 e2 ? [x0 ?] ? [x1 ?]; exists (AppExpr x0 x1) => //.
  - move=> f x0 τarg τret body fni x0ni safe [x2 ?].
    case: (string_dec x f) => [-> | nef].
    + exists (AbsExpr f x0 τarg τret body) => //.
    + case: (string_dec x x0) => [-> | nex0].
      * exists (AbsExpr f x0 τarg τret body) => //.
      * exists (AbsExpr f x0 τarg τret x2) => //.
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
| BAE {f f1 f2 x x1 x2 τarg τret body1 body1' body2 body2'}
      (FXDiff : f <> x)
      (FFresh1 : f ∉f body1)
      (FFresh2 : f ∉f body2)
      (XFresh1 : x ∉f body1)
      (XFresh2 : x ∉f body2)
      (FCAS1 : [f / f1] body1 = body1')
      (FCAS2 : [f / f2] body2 = body2')
      (AEQ12 : body1' ≡α body2')
  : (AbsExpr f1 x1 τarg τret body1) ≡α (AbsExpr f2 x2 τarg τret body2)
where "a ≡α b" := (AlphaEquiv a b).

Theorem AlphaEquivSymm {e1 e2} : e1 ≡α e2 -> e2 ≡α e1.
  elim => //.
Qed.
