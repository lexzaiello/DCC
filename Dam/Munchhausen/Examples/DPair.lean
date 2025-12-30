import Dam.Munchhausen.Defs

/-
P 10:6 Altenkirch. Dependent pairs.
-/

abbrev DPair.choose.{u} (A : Type u) (B : A → Type u) (h : A) (b : Bool) : Type u := if b then A else B h

structure DPair.{u} (A : Type u) (B : A → Type u) where
  h   : A
  f   : ∀ (b : Bool), if b then A else B h
  heq : h = f true

namespace DPair

def mk'.{u} (A : Type u) (B : A → Type u) (a : A) (b : B a) : DPair.{u} A B where
  h := a
  f := fun x => match x with
  | true => a
  | false => b
  heq := rfl

instance instVeryDependent.{u} (A : Type u) (B : A → Type u) (e : DPair A B) : VeryDependent A B where
  a := e.h
  x := e.f false
  α o _ := o
  heq := rfl

def equivSigma.toFun.{u} (A : Type u) (B : A → Type u) : Sigma B → DPair A B := Sigma.uncurry (mk' A B)

def equivSigma.invFun.{u} (A : Type u) (B : A → Type u) (e : DPair A B) : Sigma B := ⟨e.h, e.f false⟩

instance equivSigma.{u} (A : Type u) (B : A → Type u) : Sigma B ≃ DPair A B where
  toFun := equivSigma.toFun A B
  invFun := equivSigma.invFun A B
  right_inv e := match e with
    | .mk h f heq => by
      simp only [equivSigma.toFun, equivSigma.invFun, Sigma.uncurry, mk', mk.injEq, heq_eq_eq, true_and]
      funext
      split
      exact heq
      rfl

end DPair
