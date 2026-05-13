import VersoSlides
import Verso.Doc.Concrete
import Lean4Lean.Theory.Typing.Strong

open VersoSlides

#doc (Slides) "Dependently-Typed Categorical Combinators" =>

# The Dependently-Typed Combinator Calculus

# Contribution

## Result ⟺ Practical Formalization Techniques

Formalizing a dependent type theory is challenging because *computations can appear in types*.


$$`\frac{\Gamma \vdash M : A \quad A =_{\beta} B \quad \Gamma \vdash B : K}{\Gamma \vdash M : B}`

In the _Calculus of Constructions_, if $`A` has type $`B` and $`C` is def-eq. ($`=_{\beta}`) $`B`, then $`A : C`.

# Definitional Equality is Complicated: Lean4Lean

%%%
vertical := some true
%%%

Lean4Lean is a formalization of Lean's metatheory in Lean. It defines definitional equality in a 67-line inductive:

```leanLibCode Lean4Lean.Theory.Typing.Strong (startLine := 16) (endLine := 84)
inductive IsDefEqStrong : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    u.WF uvars →
    [] ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | appDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ B : .sort v →
    A'::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B →
    A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF :
    u.WF uvars → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    u.WF uvars → v.WF uvars → Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ B.inst e' : .sort v →
    Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    A.lift::A::Γ ⊢ B.liftN 1 1 : .sort v →
    Γ ⊢ e : .forallE A B →
    A::Γ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) →
    A::Γ ⊢ A.lift : .sort u →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    u.WF uvars →
    [] ⊢ df.type.instL ls : .sort u →
    [] ⊢ df.lhs.instL ls : df.type.instL ls →
    [] ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls : df.type.instL ls →
    Γ ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls

```
