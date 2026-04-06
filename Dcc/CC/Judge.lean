import Dcc.CC.Ast
import Dcc.CC.Step2

/-
Π using couples - significantly more annoying. don't do.
-/

def arrow (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(m, n) α `(Sort n, Σ(Sort m, Id(Sort m)), β))

def Pi.type (m n : Level) : Expr :=
  arrow (DCC Sort m)
    (arrow
      (arrow
        (DCC (Σ(Sort m, Id(Sort m))))
        (DCC Sort n) m.succ n.succ)
      (DCC Sort n) n.succ n.succ) m.succ n.succ

def Pi.type₁ (m n : Level) : Expr :=
  arrow
    (arrow
      (DCC (Σ(Sort m, Id(Sort m))))
        (DCC Sort n) m.succ n.succ)
      (DCC Sort n) n.succ n.succ

def id.type (α : Expr) (m : Level) : Expr :=
  arrow α α m m

def comp.type (α γ g : Expr) (m o : Level) : Expr :=
  DCC (Π(m, o) α (γ ∘ g))

def pair.type (α β τ₁ : Expr) (m n o : Level) : Expr :=
  (arrow α (DCC Σ(τ₁, β)) m (max n o))

def fst.type (α β : Expr) (m n : Level) : Expr :=
  (arrow (DCC Σ(α, β)) α (max m n) m)

def snd.type (α β : Expr) (m n : Level) : Expr :=
  (DCC (Π(max m n, n)
    Σ(α, β) (β ∘ Fst(α, β) ∘ Snd(Sort (max m n), Id(Sort (max m n))))))

def app_e.type (β γ : Expr) (n o : Level) : Expr :=
  DCC (Π(max o n, o)
      Σ((Π(n, o) β γ), `(Sort n, (Π(n, o) β γ), β))
      (γ ∘ (Snd((Π(n, o) β γ), `(Sort n, (Π(n, o) β γ), β)) ∘ Snd(Sort (max o n), Id(Sort (max o n))))))

/-
x : Π (Σ α β) γ
Λ(x) : Π(m, o) α ((Flip(Π(n, o)) γ) ∘ β)
-/
def curr.type (α β γ : Expr) (m n o : Level) : Expr :=
  (DCC (Π(m, o) α ((Flip(Π(n, o)) γ) ∘ β)))

def coup.type (α β : Expr) : Expr :=
  (DCC Σ(α, β))

def quot.type (α β : Expr) (n m : Level) : Expr :=
  (arrow α (arrow β α n m) m m)

namespace Expr

inductive Judge : Expr → Expr → Prop
  | id    : Judge α (DCC (Sort m))
    → Judge (DCC Id(α)) (id.type α m)
  -- g : Π β A
  | comp  : Judge g (arrow α β m n)
    → Judge f (DCC (Π(n, o) β γ))
    → Judge (DCC f ∘ g) (comp.type α γ g m o)
  -- f  : α → τ₁
  -- α  : Sort m
  -- τ₁ : Sort n
  -- β : τ₁ → Sort o
  -- g : DCC (Π(m, o) α (β ∘ f ∘ Snd(Sort m, Id(Sort m))))
  -- β :
  -- ⟦β⟧⟨a, b⟩ : α → (Σ τ₁ β)
  -- this is essentially substitution in the category of contexts
  -- y₀ : B₀, y₁ : B₁(y₀)
  | pair  : Judge β (arrow τ₁ (DCC Sort o) n o.succ)
    → Judge f (arrow α τ₁ m n)
    → Judge g (DCC (Π(m, o) α (β ∘ f ∘ Snd(Sort m, Id(Sort m)))))
    → Judge (DCC ⟦β⟧⟨f, g⟩) (pair.type α β τ₁ m n o)
  -- fst(α, β) : (Σ α β) → α
  | fst   : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Fst(α, β)) (fst.type α β m n)
  /- snd(α, β) : 
  -/
  | snd   : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Snd(α, β)) (snd.type α β m n)
  /-
    App f x types are nondependent.
    At least, x does not depend on x. need to bake that into ⟦β⟧
    x : Π(max m n, o) (Σ α, β) γ
    γ : (Σ α, β) → Sort o
    γ : arrow (DCC (Σ(m, n) α β)) (DCC Sort o) (max m n) o.succ
    (Π(m, o) α 
      (App(Pi.type₁ n o, arrow (`(#(Pi.type₁ n o), arrow (DCC (Σ(m, n) α β)) (DCC Sort o) (max m n) o.succ))) ∘
        ⟦`(#(Pi.type₁ n o), arrow (DCC (Σ(m, n) α β)) (DCC Sort o) (max m n) o.succ)⟧⟨Π(n, o) ∘ β ∘ Snd(Sort m, Id(Sort m)), `((Σ(m.succ, m) (Sort m) Id(Sort m)), γ)⟩))
    Λ(x) : Π(m, o) α (
      App(?, ?)
        ∘ ⟦`(#(arrow (DCC Sort o), Sort o)⟧⟨Π(n, o) ∘ (β ∘ Snd(Sort m, Id(Sort m))), `((Σ(m.succ, m) (Sort m) (Id(Sort m))), γ)⟩
      β ∘ Snd(Sort m, Id(Sort m))
  -/
  | curr  : Judge x (DCC (Π(max m n, o) Σ(α, β) γ))
    → Judge (DCC Λ(β, x)) (curr.type α β γ m n o)
  /-
    App(γ, β) : (Π(max o n, o)
      (Σ(o, n) (Π(n, o) β γ) `((Π(n, o) β γ), β))
      (γ ∘ (Snd((Π(n, o) β γ), `((Π(n, o) β γ), β)) ∘ Snd(Sort (max o n), Id(Sort (max o n))))))
  -/
  | app_e : Judge β (DCC Sort n)
    → Judge γ (arrow β (DCC (Sort o)) n o.succ)
    → Judge (DCC App(γ, β)) (app_e.type β γ n o)
  /-
    a : α
    b : β a
    ⟦β⟧(a, b) : Σ α β
  -/
  | coup  : Judge a α
    → Judge b (DCC (β a))
    → Judge (DCC ⟦β⟧(a, b)) (coup.type α β)
  -- Can derive dependent quotation
  | quot  : Judge α (DCC Sort m)
    → Judge β (DCC Sort m)
    → Judge x α
    → Judge (DCC `(α, β, x)) (arrow α (arrow β α n m) m m)
  | app   : Judge f (DCC (Π(m, n) α β)) → Judge x α
    → Judge (DCC (f x)) (DCC (β ⟦Id(Sort m)⟧(α, x)))
  | sort  : Judge (DCC Sort m) (DCC Sort m.succ)
  | conv  : Judge x A → (∃ C, RedAffReflTrans A C ∧ RedAffReflTrans B C) → Judge x B

/-def infer (e : Expr) : Option ((t : Expr) × PLift (Judge e t)) := do
  match e with
  | DCC Sort m => return ⟨DCC Sort m.succ, ⟨.sort⟩⟩
  | DCC Id(α)  => match ← α.infer with
    | ⟨DCC Sort m, ⟨h⟩⟩ => return ⟨id.type α m, ⟨.id h⟩⟩
    | _ => .none
  | DCC f ∘ g => match ← g.infer, ← f.infer with
    | ⟨DCC (Π(m, n₁) α `(Sort n₂, Σ(Sort m₂, Id(Sort m₃)), β)), ⟨h₁⟩⟩, ⟨DCC (Π(n₃, o) β₂ γ), ⟨h₂⟩⟩ =>
      if heq₁ : m = m₂ ∧ m = m₃ ∧ n₁ = n₂ ∧ n₁ = n₃ ∧ β = β₂ then
      by
        have ⟨heq₁, heq₂, heq₃, heq₄, heq₅⟩ := heq₁
        simp [← heq₁, ← heq₂, ← heq₃, ← heq₄, ← heq₅] at *
        exact .some ⟨comp.type α γ g m o, ⟨.comp h₁ h₂⟩⟩
      else
        .none
    | _, _ => .none-/

end Expr
