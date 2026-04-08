import Dcc.CC.Ast
import Dcc.CC.Step2

/-
need to make Σ point-free.

Σ(m, n) : (Π(m.succ, (max m n).succ)
  (Sort m)
  ((Flip(Π(n.succ, (max m n).succ)) (Sort (max m n))) ∘ ((Flip(Π(m, n.succ)) (Sort n)) ∘ Snd(Sort m, Id(Sort m)))))

id(α) : Π(m, m) α (

this all seems to suggest γ receives

(?, f x)
^ can put dependent type here

assuming we had more point-free things:

Fst(m, n) : Π(m, m) (Sort m) (Flip(Π(m, n.succ)) ∘ Fst(Sort m, Id(Sort m))

Fst(m, n) : ∀ (α : Type) (β : α → Type) (x : Σ(α, β)), α

question 2:

does pair need to be dependent at all? can we derive dependent type with couples / sigma?

very important question: is it even possible to derive dependent Fst, for example?

Fst'(m, n) : ∀ (α : Sort m) (β : α → Sort n) (x : Σ(α, β)), α

Fst'(m, n) :=
  -- ⟦snd_β⟧(α, β)
  -- snd_β : Sort m → Sort n.succ
  -- snd_β := fun α => α → Sort n
  -- this dictates the type of snd received by Λ(...) α β with (α, β)
  -- results in: ∀ (α : Sort m) (β : α → Sort n) ....
  let snd_β := (Flip(Π(m, n.succ)) (Sort n))

  let π₁_α_β := Fst(Sort m, snd_β)
  let π₂_α_β := Snd(Sort m, snd_β)

  -- take ⟦snd_β⟧(α, β), and make Σ(m, n) α β
  -- my_γ computes the type of π₂_α_β, which is just (α → Sort n), but we need α to do that
  let mk_t_sigma := ⟦(Σ(m.succ, n.succ) (Sort m) snd_β), my_γ⟧⟨Σ(m, n) ∘ π₁_α_β, π₂_α_β⟩

  Λ(snd_β, )

⟨f, g⟩

f : ∀ (x : α) (y : β x), γ x y
g : ∀ (x : α), β x

f : α → β
⟨f, g⟩ : α → ⟦`(Sort n,

⟦β, `(Sort o, Σ(
γ : Σ(Sort n, Id(Sort n))

g : ∀ (x : α), γ
g x : γ (β, (f x))

⟦α, β, γ⟧⟨,⟩ : ∀ (f : ∀ (x : α), β x) (g : ∀ (x : α), γ (f x))
-/

def arrow (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(m, n) α `(Sort n, (Σ(m.succ, m) (Sort m) (Id(Sort m))), β))

def Pi.type (m n : Level) : Expr :=
  arrow (DCC Sort m)
    (arrow
      (arrow
        (DCC (Σ(m.succ, m) (Sort m) Id(Sort m)))
        (DCC Sort n) m.succ n.succ)
      (DCC Sort n) n.succ n.succ) m.succ n.succ


/-
Σ α β : Sort (max m n)
-/
def Sigma.type (m n : Level) : Expr :=
  DCC ((Π(m.succ, (max m n).succ)
         (Sort m)
        ((Flip(Π(n.succ, (max m n).succ)) `(Sort (max m n).succ, (Σ(n.succ.succ, n.succ) (Sort n.succ) Id(Sort n.succ)), Sort (max m n)))
          ∘ ((Flip(Π(m, n.succ)) `(Sort n.succ, (Σ(m.succ, m) (Sort m) Id(Sort m)), Sort n)) ∘ Snd(Sort m, Id(Sort m))))))

def id.type (α : Expr) (m : Level) : Expr :=
  arrow α α m m

def flip.type (α β γ : Expr) (m n o : Level) : Expr :=
  (arrow β (arrow α γ m o) n o).reduce.fst

def comp.type (α γ g : Expr) (m o : Level) : Expr :=
  DCC (Π(m, o) α (γ ∘ g))

/-
⟦α, γ⟧⟨f, x⟩ : Π(m, (max n o)) α (() ∘ f
-/

def pair.type (α β γ : Expr) (m n o : Level) : Expr :=
  (DCC (Π(m, (max n o)) α ((Flip(Σ(n, o)) γ) ∘ β)))

def fst.type (α β : Expr) (m n : Level) : Expr :=
  (arrow (DCC (Σ(m, n) α β)) α (max m n) m)

def snd.type (α β : Expr) (m n : Level) : Expr :=
  (DCC (Π(max m n, n)
    (Σ(m, n) α β) (β ∘ Fst(α, β) ∘ Snd(Sort (max m n), Id(Sort (max m n))))))

def app_e.type (β γ : Expr) (n o : Level) : Expr :=
  DCC (Π(max o n, o)
      (Σ(o, n) (Π(n, o) β γ) `(Sort n, (Π(n, o) β γ), β))
      (γ ∘ (Snd((Π(n, o) β γ), `(Sort n, (Π(n, o) β γ), β)) ∘ Snd(Sort (max o n), Id(Sort (max o n))))))

/-
x : Π (Σ α β) γ
Λ(x) : Π(m, o) α ((Flip(Π(n, o)) γ) ∘ β)
-/
def curr.type (α β γ : Expr) (m n o : Level) : Expr :=
  (DCC (Π(m, o) α ((Flip(Π(n, o)) γ) ∘ β)))

def coup.type (α β : Expr) (m n : Level) : Expr :=
  (DCC (Σ(m, n) α β))

def quot.type (α β : Expr) (m n : Level) : Expr :=
  (arrow β α n m)

namespace Expr

inductive Judge : Expr → Expr → Type where
  | id    : Judge α (DCC (Sort m))
    → Judge (DCC Id(α)) (id.type α m).reduce.fst
  /-
    (α, y)
    x : (Π(m, o) α ((Flip(Π(n, o)) γ) ∘ β)))
    (DCC (Π(m, o) α ((Flip(Π(n, o)) γ) ∘ β)))
    Flip(x)
  -/
  | flip  : Judge x (arrow α (arrow β γ n o) m o)
    → Judge (DCC Flip(x)) (flip.type α β γ n n o)
  -- g : Π β A
  | comp  : Judge g (arrow α β m n)
    → Judge f (DCC (Π(n, o) β γ))
    → Judge (DCC f ∘ g) (comp.type α γ g m o).reduce.fst
  /-
    ⟦m, α, γ⟧⟨f, g⟩ x = ⟦(γ ⟦Id(Sort m)⟧(α, x))⟧(f x, g x)
    f : ∀ (x : α), β x
    g : ∀ (x : α), γ ∘ f
    γ : ∀ (x : (Σ(m.succ, m) (Sort m) Id(Sort m))), (β ∘ Snd((Sort m), Id(Sort m))) → Sort o

    ⟦m, α, γ⟧⟨f, g⟩ x : (Σ(n, o) (β x) γ)
  -/
  | pair  : Judge f (DCC (Π(m, n) α β))
    → Judge g (DCC  (Π(m, o) α (γ ∘ f)))
    → Judge γ (DCC (
      Π(m.succ, o.succ)
       (Σ(m.succ, m) (Sort m) Id(Sort m))
       ((Flip(Π(n, o.succ)) (Sort o)) ∘ (β ∘ Snd((Sort m), Id(Sort m))))))
    → Judge (DCC ⟦m, α, γ⟧⟨f, g⟩) (pair.type α β γ m n o).reduce.fst
  -- fst(α, β) : (Σ α β) → α
  | fst   : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Fst(α, β)) (fst.type α β m n).reduce.fst
  /- snd(α, β) : 
  -/
  | snd   : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Snd(α, β)) (snd.type α β m n).reduce.fst
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
  | curr  : Judge x (DCC (Π(max m n, o) (Σ(m, n) α β) γ))
    → Judge (DCC Λ(β, x)) (curr.type α β γ m n o).reduce.fst
  /-
    App(γ, β) : (Π(max o n, o)
      (Σ(o, n) (Π(n, o) β γ) `((Π(n, o) β γ), β))
      (γ ∘ (Snd((Π(n, o) β γ), `((Π(n, o) β γ), β)) ∘ Snd(Sort (max o n), Id(Sort (max o n))))))
  -/
  | app_e : Judge β (DCC Sort n)
    → Judge γ (arrow β (DCC (Sort o)) n o.succ)
    → Judge (DCC App(γ, β)) (app_e.type β γ n o).reduce.fst
  /-
    a : α
    b : β a
    ⟦β⟧(a, b) : Σ α β
  -/
  | coup  : Judge β (arrow α (DCC (Sort n)) m n.succ)
    → Judge a α
    → Judge b (DCC (β a)).reduce.fst
    → Judge (DCC ⟦β⟧(a, b)) (coup.type α β m n).reduce.fst
  -- Can derive dependent quotation
  | quot  : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Judge x α
    → Judge (DCC `(α, β, x)) (quot.type α β m n).reduce.fst
  | pi    : Judge (DCC Π(m, n)) (Pi.type m n)
  | sigma : Judge (DCC Σ(m, n)) (Sigma.type m n)
  | app   : Judge f (DCC (Π(m, n) α β))
    → Judge x α
    → Judge (DCC (f x)) (DCC (β ⟦Id(Sort m)⟧(α, x))).reduce.fst
  | sort  : Judge (DCC Sort m) (DCC Sort m.succ)
deriving Repr

instance : Std.ToFormat (Judge A B) := ⟨repr⟩

def match_arrow (t : Expr) : Option ((α β : Expr) × (m n : ℕ) × (PLift (t = arrow α β m n))) :=
  match t with
  | DCC (Π(m₁, n₁) α `(Sort n₂, (Σ(m₃, m₄) (Sort m₂) (Id(Sort m₅))), β)) =>
    if heq : m₁ = m₂ ∧ m₁.succ = m₃ ∧ n₁ = n₂ ∧ m₃ = m₁.succ ∧ m₁ = m₄ ∧ m₁ = m₅ then
      .some ⟨α, β, m₁, n₁, ⟨by have ⟨ha, hb, hc, hd, he, hf⟩ := heq; rw [← ha, ← hb, ← hc, ← he, ← hf]; rfl⟩⟩
    else
      .none
  | _ => .none

def infer (e : Expr) : Option ((t : Expr) × (Judge e t)) := do
  match e with
  | DCC Π(m, n) => .some ⟨_, .pi⟩
  | DCC Σ(m, n) => .some ⟨_, .sigma⟩
  | DCC ⟦β⟧(a, b) =>
    let ⟨t_β, h_t_β⟩ ← β.infer
    match ← t_β.match_arrow with
    | ⟨α, DCC Sort n, m, n₂, ⟨heq₀⟩⟩ =>
      let ⟨α₂, h_t_a⟩  ← a.infer
      let ⟨t_b, h_t_b⟩ ← b.infer
      if heq₂ : α = α₂ then
        if heq₃ : t_b = (DCC (β a)).reduce.fst then
          if heq₄ : n₂ = n.succ then
            .some ⟨_, .coup (heq₄ ▸ (heq₀ ▸ h_t_β)) (heq₂ ▸ h_t_a) (heq₃ ▸ h_t_b)⟩
          else .none
        else .none
      else .none
    | _ => .none
  | DCC Sort m => .some ⟨DCC Sort m.succ, .sort⟩
  | DCC `(α, β, x) =>
    let ⟨t_x, h_t_x⟩ ← x.infer
    match ← α.infer, ← β.infer with
    | ⟨DCC Sort m, h_t_α⟩, ⟨DCC Sort n, h_t_β⟩ =>
      if heq : t_x = α then
        .some ⟨_, .quot h_t_α h_t_β (heq ▸ h_t_x)⟩
      else .none
    | _, _ => .none
  | DCC Id(α)  => match ← α.infer with
    | ⟨DCC Sort m, h⟩ => return ⟨(id.type α m).reduce.fst, .id h⟩
    | _ => .none
  | DCC Fst(α, β) => match ← infer α with
    | ⟨DCC Sort m, h_t_α⟩ =>
      let ⟨t_β, h_t_β⟩ ← infer β
      match ← t_β.match_arrow with
      | ⟨α₁, DCC Sort n, m₁, n₁, ⟨heq₁⟩⟩ =>
        if heq : α = α₁ ∧ n.succ = n₁ ∧ m = m₁ then
          have ⟨heqa, heqb, heqc⟩ := heq
          .some ⟨_, .fst h_t_α (by rw [heq₁, ← heqa, ← heqb, ← heqc] at h_t_β; exact h_t_β)⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Snd(α, β) => match ← infer α with
    | ⟨DCC Sort m, h_t_α⟩ =>
      let ⟨t_β, h_t_β⟩ ← infer β
      match ← t_β.match_arrow with
      | ⟨α₁, DCC Sort n, m₁, n₁, ⟨heq₁⟩⟩ =>
        if heq : α = α₁ ∧ n.succ = n₁ ∧ m = m₁ then
          have ⟨heqa, heqb, heqc⟩ := heq
          .some ⟨_, .snd h_t_α (by rw [heq₁, ← heqa, ← heqb, ← heqc] at h_t_β; exact h_t_β)⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Flip(x) =>
    let ⟨t_x, h_t_x⟩ ← x.infer
    match ← t_x.match_arrow with
    | ⟨α, βγ, m, o, ⟨heq⟩⟩ =>
      match ← βγ.match_arrow with
      | ⟨β, γ, n, o₂, ⟨heq₂⟩⟩ =>
        if heq₃ : o = o₂ then
          .some ⟨_, .flip (by rw [heq, heq₂, ← heq₃] at h_t_x; exact h_t_x)⟩
        else .none
  | DCC App(γ, β) =>
    let ⟨t_γ, h_t_γ⟩ ← γ.infer
    match ← β.infer with
    | ⟨DCC Sort n, h_t_β⟩ =>
      match ← t_γ.match_arrow with
      | ⟨β₂, DCC Sort o, n₂, o₂, ⟨heq₂⟩⟩ =>
        if heq : β = β₂ ∧ n = n₂ ∧ o.succ = o₂ then
          have ⟨ha, hb, hc⟩ := heq
          .some ⟨_, .app_e h_t_β (by rw [heq₂, ← ha, ← hb, ← hc] at h_t_γ; exact h_t_γ)⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Λ(β, x) =>
    let ⟨t_β, h_t_β⟩ ← β.infer
    match ← x.infer with
    | ⟨DCC (Π(mn, o) (Σ(m₂, n) α β₂) γ), h_t_x⟩ =>
      if heq : max m₂ n = mn ∧ β = β₂ then
        have ⟨ha, hb⟩ := heq
        .some ⟨_, .curr (by rw [← ha, ← hb] at h_t_x; exact h_t_x)⟩
      else .none
    | _ => .none
  | DCC ⟦m, α, γ⟧⟨f, g⟩ =>
    let ⟨t_γ, h_t_γ⟩ ← infer γ
    let ⟨t_f, h_t_f⟩ ← infer f
    let ⟨t_g, h_t_g⟩ ← infer g
    match t_f, t_g, t_γ with
    | (DCC (Π(m₁, n₁) α₁ β)),
      (DCC  (Π(m₂, o₂) α₂ (γ₂ ∘ f₂))),
      (DCC (Π(m₃, o₃ + 1)
       (Σ(m₄, m₅) (Sort m₆) Id(Sort m₇))
       ((Flip(Π(n₂, o₄ + 1)) (Sort o₅)) ∘ (β₂ ∘ Snd((Sort m₉), Id(Sort m10)))))) =>
      if heq₃ : m = m₁ ∧ m = m₂ ∧ m.succ = m₃ ∧ m.succ = m₄ ∧ m = m₅ ∧ m = m₆ ∧ m = m₇ ∧ m = m₉ ∧ m = m10
        ∧ n₁ = n₂ ∧ o₂ = o₃ ∧ o₂ = o₄ ∧ o₂ = o₅ ∧ β = β₂ ∧ α = α₁ ∧ α = α₂ ∧ γ = γ₂ ∧ f = f₂ then
        have ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := heq₃
        .some ⟨_, .pair
          (by rw [← h1, ← h15] at h_t_f; exact h_t_f)
          (by rw [← h2, ← h16, ← h17, ← h18] at h_t_g; exact h_t_g)
          (by rw [← h3, ← h11, ← h4, ← h5, ← h6, ← h7, ← h8, ← h9, ← h12, ← h14, ← h10, ← h13] at h_t_γ; simp at h_t_γ; exact h_t_γ)⟩
      else .none
    | _, _, _ => .none
  | DCC f ∘ g =>
    let ⟨t_g, h_t_g⟩ ← g.infer
    let ⟨t_f, h_t_f⟩ ← f.infer
    match t_g.match_arrow, t_f.match_arrow with
    | .some ⟨α, β₁, m, n₁, ⟨heq₁⟩⟩, .some ⟨β₂, γ, n₂, o, ⟨heq₂⟩⟩ =>
      if heq₃ : β₁ = β₂ ∧ n₁ = n₂ then
        .some ⟨_, .comp (heq₁ ▸ h_t_g) (by
          have ⟨heqa, heqb⟩ := heq₃
          rw [← heqa, ← heqb] at heq₂
          rw [heq₂] at h_t_f
          exact h_t_f)⟩
      else .none
    | _, _ => .none
  | DCC (f x) => match ← f.infer, ← x.infer with
    | ⟨DCC (Π(m, n) α₁ β), h_f⟩, ⟨α₂, h_x⟩ =>
      if heq : α₁ = α₂ then
        .some ⟨(DCC (β ⟦Id(Sort m)⟧(α₁, x))).reduce.fst, .app h_f (heq ▸ h_x)⟩
      else .none
    | _, _ => .none

#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Id(Sort 1) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (⟦Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Fst(Sort 2, Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Snd(Sort 2, Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Σ(2, 1) (Sort 1) Id(Sort 1)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Π(1, 1) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC Id(Sort 1))
#eval (Std.format ∘ Sigma.fst) <$> infer (id.type (DCC Sort 0) 1)
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (`(Sort 1, Sort 1, Sort 0) (Sort 0)))
#eval infer (DCC (`(Sort 1, Sort 2, Sort 0) ∘ Id(Sort 2)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC ⟦3, Sort 2, Id(Sort 2)⟧⟨Id(Sort 2), Id(Sort 2) ∘ Id(Sort 2)⟩)
#eval infer (pair.type (DCC Sort 1) (DCC Id(Sort 1)) (DCC (Sort 1)) 2 2 2)

/-
example: deriving nondependent pair rule:

⟨a, b⟩ x = (a x, b x) : Σ α (`(Sort n, α, β))

⟦`(Sort 2, Sort 1, Sort 1)⟧⟨Id(Sort 1), Id(Sort 1)⟩

can just change g here...

⟦`(Sort 2, Sort 1, Sort 1)⟧⟨Id(Sort 1), Id(Sort 1)⟩

g receives Sort 0

we need g's type to be
β ∘ f ∘ Snd(_, _)

what's an example of App?

example: deriving S combinator

S x y z = (x z) (y z)

S = App ∘ ⟨x, App ∘ y⟩

S : ∀ (α : Type)
  (β : α → Type)
  (γ : ∀ (x : α) (y : β x), Type)
  (x : ∀ (x : α) (y : β x), γ x y)
  (y : ∀ (x : α), β x)
  (z : α), γ z (y z)

f : ∀ (x : α), β x

App(α, β) : ∀ (x : Σ(∀ (x : α), β x, β)), 
App(α, β) (f, x) = f x

assuming

App(β, γ) : (x : Σ((Π(?, ?) β γ), `(Sort n, Π(?, ?) β γ, β))), γ x.snd

S(α, β, γ) = App(γ, β) ∘ ⟨x, y⟩

x's type receives

(α, z) then (

S(α, β, γ) = ⟨y, x⟩

⟨y, x⟩ z = (y z, x z)

⟨Snd, Fst⟩ ∘ ⟨y, x⟩

App (f, x) = f x

f : ∀ (x : α), γ x

β : α → Type
γ : ∀ (
App(γ, β) : ∀ (x : Σ(α, β)), 
App(γ, β) (f, x) = f x

S α β γ = App ∘ ⟨x, App ∘ y⟩

⟨f, g⟩ x = (f x, g x)

f : ∀ (x : α), β x
(g x) : γ (f x)

g : ∀ (x : α), γ ∘ f
-/

end Expr
