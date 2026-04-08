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

/-
Σ α β : Sort (max m n)
-/
def Sigma.type (m n : Level) : Expr :=
  DCC (Sort (max m n))

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
    → Judge (DCC Flip(x)) (arrow β (arrow α γ m o) n o).reduce.fst
  -- g : Π β A
  | comp  : Judge g (arrow α β m n)
    → Judge f (DCC (Π(n, o) β γ))
    → Judge (DCC f ∘ g) (comp.type α γ g m o).reduce.fst
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
    → Judge (DCC ⟦β⟧⟨f, g⟩) (pair.type α β τ₁ m n o).reduce.fst
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
  | curr  : Judge x (DCC (Π(max m n, o) Σ(α, β) γ))
    → Judge (DCC Λ(m, β, x)) (curr.type α β γ m n o).reduce.fst
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
    → Judge (DCC ⟦β⟧(a, b)) (coup.type α β).reduce.fst
  -- Can derive dependent quotation
  | quot  : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Judge x α
    → Judge (DCC `(α, β, x)) (quot.type α β m n).reduce.fst
  | pi    : Judge (DCC Π(m, n)) (Pi.type m n)
  | sigma : Judge α (DCC (Sort m))
    → Judge β (arrow α (DCC (Sort n)) m n.succ)
    → Judge (DCC Σ(α, β)) (Sigma.type m n).reduce.fst
  | app   : Judge f (DCC (Π(m, n) α β))
    → Judge x α
    → Judge (DCC (f x)) (DCC (β ⟦Id(Sort m)⟧(α, x))).reduce.fst
  | sort  : Judge (DCC Sort m) (DCC Sort m.succ)
deriving Repr

instance : Std.ToFormat (Judge A B) := ⟨repr⟩

def match_arrow (t : Expr) : Option ((α β : Expr) × (m n : ℕ) × (PLift (t = arrow α β m n))) :=
  match t with
  | DCC (Π(m₁, n₁) α `(Sort n₂, Σ(Sort m₂, Id(Sort m₃)), β)) =>
    if heq : m₁ = m₂ ∧ m₁ = m₃ ∧ n₁ = n₂ then
      .some ⟨α, β, m₁, n₁, ⟨by have ⟨heq₁, heq₂, heq₃⟩ := heq; rw [← heq₁, ← heq₂, ← heq₃]; rfl⟩⟩
    else
      .none
  | _ => .none

def infer (e : Expr) : Option ((t : Expr) × (Judge e t)) := do
  match e with
  | DCC Π(m, n) => .some ⟨_, .pi⟩
  | DCC Σ(α, β) =>
    let ⟨t_β, h_t_β⟩ ← β.infer
    match ← α.infer with
    | ⟨DCC Sort m, h_t_α⟩ =>
      match ← t_β.match_arrow with
      | ⟨α₂, DCC Sort n, m₂, n₂, ⟨heq₂⟩⟩ =>
        if ha : α = α₂ then
          if hb : m = m₂ then
            if hc : n.succ = n₂ then
              .some ⟨_, .sigma h_t_α (ha ▸ hb ▸ hc ▸ heq₂ ▸ h_t_β)⟩
            else .none
          else .none
        else .none
      | _ => .none
    | _ => .none
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
  | DCC Λ(m, β, x) =>
    let ⟨t_β, h_t_β⟩ ← β.infer
    match ← β.match_arrow with
    | ⟨α, DCC Sort n, m₂, n₂, ⟨heq₁⟩⟩ =>
      match ← x.infer with
      | ⟨DCC (Π(mn, o) Σ(α₂, β₂) γ), h_t_x⟩ =>
        if heq : max m n = mn ∧ n.succ = n₂ ∧ β = β₂ ∧ α = α₂ ∧ m = m₂ then
          have ⟨ha, hb, hc, _⟩ := heq
          .some ⟨_, .curr (by rw [← ha, ← hc] at h_t_x; exact h_t_x)⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC ⟦β⟧⟨f, g⟩ =>
    let ⟨t_β, h_t_β⟩ ← infer β
    let ⟨t_f, h_t_f⟩ ← infer f
    let ⟨t_g, h_t_g⟩ ← infer g
    match t_β.match_arrow, t_f.match_arrow, t_g with
    | .some ⟨τ₁, (DCC Sort o), n₁, o₂, ⟨heq₁⟩⟩,
      .some ⟨α, τ₁', m, n₂, ⟨heq₂⟩⟩,
      (DCC (Π(m₂, o₃) α₂ (β₂ ∘ f₂ ∘ Snd(Sort m₃, Id(Sort m₄))))) =>
      if heq₃ : τ₁ = τ₁' ∧ o.succ = o₂ ∧ o = o₃ ∧ n₁ = n₂ ∧ m = m₂ ∧ m = m₃ ∧ m = m₄ ∧ f = f₂ ∧ β = β₂ ∧ α = α₂ then
        have ⟨heqa, heqb, heqc, heqd, heqe, heqf, heqg, heqh, heqj, heqk⟩ := heq₃
        .some ⟨_, .pair
          (by rw [heq₁, ← heqb] at h_t_β; exact h_t_β)
          (by rw [heq₂, ← heqa, ← heqd] at h_t_f; exact h_t_f)
          (by rw [← heqe, ← heqc, ← heqj, ← heqk, ← heqh, ← heqf, ← heqg] at h_t_g; exact h_t_g)⟩
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
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC Σ(Sort 1, Id(Sort 1)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Π(1, 1) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC Id(Sort 1))
#eval (Std.format ∘ Sigma.fst) <$> infer (Expr.app
   (Expr.app (Expr.pi 2 2) (Expr.sort 1))
   (Expr.quot
     (Expr.sort 2)
     (Expr.sigma (Expr.sort 2) (Expr.id (Expr.sort 2)))
     (Expr.sort 1)))
#eval (Std.format ∘ Sigma.fst) <$> infer (id.type (DCC Sort 0) 1)
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (`(Sort 1, Sort 1, Sort 0) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (⟦Id(Sort 2)⟧⟨`(Sort 2, Sort 1, Sort 1), Id(Sort 1)⟩ (Sort 0)))
#eval infer (pair.type (DCC Sort 1) (DCC Id(Sort 1)) (DCC (Sort 1)) 2 2 2)

end Expr
