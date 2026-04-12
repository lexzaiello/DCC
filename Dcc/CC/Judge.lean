import Dcc.CC.Ast
import Dcc.CC.Step2

/-
Λ(Sort m, Id(Sort m), Snd(Sort m, Id(Sort m))) : ∀ (x : α)
-/

def arrow (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(m, n) α `(Sort n, Σ(Sort m, Id(Sort m)), β))

syntax "(" expr ":" expr ")" "→" "(" expr ":" expr ")" : expr

macro_rules
  | `(DCC ($α:expr : Sort $m) → ($β:expr : Sort $n)) => `(arrow (DCC $α) (DCC $β) $m $n)

namespace Expr

inductive IsArrow : Expr → (α β : Expr) → Level → Level → Type
  | mk    : IsArrow (arrow α β m n) α β m n
deriving Repr

def is_arrow (t : Expr) : Option ((α β : Expr) × (m n : Level) × IsArrow t α β m n) :=
  match t with
  | DCC (Π(m, n) α `(Sort n₂, Σ(Sort m₂, Id(Sort m₃)), β)) =>
    if heq : m = m₂ ∧ m = m₃ ∧ n = n₂ then
      have ⟨ha, hb, hc⟩ := heq
      .some ⟨α, β, m, n, (by simp_all; exact .mk)⟩
    else .none
  | _ => .none

def IsArrow.complete (h : IsArrow e α β m n) : is_arrow e = .some ⟨α, β, m, n, h⟩ := by
  cases h
  simp [is_arrow, arrow]
  aesop

end Expr

def Pi.type (m n : Level) : Expr :=
  arrow (DCC Sort m)
    (arrow
      (arrow
        (DCC Σ(Sort m, Id(Sort m)))
        (DCC Sort n) m.succ n.succ)
      (DCC Sort n) n.succ n.succ) m.succ n.succ

#eval Std.format (Pi.type 0 2)

/-
Σ α β : Sort (max m n)
-/
def Sigma.type (m n : Level) : Expr :=
  (DCC (Sort max m n))

def id.type (α : Expr) (m : Level) : Expr :=
  arrow α α m m

def flip.type (α β γ : Expr) (m n o : Level) : Expr :=
  (arrow β (arrow α γ m o) n o).reduce.fst

/-
g : α → β
f : ∀ (x : β), γ x
-/
def comp'.type (α β γ g : Expr) (m n o : Level) : Expr :=
  DCC (Π(m, o) α ((Λ'(Sort n, Id(Sort n), γ) β) ∘' (g ∘' Snd'(Sort m, α))))

/-
  g : Π (x : α), Σ α β
  f : Π (x : Σ α β), γ x
  (f ∘ g) : (Π(m, o) α ((Λ(Id(Sort n), γ) (Σ(α, β))) ∘' (g ∘' Snd'(Sort m, α))))

  (⟦α, β, γ⟧∘) : )
-/
def comp.type (α β γ : Expr) (m n o : Level) : Expr :=
  DCC
    ((((α : Sort m) → (Σ(α, β) : Sort (max m n))) : Sort (max m n)) →
    ((Π(n, o) ((α : Sort m) → (Σ(α, β) : Sort (max m n)))
    ((Π(m, o) α) ∘'
      (Flip(Λ'(
          ((α : Sort m) → (Σ(α, β) : Sort (max m n))),
          α,
          (⟦Sort (max m n),
             Id(Sort max m n),
             `(Sort o.succ,
               Σ(Sort (max m n), Id(Sort (max m n))),
               Sort o)⟧∘ γ
            (⟦α, β,
                `(Sort (max m n).succ,
                  Σ(α, β),
                  Σ(Sort (max m n), Id(Sort (max m n))))⟧∘
              ⟦Sort (max m n), Id(Sort (max m n))⟧(, Σ(α, β))
              App((max m n), α, `(Sort (max m n), α, Σ(α, β)))))))
            ∘' Snd'(Sort (max m n), ((α : Sort m) → (Σ(α, β) : Sort (max m n))))))) : Sort o))

def pair.type (α β γ : Expr) (m n o : Level) : Expr :=
  (arrow α (DCC Σ(β, γ)) m (max n o))

def fst.type (α β : Expr) (m n : Level) : Expr :=
  (arrow (DCC Σ(α, β)) α (max m n) m)

def snd'.type (α β : Expr) (m n : Level) : Expr :=
  (arrow (DCC Σ(α, `(Sort n, α, β))) β (max m n) n)

def snd.type (α β : Expr) (m n : Level) : Expr :=
  (DCC (Π(max m n, n)
    Σ(α, β) (β ∘' Fst(α, β) ∘' Snd'(Sort (max m n), Σ(α, β)))))

/-
α is type of x in (f, x)
f : ∀ α, β x
-/
def app_e.type (α β : Expr) (m n : Level) : Expr :=
  let t_f := DCC (Π(m, n) α β)
  let t_x := DCC `(Sort n, t_f, α)

  DCC (Π(max m n, n)
      Σ(t_f, t_x)
      ((Λ'(Sort m, Id(Sort m), β) α) ∘' (Snd(t_f, t_x) ∘' Snd'(Sort (max m n), Σ(t_f, t_x)))))

/-
x : Σ(α, β) → γ
Λ'(β, x) : α → β → γ
-/
def curr'.type (α β γ : Expr) (m n o : Level) : Expr :=
  DCC (Π(m, o) α ((Flip(Π(n, o)) `(Sort o, Σ(Sort n, Id(Sort n)), γ)) ∘' (β ∘' Snd'(Sort m, α))))

/-
Λ(α, γ, x) : ∀ (x : α) (y : x), γ ⟦α, Id(α)⟧(x, y)
-/
def curr.type (α γ : Expr) (m n : Level) : Expr :=
  (DCC (Π(m.succ, n) α ((Flip(Π(m, n)) (γ ∘'
  (Λ'(Sort m.succ, Id(Sort m.succ), Id(Σ(Sort m.succ, Id(Sort m.succ)))) ⟦Sort m.succ, Id(Sort m.succ)⟧(α, Id(α))))) ∘' Snd'(Sort m.succ, α))))

/-
⟦α, β⟧(,) : ∀ (x : α) (y : β x), Σ(α, β)
-/

def coup.type (α β : Expr) (m n : Level) : Expr :=
  (DCC (Π(m, (max m n)) α
    ((Flip(Π(n, (max m n))) `(Sort (max m n), Σ(Sort n, Id(Sort n)), Σ(α, β))) ∘' (β ∘' Snd'(Sort m, α)))))

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

    x : ∀ (x : α)
  -/
  | flip  : Judge x τ₁
    → IsArrow τ₁ α τ₂ m o
    → IsArrow τ₂ β γ n o 
    → Judge (DCC Flip(x)) (flip.type α β γ m n o).reduce.fst
  -- g : Π β A
  | comp'  : Judge g τ₁
    → IsArrow τ₁ α β m n
    → Judge f (DCC (Π(n, o) β γ))
    → Judge (DCC f ∘' g) (comp'.type α β γ g m n o).reduce.fst
  | comp   : Judge α (DCC Sort m)
    → Judge β τ₁
    → IsArrow τ₁ α (DCC (Sort n)) m n.succ
    → Judge γ τ₂
    → IsArrow τ₂ (DCC Σ(α, β)) (DCC Sort o) (max m n) o.succ
    → Judge (DCC ⟦α, β, γ⟧∘) (comp.type α β γ m n o).reduce.fst
  /-
    ⟦m, α, γ⟧⟨f, g⟩ x = ⟦(γ ⟦Id(Sort m)⟧(α, x))⟧(f x, g x)
    f : α → β
    g : ∀ (x : α), γ x

    ⟦m, α, γ⟧⟨f, g⟩ x : (Σ(n, o) (β x) γ)
  -/
  | pair  : Judge f τ₁
    → IsArrow τ₁ α β m n
    → Judge g (DCC (Π(m, o) α (γ ∘' (f ∘' Snd'(Sort m, α)))))
    → Judge (DCC ⟦β, γ⟧⟨f, g⟩) (pair.type α β γ m n o).reduce.fst
  -- fst(α, β) : (Σ α β) → α
  | fst   : Judge α (DCC Sort m)
    → Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m n.succ
    → Judge (DCC Fst(α, β)) (fst.type α β m n).reduce.fst
  | snd'  : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Judge (DCC Snd'(α, β)) (snd'.type α β m n).reduce.fst
  /- snd(α, β) : 
  -/
  | snd   : Judge α (DCC Sort m)
    → Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m n.succ
    → Judge (DCC Snd(α, β)) (snd.type α β m n).reduce.fst
  | curr' : Judge x τ₁
    → (IsArrow τ₁ (DCC Σ(α, β)) γ (max m n) o)
    → Judge β τ₂
    → IsArrow τ₂ α (DCC Sort n) m n.succ
    → Judge (DCC Λ'(α, β, x)) (curr'.type α β γ m n o).reduce.fst
  /-
    x : Σ(α, β) → γ
    β : α → Sort n
  -/
  | curr  : Judge α (DCC (Sort m.succ))
    → Judge x (DCC (Π(m.succ, n) Σ(α, Id(α)) γ))
    → Judge (DCC Λ(α, x)) (curr.type α γ m n).reduce.fst
  /-
    App(γ, β) : (Π(max o n, o)
      (Σ(o, n) (Π(n, o) β γ) `((Π(n, o) β γ), β))
      (γ ∘ (Snd((Π(n, o) β γ), `((Π(n, o) β γ), β)) ∘ Snd(Sort (max o n), Id(Sort (max o n))))))
  -/
  | app_e : Judge α (DCC Sort m)
    → Judge (DCC App(n, α, β)) (app_e.type α β m n).reduce.fst
  /-
    a : α
    b : β a
    ⟦β⟧(a, b) : Σ α β
  -/
  | coup  : Judge α (DCC (Sort m))
    → Judge β τ₁
    → IsArrow τ₁ α (DCC (Sort n)) m n.succ
    → Judge (DCC ⟦α, β⟧(,)) (coup.type α β m n)
  -- Can derive dependent quotation
  | quot  : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Judge x α
    → Judge (DCC `(α, β, x)) (quot.type α β m n).reduce.fst
  | pi    : Judge (DCC Π(m, n)) (Pi.type m n)
  | sigma : Judge α (DCC Sort m)
    → Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m n.succ
    → Judge (DCC Σ(α, β)) (Sigma.type m n)
  | app   : Judge f (DCC (Π(m, n) α β))
    → Judge x α
    → Judge (DCC (f x)) (DCC (β ⟦Sort m, Id(Sort m)⟧(α, x))).reduce.fst
  | sort  : Judge (DCC Sort m) (DCC Sort m.succ)
deriving Repr

instance : Std.ToFormat (Judge A B) := ⟨repr⟩

def match_arrow (t : Expr) : Option ((α β : Expr) × (m n : ℕ) × (PLift (t = arrow α β m n))) :=
  match t with
  | DCC (Π(m₁, n₁) α `(Sort n₂, Σ(Sort m₂, Id(Sort m₃)), β)) =>
    if heq : m₁ = m₃ ∧ n₁ = n₂ ∧ m₁ = m₂ then
      .some ⟨α, β, m₁, n₁, ⟨by have ⟨ha, hb, hc⟩ := heq; rw [← ha, ← hb, ← hc]; rfl⟩⟩
    else
      .none
  | _ => .none

set_option maxHeartbeats 0 in def infer (e : Expr) : Option ((t : Expr) × (Judge e t)) :=
  match e with
  | DCC Π(m, n) => .some ⟨_, .pi⟩
  | DCC Σ(α, β) =>
    match α.infer with
    | .some ⟨DCC Sort m, h_t_α⟩ =>
      match β.infer with
      | .some ⟨t_β, h_t_β⟩ =>
        match t_β.is_arrow with
        | .some ⟨α₂, DCC Sort n, m₂, n₂, heq⟩ =>
          if heq₂ : α = α₂ ∧ n₂ = n.succ ∧ m = m₂ then
            have ⟨ha, hb, hc⟩ := heq₂
            .some ⟨_, .sigma h_t_α h_t_β (by rw [← ha, hb, ← hc] at heq; exact heq)⟩
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC ⟦α, β⟧(,) =>
    match α.infer, β.infer with
    | .some ⟨DCC Sort m, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match t_β.is_arrow with
      | .some ⟨α₂, DCC Sort n, m₂, n₂, heq₀⟩ =>
        if heq₂ : α = α₂ then
          if heq₄ : n₂ = n.succ then
            if heq₅ : m = m₂ then
              .some ⟨_, .coup h_t_α h_t_β (heq₅ ▸ heq₄ ▸ (heq₂ ▸ heq₀))⟩
            else .none
          else .none
        else .none
      | _ => .none
    | _, _ => .none
  | DCC Sort m => .some ⟨DCC Sort m.succ, .sort⟩
  | DCC `(α, β, x) =>
    match x.infer, α.infer, β.infer with
    | .some ⟨t_x, h_t_x⟩, .some ⟨DCC Sort m, h_t_α⟩, .some ⟨DCC Sort n, h_t_β⟩ =>
      if heq : t_x = α then
        .some ⟨_, .quot h_t_α h_t_β (heq ▸ h_t_x)⟩
      else .none
    | _, _, _ => .none
  | DCC Id(α)  => match α.infer with
    | .some ⟨DCC Sort m, h⟩ => return ⟨(id.type α m).reduce.fst, .id h⟩
    | _ => .none
  | DCC Fst(α, β) => match infer α, infer β with
    | .some ⟨DCC Sort m, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match t_β.is_arrow with
      | .some ⟨α₁, DCC Sort n, m₁, n₁, heq₁⟩ =>
        if heq : α = α₁ ∧ n.succ = n₁ ∧ m = m₁ then
          have ⟨heqa, heqb, heqc⟩ := heq
          .some ⟨_, .fst h_t_α h_t_β (by rw [← heqa, ← heqb, ← heqc] at heq₁; exact heq₁)⟩
        else .none
      | _ => .none
    | _, _ => .none
  | DCC Snd'(α, β) => match infer α, infer β with
    | .some ⟨DCC Sort m, h_t_α⟩, .some ⟨DCC Sort n, h_t_β⟩ =>
      .some ⟨_, .snd' h_t_α h_t_β⟩
    | _, _ => .none
  | DCC Snd(α, β) =>
    match infer α, infer β with
    | .some ⟨DCC Sort m, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match t_β.is_arrow with
      | .some ⟨α₁, DCC Sort n, m₁, n₁, heq₁⟩ =>
        if heq : α = α₁ ∧ n.succ = n₁ ∧ m = m₁ then
          have ⟨heqa, heqb, heqc⟩ := heq
          .some ⟨_, .snd h_t_α h_t_β (by rw [← heqa, ← heqb, ← heqc] at heq₁; exact heq₁)⟩
        else .none
      | _ => .none
    | _, _ => .none
  | DCC Flip(x) =>
    match x.infer with
    | .some ⟨t_x, h_t_x⟩ =>
      match t_x.is_arrow with
      | .some ⟨α, βγ, m, o, heq⟩ =>
        match βγ.is_arrow with
        | .some ⟨β, γ, n, o₂, heq₂⟩ =>
          if heq₃ : o = o₂ then
            .some ⟨_, .flip (γ := γ) h_t_x heq (by simp_all; exact heq₂)⟩
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC App(n, α, β) =>
    match α.infer with
    | .some ⟨DCC Sort m, h_t_α⟩ =>
      .some ⟨_, .app_e h_t_α⟩
    | _ => .none
  | DCC Λ'(α, β, x) =>
    match x.infer, β.infer with
    | .some ⟨t_x, h_t_x⟩, .some ⟨t_β, h_t_β⟩ =>
      match t_x.is_arrow, t_β.is_arrow with
      | .some ⟨DCC Σ(α₁, β₂), γ, mn, o, heq₁⟩, .some ⟨DCC α₂, DCC Sort n, m, n₂, heq₂⟩ =>
        if heq : mn = max m n ∧ β₂ = β ∧ n₂ = n.succ ∧ α₂ = α ∧ α₁ = α then
          have ⟨ha, hb, hc, hd, he⟩ := heq
          .some ⟨_, .curr' h_t_x (by rw [ha, hb, he] at heq₁; exact heq₁) h_t_β (by rw [hd, hc] at heq₂; exact heq₂)⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC Λ(α, x) =>
    match heq₀ : α.infer, x.infer with
    | .some ⟨DCC Sort m + 1, h_t_α⟩, .some ⟨(DCC (Π(m₂ + 1, n) Σ(α₁, Id(α₂)) γ₂)), h_t_x⟩ =>
      if heq₂ : m₂ = m ∧ α₁ = α ∧ α = α₂ then
        have ⟨ha, hb, hc⟩ := heq₂
        .some ⟨_, Judge.curr
          h_t_α
          (ha ▸ hb ▸ hc ▸ h_t_x)⟩
      else .none
    | _, _ => .none
  | DCC ⟦β, γ⟧⟨f, g⟩ =>
    match infer f, infer g with
    | .some ⟨t_f, h_t_f⟩, .some ⟨t_g, h_t_g⟩ =>
      match t_f.is_arrow, t_g with
      | .some ⟨α, β₂, m, n, heq₁⟩,
        (DCC  (Π(m₂, o₂) α₂ (γ₂ ∘' (f₂ ∘' Snd'(Sort m₃, α₃))))) =>
        if heq₃ : m = m₂ ∧ m = m₂ ∧ α = α₂ ∧ γ = γ₂ ∧ f = f₂ ∧ m = m₃ ∧ α = α₃ ∧ β = β₂ then
          have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := heq₃
          .some ⟨_, .pair
            h_t_f
            (h8 ▸ heq₁)
            (by
              rw [← h1, ← h3, ← h4, ← h5, ← h6, ← h7] at h_t_g
              exact h_t_g)⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC f ∘' g =>
    match g.infer, f.infer with
    | .some ⟨t_g, h_t_g⟩, .some ⟨t_f, h_t_f⟩ =>
      match t_g.is_arrow, t_f with
      | .some ⟨α, β₁, m, n₁, heq₁⟩, DCC (Π(n₂, o) β₂ γ) =>
        if heq₃ : β₁ = β₂ ∧ n₁ = n₂ then
          .some ⟨_, .comp' h_t_g heq₁ (by
            have ⟨heqa, heqb⟩ := heq₃
            rw [← heqa, ← heqb] at h_t_f
            exact h_t_f)⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC ⟦α, β, γ⟧∘ =>
    match α.infer, β.infer, γ.infer with
    | .some ⟨DCC Sort m, h_t_α⟩, .some ⟨t_β, h_t_β⟩, .some ⟨t_γ, h_t_γ⟩ =>
      match t_β.is_arrow, t_γ.is_arrow with
      | .some ⟨α₂, DCC Sort n, m₂, n₂, heqa⟩, .some ⟨DCC Σ(α₃, β₂), DCC Sort o, mn, o₂, heqb⟩ =>
        if heq : α₂ = α ∧ α₃ = α ∧ m₂ = m ∧ n₂ = n.succ ∧ mn = (max m n) ∧ o₂ = o.succ ∧ β₂ = β then
          have ⟨ha, hb, hc, hd, he, hf, hg⟩ := heq
          .some ⟨_, .comp h_t_α h_t_β (hd ▸ hc ▸ ha ▸ heqa) h_t_γ (he ▸ hf ▸ hg ▸ hb ▸ heqb)⟩
        else .none
      | _, _ => .none
    | _, _, _ => .none
  | DCC (f x) => match f.infer, x.infer with
    | .some ⟨DCC (Π(m, n) α₁ β), h_f⟩, .some ⟨α₂, h_x⟩ =>
      if heq : α₁ = α₂ then
        .some ⟨(DCC (β ⟦Sort m, Id(Sort m)⟧(α₁, x))).reduce.fst, .app h_f (heq ▸ h_x)⟩
      else .none
    | _, _ => .none

#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Id(Sort 1) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (⟦Sort 2, Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Fst(Sort 2, Id(Sort 2)) ⟦Sort 2, Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Snd(Sort 2, Id(Sort 2)) ⟦Sort 2, Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Σ(Sort 1, Id(Sort 1))))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Π(1, 1) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC Id(Sort 1))
#eval (Std.format ∘ Sigma.fst) <$> infer (id.type (DCC Sort 0) 1)
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (`(Sort 1, Sort 1, Sort 0) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC ((`(Sort 1, Sort 2, Sort 0) ∘' Id(Sort 2)) (Sort 1)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Λ'(Sort 2, Id(Sort 2), Id((Σ(Sort 2,  Id(Sort 2))))) (Sort 1)))

/-
⟦Id(Sort 2)⟧⟨Id(Sort 2), `(Sort 1, Sort 2, Sort 0)⟩
-/

#eval (Std.format ∘ Sigma.fst) <$> infer (DCC Id(Sort 2) ∘' Id(Sort 2))

def test_pair : Option Expr :=
  let f := DCC Id(Sort 2)
  let g := DCC Id(Sort 2) ∘' Id(Sort 2)
  -- γ receives (f x)
  /-
    Id(Sort 2) ∘ Id(Sort 2) :
    (some ((Π(3, 3) Sort 2) (Λ(Id(Sort 3),`(Sort 3, ((Σ(4, 3) Sort 3) Id(Sort 3)), Sort 2)) Sort 2)
      ∘ Id(Sort 2) ∘ Snd(Sort 3, Id(Sort 3))))
  -/
  let γ := DCC (Λ'(Sort 3, Id(Sort 3),`(Sort 3, Σ(Sort 3, Id(Sort 3)), Sort 2)) Sort 2)
  let e := DCC (⟦Sort 2, γ⟧⟨f, g⟩ (Sort 1))
  Sigma.fst <$> e.infer

#eval test_pair.format

def Id' (m : Level) : Expr :=
  DCC Λ(Sort m, Snd(Sort m, Id(Sort m)))

#eval (DCC Snd(Sort 2, Id(Sort 2))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ((#(Id' 2) (Sort 1)) (Sort 0))).infer

theorem Judge.complete (h_t : Judge e t) : infer e = .some ⟨t, h_t⟩ := by
  induction h_t with
  | app _ _ ih₁ ih₂ => unfold infer; rw [ih₁, ih₂]; simp
  | quot _ _ _ ih₁ ih₂ ih₃ => unfold infer; rw [ih₁, ih₂, ih₃]; simp
  | app_e _ ih => unfold infer; rw [ih]
  | sigma _ _ h_t_arrow ih₁ ih₂ =>
    have h := h_t_arrow.complete
    unfold infer
    rw [ih₁, ih₂]
    simp [h]
    split
    · rfl
  | sort => unfold infer; rfl
  | pi => unfold infer; rfl
  | comp' _ h_t_arrow _ ih₁ ih₂ =>
    have h := h_t_arrow.complete
    unfold infer
    rw [ih₁, ih₂]
    aesop
  | comp _ _ h_t_arrow₁ _ h_t_arrow₂ ih₁ ih₂ ih₃ =>
    have ha := h_t_arrow₁.complete
    have hb := h_t_arrow₂.complete
    unfold infer
    simp [ih₁, ih₂, ih₃, ha, hb]
    split
    rfl
  | fst _ _ h_t_arrow ih₁ ih₂ =>
    have h := h_t_arrow.complete
    unfold infer
    rw [ih₁, ih₂]
    aesop
  | snd _ _ h_t_arrow ih₁ ih₂ =>
    have h := h_t_arrow.complete
    unfold infer
    rw [ih₁, ih₂]
    aesop
  | snd' _ _ ih₁ ih₂ => unfold infer; rw [ih₁, ih₂]
  | curr _ _ ih₁ ih₂ =>
    unfold infer
    rw [ih₁, ih₂]
    aesop
  | curr' _ h_arrow₁ _ h_arrow₂ ih₁ ih₂ =>
    have ha := h_arrow₁.complete
    have hb := h_arrow₂.complete
    unfold infer
    simp [ih₁, ih₂, ha, hb]
    split
    rfl
  | pair _ h_arrow _ ih₁ ih₂ =>
    have h := h_arrow.complete
    unfold infer
    rw [ih₁, ih₂]
    aesop
  | coup _ _ h_arrow ih₁ ih₂ =>
    have h := h_arrow.complete
    unfold infer
    simp [ih₁, ih₂, h]
  | id _ ih =>
    unfold infer
    simp [ih]
  | flip _ h_arrow₁ h_arrow₂ ih =>
    have ha := h_arrow₁.complete
    have hb := h_arrow₂.complete
    unfold infer
    rw [ih]
    aesop

def Judge.decide : Judge e t ⊕ (Judge e t → PLift False) :=
  if h : (infer e).isSome then
    if heq : ((infer e).get h).fst = t then
      .inl (heq ▸ ((infer e).get h).snd)
    else
      .inr fun hn => by
        have h_comp := hn.complete
        simp_all
  else .inr fun hn => by
    have h_comp := hn.complete
    simp_all

def judge_sound (_h_t : Expr.infer e = .some ⟨t, h⟩) : e.Judge t := h

end Expr

/-
def point_free_id (h_t_α : α.Judge (DCC Sort m)) (h_t_x : x.Judge α) : (DCC (#(Expr.mk_id m) α x)).Judge α := by
  unfold Expr.mk_id
  have h := Expr.Judge.app 
  
  sorry
-/
