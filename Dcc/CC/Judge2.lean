import Dcc.CC.Ast
import Dcc.CC.Step2


def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, `(α, β))) α)

def id.type (α : Expr) (m : Level) : Expr :=
  arrow α (arrow α α m) m

def fst.type (α β : Expr) (m n : Level) : Expr :=
  arrow (DCC Σ(β)) α (max m n)

def snd.type (β : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)),
    `(Sort (max m n),
      β ∘ Fst(β))) Σ(β))

def coup.type (β : Expr) : Expr :=
  DCC Σ(β)

/-
x : ∀ (s : Σ(β)), γ s
Λ(β, x) : ∀ (x : α) (y : β x), γ ⟦β⟧(x, y)
-/
def curr.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m),
    `(Sort m, Π(β,
      Λ(β, (γ Σ(β)))))) α) -- weaken α, keep x

/-
Nondependent quotation.

x : α
`(β, x) : β → α
-/
def quot.type (α β : Expr) (n : Level) : Expr :=
  arrow β α n

/-
f : ∀ (x : α), β x
g : ∀ (x : α), γ (f x)
⟨f, g⟩ : α → Σ(γ)
-/
def pair.type (α γ : Expr) (m : Level) : Expr :=
  arrow α (DCC Σ(γ)) m

/-
f ∘ g is tail-dependent composition. f is dependent, but g is not.

dependent composition can be derived, however, if g's codomain is Σ α, β

f ∘ g : ∀ (x : α), γ (g x)
-/
def comp.type (α β γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, (γ β) ∘ g)) α)

/-
f : ∀ (x : α), β x
App(β) : ∀ (s : Σ(`(Π(m, Id(Sort m), β), α))), (β α) ∘ Snd'(Π(m, Id(Sort m), β), β)
-/
def App.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)), (β α) ∘ Snd'(Π(Id(Sort m), β), β))
    Σ(`(Π(Id(Sort m), β), α)))

def snd'.type (α β : Expr) (m n : Level) : Expr :=
  arrow (DCC Σ(`(α, β))) β (max m n)

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
def Pi.type (α : Expr) (m n : Level) : Expr :=
  arrow α (DCC Sort n) m

def Sigma.type (m n : Level) : Expr :=
  DCC (Sort (max m n))

namespace Expr

inductive Reduces : Expr → Expr → Prop
  | mk : RedAffReflTrans A B → IsNormAff B → Reduces A B

@[simp] theorem Reduces.unique : Reduces A B → Reduces A C → B = C := fun ⟨a, b⟩ ⟨c, d⟩ =>
  a.norm_unique b c d

@[simp] theorem Reduces.unique' (h₁ : Reduces A B) (h₂ : Reduces A C) : h₁ ≍ h₂ := by
  have h := h₁.unique h₂
  cases h
  congr

theorem Reduces.complete : Reduces A B → reduce A = B :=
  fun ⟨ha, hb⟩ => ha.complete hb

def reduce_reduces (h : reduce A = B) : Reduces A B := ⟨reduce_sound h, reduce_norm h⟩

def reduce_reduces' : Reduces A A.reduce := reduce_reduces rfl

inductive IsArrow : Expr → (α β : Expr) → Level → Prop
  | mk    : Reduces A (arrow α β m) → IsArrow A α β m

def IsArrow.unique (h₁ : IsArrow τ α β m) (h₂ : IsArrow τ α₂ β₂ n) : m = n ∧ α = α₂ ∧ β = β₂ := by
  induction h₁ generalizing n
  induction h₂ generalizing m
  rename_i h₁ h₂
  have h := h₂.complete
  rw [h₁.complete] at h
  unfold arrow at h
  simp_all

def IsArrow.unique' (h₁ : IsArrow τ α β m) (h₂ : IsArrow τ α β m) : h₁ = h₂ := by
  induction h₁
  cases h₂
  rename_i h₁ h₂
  cases h₁.unique' h₂
  rfl

@[inline] abbrev is_arrow (t : Expr) : Option ((α β : Expr) × (m : Level) × PLift (IsArrow t α β m)) :=
  match heq₀ : t.reduce with
  | DCC (Π(Id(Sort m), `(Sort m₂, `(α, β))) α₂) =>
    if heq : m = m₂ ∧ α = α₂ then
      have ⟨h₁, h₂⟩ := heq
      .some ⟨α, β, m, ⟨reduce_sound (by
        rw [← h₁, ← h₂] at heq₀
        exact heq₀), reduce_norm (by
        rw [← h₁, ← h₂] at heq₀
        exact heq₀)⟩⟩
    else
      .none
  | _ => .none

def IsArrow.complete (h : IsArrow e α β m) : is_arrow e = .some ⟨α, β, m, ⟨h⟩⟩ := by
  match h with
  | ⟨h⟩ =>
    have ha := h.complete
    simp [is_arrow]
    split
    case h_1 heq' =>
      split
      case isTrue h =>
        split
        rw [heq'] at ha
        cases ha
        rfl
      case isFalse h =>
        rw [heq'] at ha
        cases ha
        exact (h ⟨rfl, rfl⟩).elim
    case h_2 h => exact (h _ _ _ _ _ ha).elim

inductive Judge : Expr → Expr → Prop where
  | id   : Judge α τ
    → Reduces τ (DCC Sort m)
    → Judge (DCC Id(α)) (id.type α m)
  | comp : Judge g τ₁
    → IsArrow τ₁ α β m
    → Judge f τ₂
    → Reduces τ₂ (DCC (Π(Id(Sort n), γ) β))
    → Judge (DCC f ∘ g) (comp.type α β γ g m)
  | fst  : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC Fst(β)) (fst.type α β m n)
  | snd   : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC Snd(β)) (snd.type β m n)
  | sigma : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC Σ(β)) (Sigma.type m n)
  | snd' : Judge α τ₁
    → Reduces τ₁ (DCC Sort m)
    → Judge β τ₂
    → Reduces τ₂ (DCC Sort n)
    → Judge (DCC Snd'(α, β)) (snd'.type α β m n)
  | coup : Judge x τ₁
    → Reduces τ₁ α
    → Judge y τ₂
    → Judge β τ₃
    → IsArrow τ₃ α (DCC Sort n) m
    → Reduces (DCC (β x)) τ₂'
    → Reduces τ₂ τ₂'
    → Judge (DCC ⟦β⟧(x, y)) (coup.type β)
  | curr : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge x τ₂
    → Reduces τ₂ (DCC (Π(f_α, γ) x_α))
    → Reduces (DCC (f_α x_α)) (DCC Σ(β))
    → Judge (DCC Λ(β, x)) (curr.type α β γ m)
  | quot : Judge x τ₁
    → Reduces τ₁ α
    → Judge β τ₂
    → Reduces τ₂ (DCC Sort n)
    → Judge (DCC `(β, x)) (quot.type α β n)
  | pair : Judge f τ₁
    → Reduces τ₁ (DCC (Π(f_α, β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge g τ₂
    → Reduces τ₂ (DCC (Π(f_α₂, `(Sort m, γ ∘ f)) x_α₂))
    → Reduces (DCC (f_α₂ x_α₂)) α
    → Judge (DCC ⟦γ⟧⟨f, g⟩) (pair.type α γ m)
  | appl : Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge (DCC App(β)) (App.type α β m n)
  | pi   : Judge f_α τ₁
    → IsArrow τ₁ α (DCC Sort n) m
    → Judge f_β τ₂
    → Reduces τ₂ (DCC Π(Id(α), Π(f_α, `(α, `(Sort n, Sort o)))))
    → Judge (DCC Π(f_α, f_β)) (Pi.type α m n)
  | sort : Judge (DCC Sort m) (DCC Sort m.succ)
  | app  : Judge f τ₁
    → Reduces τ₁ (DCC (Π(f_α, f_β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge x τ₂
    → Reduces τ₂ α
    → Judge (DCC (f x)) (DCC (f_β x_α x))

@[inline] abbrev with_red (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ₁ τ₂ : Expr) × PLift (Judge e τ₁) × PLift (Reduces τ₁ τ₂)) :=
  match h with
  | .some ⟨t, h⟩ => .some ⟨t, t.reduce, h, ⟨reduce_reduces rfl⟩⟩
  | _ => .none

@[inline] abbrev with_arr (h : Option ((t : Expr) × PLift (Judge e t))) :
  Option ((τ α β : Expr) × (m : Level) × PLift (Judge e τ) × PLift (IsArrow τ α β m)) :=
    match h with
    | .some ⟨t, h⟩ => match is_arrow t with
      | .some ⟨α, β, m, h_arr⟩ => .some ⟨t, α, β, m, h, h_arr⟩
      | _ => .none
    | _ => .none

def Judge.unique (h₁ : Judge x τ₁) (h₂ : Judge x τ₂) : τ₁ = τ₂ := by
  induction h₁ generalizing τ₂ with
  | app ht₁ hr₁ hr₂ ht₂ hr₃ ih₁ ih₂ =>
    cases h₂
    rename_i hr₄ hr₅ hr₆ ht₃ ht₄
    have ha := ih₁ ht₃
    have hb := ih₂ ht₄
    have h₁ := hr₁.unique (ha ▸ hr₄)
    have h₂ := hr₃.unique (hb ▸ hr₆)
    simp_all
  | pair ht₁ hr₁ hr₂ ht₂ hra hr₄ ih₁ ih₂ =>
    cases h₂
    rename_i hr₃ hr₄ hr₅ ht₃ hr₆ ht₇
    have ha := ih₁ ht₃
    have hb := ih₂ ht₇
    have h₁ := hr₁.unique (ha ▸ hr₃)
    have h₂ := hra.unique (hb ▸ hr₆)
    simp_all
    have h₁ := hr₂.unique (by exact hr₄)
    simp_all
  | pi ht₁ harr₁ ht₂ hr₁ ih₁ ih₂ =>
    cases h₂
    rename_i harr₂ ht₃ hr₂ ht₄
    have ha := ih₁ ht₃
    have hb := ih₂ ht₄
    have h₁ := harr₁.unique (ha ▸ harr₂)
    have h₂ := hr₁.unique (hb ▸ hr₂)
    simp_all
  | appl ht harr ih =>
    cases h₂
    rename_i harr₂ ht₂
    have h := ih ht₂
    have h := harr.unique (h ▸ harr₂)
    simp_all
  | quot ht₁ hr₁ ht₂ hr₂ ih₁ ih₂  =>
    cases h₂
    rename_i hr₃ hr₄ ht₃ ht₄
    have ha := ih₁ ht₄
    have hb := ih₂ ht₃
    have h₁ := hr₁.unique (ha ▸ hr₃)
    have h₂ := hr₂.unique (hb ▸ hr₄)
    simp_all
  | sort => cases h₂; rfl
  | curr _ harr₁ _ hr₁ hr₂ ih₁ ih₂  =>
    cases h₂
    rename_i harrb hrb ht₂ hr₂ ht₃
    have ha := ih₁ ht₂
    have hb := ih₂ ht₃
    have h₁ := harr₁.unique (ha ▸ harrb)
    have h₂ := hr₁.unique (hb ▸ hrb)
    simp_all
  | id _ hred ih =>
    have ha := hred.complete
    cases h₂ with
    | id h₂ hred =>
      have hb := hred.complete
      have h := ih h₂
      simp_all
  | comp _ _ _ hr₁ ih₁ ih₂ =>
    cases h₂ with
    | comp =>
      rename_i hr₂ _ _
      have ha := hr₁.complete
      have hb := hr₂.complete
      rename_i h₂ h₃
      have hc := ih₁ h₃
      have hd := ih₂ h₂
      rename_i h_arrow₁ _ _ _ _ _ _ _ _ h_arrow₂
      have h := h_arrow₁.unique (hc ▸ h_arrow₂)
      simp_all
  | sigma | snd | fst =>
    cases h₂
    rename_i h_arrow₁ ih _ _ _ _ h_arrow₂ h
    have h := ih h
    have h := h_arrow₁.unique (h ▸ h_arrow₂)
    simp_all
  | snd' =>
    cases h₂
    rename_i ih₁ ih₂ _ _ _ _ _ _ ha hb
    have ha := ih₁ ha
    have hb := ih₂ hb
    rename_i hr₁ _ hr₂ _ _ _ _ hr₃ hr₄ _ _
    have h₁ := hr₁.unique (ha ▸ hr₃)
    have h₂ := hr₂.unique (hb ▸ hr₄)
    simp_all
  | coup _ _ _ _ _ _ _ ih₁ ih₂ ih₃ =>
    cases h₂
    rfl

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge e t)) :=
  match e with
  | DCC Sort m => .some ⟨_, ⟨.sort⟩⟩
  | DCC (Id(α)) =>
    match with_red (infer α) with
    | .some ⟨_, DCC Sort m, ⟨ht⟩, ⟨h_red⟩⟩ => .some ⟨_, ⟨.id ht h_red⟩⟩
    | _ => .none
  | DCC (f ∘ g) =>
    match with_arr (infer g), with_red (infer f) with
    | .some ⟨_, α, β, m, ⟨ht₁⟩, ⟨harr₁⟩⟩, .some ⟨_, (DCC (Π(Id(Sort n₂), γ) β₂)), ⟨ht₂⟩, ⟨hred⟩⟩ =>
      if heq : β₂ = β then
        .some ⟨_, ⟨.comp ht₁ harr₁ ht₂ (heq ▸ hred)⟩⟩
      else .none
    | _, _ => .none
  | DCC Fst(β) =>
    match with_arr (infer β) with
    | .some ⟨τ₁, α, DCC Sort n, m, ⟨ht⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.fst ht harr⟩⟩
    | _ => .none
  | DCC Snd(β) =>
    match with_arr (infer β) with
    | .some ⟨τ₁, α, DCC Sort n, m, ⟨ht⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.snd ht harr⟩⟩
    | _ => .none
  | DCC Σ(β) =>
    match with_arr (infer β) with
    | .some ⟨τ₁, α, DCC Sort n, m, ⟨ht⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.sigma ht harr⟩⟩
    | _ => .none
  | DCC Snd'(α, β) =>
    match with_red (infer α), with_red (infer β) with
    | .some ⟨τ₁, DCC Sort m, ⟨ht₁⟩, ⟨hr₁⟩⟩, .some ⟨τ₂, DCC Sort n, ⟨ht₂⟩, ⟨hr₂⟩⟩ =>
      .some ⟨_, ⟨.snd' ht₁ hr₁ ht₂ hr₂⟩⟩
    | _, _ => .none
  | DCC ⟦β⟧(x, y) =>
    match with_red (infer x), with_red (infer y), with_arr (infer β) with
    | .some ⟨τ₁, α, ⟨ht₁⟩, ⟨hr₁⟩⟩, .some ⟨τ₂, βxm, ⟨ht₂⟩, ⟨hr₂⟩⟩, .some ⟨_, α₂, DCC Sort n, m, ⟨ht₃⟩, ⟨harr⟩⟩ =>
      if heq : (reduce (DCC (β x))) = βxm ∧ α = α₂ then
        have ⟨h₁, h₂⟩ := heq
        .some ⟨_, ⟨.coup ht₁ hr₁ ht₂ ht₃ (h₂ ▸ harr) (reduce_reduces h₁) hr₂⟩⟩
      else .none
    | _, _, _ => .none
  | DCC Λ(β, x) =>
    match with_arr (infer β), with_red (infer x) with
    | .some ⟨τ₁, α, DCC Sort n, m, ⟨ht₁⟩, ⟨harr₁⟩⟩, .some ⟨τ₂, DCC (Π(f_α, γ) x_α), ⟨ht₂⟩, ⟨hr₂⟩⟩ =>
      if heq : (reduce (DCC (f_α x_α)) = DCC Σ(β)) then
        .some ⟨_, ⟨.curr ht₁ harr₁ ht₂ hr₂ (reduce_reduces heq)⟩⟩
      else .none
    | _, _ => .none
  | DCC `(β, x) =>
    match with_red (infer x), with_red (infer β) with
    | .some ⟨τ₁, α, ⟨ht₁⟩, ⟨hr₁⟩⟩, .some ⟨τ₂, DCC Sort n, ⟨ht₂⟩, ⟨hr₂⟩⟩ =>
      .some ⟨_, ⟨.quot ht₁ hr₁ ht₂ hr₂⟩⟩
    | _, _ => .none
  | DCC ⟦γ⟧⟨f, g⟩ =>
    match with_red (infer f), with_red (infer g) with
    | .some ⟨τ₁, DCC (Π(f_α, β) x_α), ⟨ht₁⟩, ⟨hr₁⟩⟩, .some ⟨τ₂, DCC (Π(f_α₂, `(Sort m₃, γ₂ ∘ f₂)) x_α₂), ⟨ht₂⟩, ⟨hr₂⟩⟩ =>
      if heq : (reduce (DCC (f_α x_α)) = reduce (DCC (f_α₂ x_α₂))) ∧ f₂ = f ∧ γ₂ = γ then
        have ⟨h₁, h₂, h₃⟩ := heq
        .some ⟨_, ⟨.pair ht₁ hr₁ (reduce_reduces rfl) ht₂ (by
          rw [h₂, h₃] at hr₂
          exact hr₂) (reduce_reduces h₁.symm)⟩⟩
      else .none
    | _, _ => .none
  | DCC App(β) =>
    match with_arr (infer β) with
    | .some ⟨τ₁, α, DCC Sort n, m, ⟨ht⟩, ⟨harr⟩⟩ => .some ⟨_, ⟨.appl ht harr⟩⟩
    | _ => .none
  | DCC Π(f_α, f_β) =>
    match with_arr (infer f_α), with_red (infer f_β) with
    | .some ⟨τ₁, α, DCC Sort n, m₂, ⟨ht₁⟩, ⟨harr⟩⟩, .some ⟨τ₂, DCC Π(Id(α₂), Π(f_α₂, `(α₃, `(Sort n₃, Sort o)))), ⟨ht₂⟩, ⟨hr₂⟩⟩ =>
      if heq : α₂ = α ∧ f_α₂ = f_α ∧ α₃ = α ∧ n₃ = n then
        have ⟨h₁, h₂, h₃, h₄⟩ := heq
        .some ⟨_, ⟨.pi ht₁ harr ht₂ (by
          rw [h₁, h₂, h₃, h₄] at hr₂
          exact hr₂)⟩⟩
      else .none
    | _, _ => .none
  | DCC (f x) =>
    match with_red (infer f), with_red (infer x) with
    | .some ⟨τ₁, DCC (Π(f_α, f_β) x_α), ⟨ht₁⟩, ⟨hr₁⟩⟩, .some ⟨τ₂, τ₂', ⟨ht₂⟩, ⟨hr₂⟩⟩ =>
      if heq : (reduce (DCC (f_α x_α))) = τ₂' then
        .some ⟨_, ⟨.app ht₁ hr₁ (reduce_reduces rfl) ht₂ (heq ▸ hr₂)⟩⟩
      else .none
    | _, _ => .none

theorem Judge.complete (h : Judge e t) : infer e = .some ⟨t, ⟨h⟩⟩ := by
  induction h with
  | id _ h_red ih =>
    have ha := h_red.complete
    dsimp only [infer, with_red]
    simp [ih]
    split
    case h_1 heq =>
      rename_i ht₁ _ _ _ ht₂ hr₂
      have ha := ht₁.unique ht₂
      have hb := h_red.unique (ha ▸ hr₂)
      aesop
    case h_2 =>
      rename_i h
      exact (h _ _ (by assumption) (by assumption) (by
        congr
        aesop)).elim
  | comp h_t_g h_arr h_t_f h_red ih₁ ih₂ =>
    have ha := h_red.complete
    have ha := h_arr.
    dsimp only [infer, with_red]
    rw [ih₁, ih₂, with_arr]
    split
    case h_1 heq =>
      
      sorry

end Expr
