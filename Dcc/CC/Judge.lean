import Dcc.CC.Ast
import Dcc.CC.Step2

namespace Expr

inductive Reduces : Expr → Expr → Type
  | mk : RedAffReflTrans A B → IsNormAff B → Reduces A B
deriving Repr

theorem Reduces.complete : Reduces A B → reduce A = B :=
  fun ⟨ha, hb⟩ => ha.complete hb

def reduce_reduces (h : reduce A = B) : Reduces A B := ⟨reduce_sound h, reduce_norm h⟩

def reduce_reduces' : Reduces A A.reduce := reduce_reduces rfl

end Expr

/-
Λ(Sort m, Id(Sort m), Snd(Sort m, Id(Sort m))) : ∀ (x : α)
-/

def arrow (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(m, n) α `(Sort n, Σ(Sort m, Id(Sort m)), β))

namespace Expr

theorem RedAff.arrow_level : RedAff (arrow α β m n) (arrow α₂ β₂ m₂ n₂) → m = m₂ ∧ n = n₂ := by
  intro h
  cases h with
  | congrFun => exact ⟨rfl, rfl⟩
  | congrArg h => cases h

theorem RedAff.arrow : RedAff (arrow α β m n) τ₂ →  (∃ γ, RedAff α γ ∧ τ₂ = arrow γ β m n) ∨ τ₂ = arrow α β m n := by
  intro h
  cases h with
  | congrFun h =>
    cases h with
    | congrFun h => cases h
    | congrArg h =>
      exact (.inl ⟨_, h, rfl⟩)
  | congrArg h => cases h

theorem reduce_step : (step? e) = .some ⟨e', _h⟩ → reduce e = reduce e' := by
  intro h
  conv =>
    left
    unfold reduce
    rw [h]

@[simp] theorem reduce_comp'₀ : reduce (DCC (f ∘' g)) = (DCC (f ∘' g)) := by
  unfold reduce
  simp [step?]

theorem reduce_congr_pi : reduce (DCC (Π(m, n) α β)) = (DCC (Π(m, n) α.reduce β.reduce)) := by
  let lex_rel := Prod.lex instWellFoundedRel instWellFoundedRel
  induction heq : (α, β) using lex_rel.wf.induction generalizing α β with
  | h a ih =>
    cases heq
    conv =>
      left
      unfold reduce
    simp [step?]
    split
    case h_1 h _ =>
      cases h
      case congrFun h _ =>
        cases h
        case congrFun h _ => cases h
        case congrArg x' h _ =>
          exact h.reduce_same ▸ (ih (x', β) (.left β β h) rfl)
      case congrArg β' h_r_β heq =>
        exact h_r_β.reduce_same ▸ ih (α, β') (by apply Prod.Lex.right; exact h_r_β) rfl
    case h_2 heq =>
      cases h_α : α.step? <;> simp_all
      cases h_β : β.step? <;> simp_all
      have ha := step?_none h_α
      have hb := step?_none h_β
      exact ⟨ha.complete_reduce.symm, hb.complete_reduce.symm⟩

@[simp] theorem reduce_congr_quot : reduce (DCC (`(α, β, x) y)) = reduce x := by
  induction x using instWellFounded.induction with
  | h a ih =>
    conv =>
      left
      unfold reduce
    simp [step?]

theorem reduce_congr_self_arrow : reduce (arrow A β m n) = (arrow (reduce A) β m n) := by
  induction A using instWellFounded.induction with
  | h a ih =>
    unfold reduce
    simp [arrow, step?]
    aesop

@[simp] theorem reduce_congr_arrow (h : reduce A = B) : reduce (arrow A β m n) = (arrow B β m n) := by
  rw [← h]
  exact reduce_congr_self_arrow

theorem reduce_arrow : (arrow α β m n).reduce = τ₂ → τ₂ = (arrow α.reduce β m n) := by
  intro h
  rw [← h]
  exact reduce_congr_self_arrow

theorem reduce_arrow_norm : (arrow (reduce α) β m n).IsNormAff := reduce_norm reduce_congr_self_arrow

end Expr

syntax "(" expr ":" expr ")" "→" "(" expr ":" expr ")" : expr

macro_rules
  | `(DCC ($α:expr : Sort $m) → ($β:expr : Sort $n)) => `(arrow (DCC $α) (DCC $β) $m $n)

namespace Expr

inductive IsArrow : Expr → (α β : Expr) → Level → Level → Type
  | mk    : Reduces A (arrow α β m n) → IsArrow A α β m n
deriving Repr

def is_arrow (t : Expr) : Option ((α β : Expr) × (m n : Level) × IsArrow t α β m n) :=
  match heq₀ : t.reduce with
  | DCC (Π(m, n) α `(Sort n₂, Σ(Sort m₂, Id(Sort m₃)), β)) =>
    if heq : m = m₂ ∧ m = m₃ ∧ n = n₂ then by
      have ⟨ha, hb, hc⟩ := heq
      rw [← ha, ← hb, ← hc] at heq₀
      refine .some ⟨α, β, m, n, ?_, ?_⟩
      · exact reduce_sound heq₀
      · exact reduce_norm heq₀
    else .none
  | _ => .none

def IsArrow.complete (h : IsArrow e α β m n) : is_arrow e = .some ⟨α, β, m, n, h⟩ := by
  match h with
  | ⟨h⟩ =>
    have ha := h.complete
    simp [is_arrow]
    split
    case h_1 heq' =>
      rw [ha] at heq'
      cases heq'
      aesop
    case h_2 h => exact (h _ _ _ _ _ _ _ ha).elim

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
  (arrow β (arrow α γ m o) n o)

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
            ∘' Snd'(Sort (max m n), ((α : Sort m) → (Σ(α, β) : Sort (max m n))))))))

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
  | id    : Judge α τ₁
    → Reduces τ₁ (DCC (Sort m))
    → Judge (DCC Id(α)) (id.type α m)
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
    → Judge (DCC Flip(x)) (flip.type α β γ m n o)
  -- g : Π β A
  | comp'  : Judge g τ₁
    → IsArrow τ₁ α β m n
    → Judge f t_f
    → Reduces t_f (DCC (Π(n, o) β γ))
    → Judge (DCC f ∘' g) (comp'.type α β γ g m n o)
  | comp   : Judge α t_α
    → Reduces t_α (DCC Sort m)
    → Judge β τ₁
    → IsArrow τ₁ α (DCC (Sort n)) m n.succ
    → Judge γ τ₂
    → IsArrow τ₂ (DCC Σ(α, β)) (DCC Sort o) (max m n) o.succ
    → Judge (DCC ⟦α, β, γ⟧∘) (comp.type α β γ m n o)
  /-
    ⟦m, α, γ⟧⟨f, g⟩ x = ⟦(γ ⟦Id(Sort m)⟧(α, x))⟧(f x, g x)
    f : α → β
    g : ∀ (x : α), γ x

    ⟦m, α, γ⟧⟨f, g⟩ x : (Σ(n, o) (β x) γ)
  -/
  | pair  : Judge f τ₁
    → IsArrow τ₁ α β m n
    → Judge g t_g
    → Reduces t_g (DCC (Π(m, o) α (γ ∘' (f ∘' Snd'(Sort m, α)))))
    → Judge (DCC ⟦β, γ⟧⟨f, g⟩) (pair.type α β γ m n o)
  -- fst(α, β) : (Σ α β) → α
  | fst   : Judge α t_α
    → Reduces t_α (DCC Sort m)
    → Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m n.succ
    → Judge (DCC Fst(α, β)) (fst.type α β m n)
  | snd'  : Judge α t_α
    → Reduces t_α (DCC Sort m)
    → Judge β t_β
    → Reduces t_β (DCC Sort n)
    → Judge (DCC Snd'(α, β)) (snd'.type α β m n)
  /- snd(α, β) : 
  -/
  | snd   : Judge α t_α
    → Reduces t_α (DCC Sort m)
    → Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m n.succ
    → Judge (DCC Snd(α, β)) (snd.type α β m n)
  | curr' : Judge x τ₁
    → (IsArrow τ₁ (DCC Σ(α, β)) γ (max m n) o)
    → Judge β τ₂
    → IsArrow τ₂ α (DCC Sort n) m n.succ
    → Judge (DCC Λ'(α, β, x)) (curr'.type α β γ m n o)
  /-
    x : Σ(α, β) → γ
    β : α → Sort n
  -/
  | curr  : Judge α t_α
    → Reduces t_α (DCC (Sort m.succ))
    → Judge x t_x
    → Reduces t_x (DCC (Π(m.succ, n) Σ(α, Id(α)) γ))
    → Judge (DCC Λ(α, x)) (curr.type α γ m n)
  /-
    App(γ, β) : (Π(max o n, o)
      (Σ(o, n) (Π(n, o) β γ) `((Π(n, o) β γ), β))
      (γ ∘ (Snd((Π(n, o) β γ), `((Π(n, o) β γ), β)) ∘ Snd(Sort (max o n), Id(Sort (max o n))))))
  -/
  | app_e : Judge α t_α
    → Reduces t_α (DCC Sort m)
    → Judge (DCC App(n, α, β)) (app_e.type α β m n)
  /-
    a : α
    b : β a
    ⟦β⟧(a, b) : Σ α β
  -/
  | coup  : Judge α t_α
    → Reduces t_α (DCC (Sort m))
    → Judge β τ₁
    → IsArrow τ₁ α (DCC (Sort n)) m n.succ
    → Judge (DCC ⟦α, β⟧(,)) (coup.type α β m n)
  -- Can derive dependent quotation
  | quot  : Judge α t_α
    → Reduces t_α (DCC Sort m)
    → Judge β t_β
    → Reduces t_β (DCC Sort n)
    → Judge x t_x
    → Reduces t_x α
    → Judge (DCC `(α, β, x)) (quot.type α β m n)
  | pi    : Judge (DCC Π(m, n)) (Pi.type m n)
  | sigma : Judge α t_α
    → Reduces t_α (DCC Sort m)
    → Judge β τ₁
    → IsArrow τ₁ α (DCC Sort n) m n.succ
    → Judge (DCC Σ(α, β)) (Sigma.type m n)
  | app   : Judge f t_f
    → Reduces t_f (DCC (Π(m, n) α β))
    → Judge x t_x
    → Reduces t_x α
    → Judge (DCC (f x)) (DCC (β ⟦Sort m, Id(Sort m)⟧(α, x)))
  | sort  : Judge (DCC Sort m) (DCC Sort m.succ)
deriving Repr

inductive JudgeConv : Expr → Expr → Type
  | mk : Judge x A → Reduces A B → JudgeConv x B

instance : Std.ToFormat (Judge A B) := ⟨repr⟩

set_option maxHeartbeats 0 in def infer (e : Expr) : Option ((t : Expr) × (Judge e t)) :=
  match e with
  | DCC Π(m, n) => .some ⟨_, .pi⟩
  | DCC Σ(α, β) =>
    match α.infer with
    | .some ⟨t_α, h_t_α⟩ =>
      match h_red₀ : t_α.reduce with
      | DCC Sort m =>
        match β.infer with
        | .some ⟨t_β, h_t_β⟩ =>
          match t_β.is_arrow with
          | .some ⟨α₂, DCC Sort n, m₂, n₂, heq⟩ =>
            if heq₂ : α = α₂ ∧ n₂ = n.succ ∧ m = m₂ then
              have ⟨ha, hb, hc⟩ := heq₂
              .some ⟨_, .sigma h_t_α (reduce_reduces h_red₀) h_t_β (by rw [← ha, hb, ← hc] at heq; exact heq)⟩
            else .none
          | _ => .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC ⟦α, β⟧(,) =>
    match α.infer, β.infer with
    | .some ⟨t_α, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match hred : t_α.reduce with
      | DCC Sort m =>
        match t_β.is_arrow with
        | .some ⟨α₂, DCC Sort n, m₂, n₂, heq₀⟩ =>
          if heq₂ : α = α₂ then
            if heq₄ : n₂ = n.succ then
              if heq₅ : m = m₂ then
                .some ⟨_, .coup h_t_α (reduce_reduces hred) h_t_β (heq₅ ▸ heq₄ ▸ (heq₂ ▸ heq₀))⟩
              else .none
            else .none
          else .none
        | _ => .none
      | _ => .none
    | _, _ => .none
  | DCC Sort m => .some ⟨DCC Sort m.succ, .sort⟩
  | DCC `(α, β, x) =>
    match x.infer, α.infer, β.infer with
    | .some ⟨t_x, h_t_x⟩, .some ⟨t_α, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match hred : t_α.reduce with
      | DCC Sort m =>
        match hred₂ : t_β.reduce with
        | DCC Sort n =>
          if heq : t_x.reduce = α then
            .some ⟨_, .quot h_t_α (reduce_reduces hred) h_t_β (reduce_reduces hred₂) h_t_x (reduce_reduces heq)⟩
          else .none
        | _ => .none
      | _ => none
    | _, _, _ => .none
  | DCC Id(α)  => match α.infer with
    | .some ⟨t_α, h⟩ =>
      match heq : t_α.reduce with
      | DCC Sort m =>
        return ⟨_, .id h (reduce_reduces heq)⟩
      | _ => .none
    | _ => .none
  | DCC Fst(α, β) => match infer α, infer β with
    | .some ⟨t_α, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match heq₀ : t_α.reduce with
      | DCC Sort m =>
        match t_β.is_arrow with
        | .some ⟨α₁, DCC Sort n, m₁, n₁, heq₁⟩ =>
          if heq : α = α₁ ∧ n.succ = n₁ ∧ m = m₁ then
            have ⟨heqa, heqb, heqc⟩ := heq
            .some ⟨_, .fst h_t_α (reduce_reduces heq₀) h_t_β (by rw [← heqa, ← heqb, ← heqc] at heq₁; exact heq₁)⟩
          else .none
        | _ => .none
      | _ => .none
    | _, _ => .none
  | DCC Snd'(α, β) => match infer α, infer β with
    | .some ⟨t_α, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match heq₀ : t_α.reduce with
      | DCC Sort m =>
        match heq₁ : t_β.reduce with
        | DCC Sort n =>
          .some ⟨_, .snd' h_t_α (reduce_reduces heq₀) h_t_β (reduce_reduces heq₁)⟩
        | _ => .none
      | _ => .none
    | _, _ => .none
  | DCC Snd(α, β) =>
    match infer α, infer β with
    | .some ⟨t_α, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match heq₀ : t_α.reduce with
      | DCC Sort m =>
        match t_β.is_arrow with
        | .some ⟨α₁, DCC Sort n, m₁, n₁, heq₁⟩ =>
          if heq : α = α₁ ∧ n.succ = n₁ ∧ m = m₁ then
            have ⟨heqa, heqb, heqc⟩ := heq
            .some ⟨_, .snd h_t_α (reduce_reduces heq₀) h_t_β (by rw [← heqa, ← heqb, ← heqc] at heq₁; exact heq₁)⟩
          else .none
        | _ => .none
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
    | .some ⟨t_α, h_t_α⟩ =>
      match heq₀ : t_α.reduce with
      | DCC Sort m =>
        .some ⟨_, .app_e h_t_α (reduce_reduces heq₀)⟩
      | _ => .none
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
    | .some ⟨t_α, h_t_α⟩, .some ⟨t_x, h_t_x⟩ =>
      match heq₁ : t_α.reduce with
      | DCC Sort m + 1 =>
        match heq₃ : t_x.reduce with
        | (DCC (Π(m₂ + 1, n) Σ(α₁, Id(α₂)) γ₂)) =>
          if heq₂ : m₂ = m ∧ α₁ = α ∧ α = α₂ then
            have ⟨ha, hb, hc⟩ := heq₂
            .some ⟨_, Judge.curr
              h_t_α
              (reduce_reduces heq₁)
              h_t_x
              (ha ▸ hb ▸ hc ▸ (reduce_reduces heq₃))⟩
          else .none
        | _ => .none
      | _ => .none
    | _, _ => .none
  | DCC ⟦β, γ⟧⟨f, g⟩ =>
    match infer f, infer g with
    | .some ⟨t_f, h_t_f⟩, .some ⟨t_g, h_t_g⟩ =>
      match t_f.is_arrow, heq₀ : t_g.reduce with
      | .some ⟨α, β₂, m, n, heq₁⟩,
        (DCC  (Π(m₂, o₂) α₂ (γ₂ ∘' (f₂ ∘' Snd'(Sort m₃, α₃))))) =>
        if heq₃ : m = m₂ ∧ m = m₂ ∧ α = α₂ ∧ γ = γ₂ ∧ f = f₂ ∧ m = m₃ ∧ α = α₃ ∧ β = β₂ then
          have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := heq₃
          .some ⟨_, .pair
            h_t_f
            (h8 ▸ heq₁)
            h_t_g
            (reduce_reduces (by
              rw [← h1, ← h3, ← h4, ← h5, ← h6, ← h7] at heq₀
              exact heq₀))⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC f ∘' g =>
    match g.infer, f.infer with
    | .some ⟨t_g, h_t_g⟩, .some ⟨t_f, h_t_f⟩ =>
      match t_g.is_arrow, heq₀ : t_f.reduce with
      | .some ⟨α, β₁, m, n₁, heq₁⟩, DCC (Π(n₂, o) β₂ γ) =>
        if heq₃ : β₁ = β₂ ∧ n₁ = n₂ then
          .some ⟨_, .comp' h_t_g heq₁ h_t_f (reduce_reduces (by
            have ⟨heqa, heqb⟩ := heq₃
            rw [← heqa, ← heqb] at heq₀
            exact heq₀))⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC ⟦α, β, γ⟧∘ =>
    match α.infer, β.infer, γ.infer with
    | .some ⟨t_α, h_t_α⟩, .some ⟨t_β, h_t_β⟩, .some ⟨t_γ, h_t_γ⟩ =>
      match heq₀ : t_α.reduce with
      | DCC Sort m =>
        match t_β.is_arrow, t_γ.is_arrow with
        | .some ⟨α₂, DCC Sort n, m₂, n₂, heqa⟩, .some ⟨DCC Σ(α₃, β₂), DCC Sort o, mn, o₂, heqb⟩ =>
          if heq : α₂ = α ∧ α₃ = α ∧ m₂ = m ∧ n₂ = n.succ ∧ mn = (max m n) ∧ o₂ = o.succ ∧ β₂ = β then
            have ⟨ha, hb, hc, hd, he, hf, hg⟩ := heq
            .some ⟨_, .comp h_t_α (reduce_reduces heq₀) h_t_β (hd ▸ hc ▸ ha ▸ heqa) h_t_γ (he ▸ hf ▸ hg ▸ hb ▸ heqb)⟩
          else .none
        | _, _ => .none
      | _ => .none
    | _, _, _ => .none
  | DCC (f x) => match f.infer, x.infer with
    | .some ⟨t_f, h_f⟩, .some ⟨t_x, h_x⟩ =>
      match heq₀ : t_f.reduce, heq₁ : t_x.reduce with
      | DCC (Π(m, n) α₁ β), α₂ =>
        if heq : α₁ = α₂ then
          .some ⟨(DCC (β ⟦Sort m, Id(Sort m)⟧(α₁, x))), .app h_f (reduce_reduces heq₀) h_x (reduce_reduces (heq ▸ heq₁))⟩
        else .none
      | _, _ => .none
    | _, _ => .none

def infer_conv (e : Expr) : Option ((t : Expr) × JudgeConv e t) :=
  match infer e with
  | .some ⟨t, h⟩ =>
    .some ⟨t.reduce, ⟨h, reduce_reduces rfl⟩⟩
  | _ => .none

def id_well_typed (h_t_α : Judge α (DCC Sort m)) (h_t_x : Judge x α) : JudgeConv (DCC (Id(α) x)) α.reduce := by
  apply JudgeConv.mk
  · apply Judge.app
    apply Judge.id
    · assumption
    · exact reduce_reduces (by simp [reduce, step?]; rfl)
    · exact reduce_reduces (by simp [id.type]; rfl)
    · assumption
    · exact reduce_reduces rfl
  · exact reduce_reduces reduce_congr_quot

def comp'_preservation (h : JudgeConv (DCC ((f ∘' g) x)) α) : JudgeConv (DCC (f (g x))) α :=
  match h with
  | ⟨h_t, h_red⟩ => by
    cases h_t with
    | app h_t_f h_r_t_f h_t_x h_r_t_x =>
      cases h_t_f with
      | comp' h_t_g h_arrow_g h_t_f h_r_t_f' =>
        have ha := h_r_t_f.complete
        have hb := h_r_t_x.complete
        have hc := h_red.complete
        rw [comp'.type, reduce_congr_pi] at ha
        cases ha
        simp_all
        have h_α_norm : α.IsNormAff := reduce_norm hc
        rw [reduce_step (by simp [step?]; aesop)] at hc
        cases h_arrow_g with
        | mk a =>
          refine ⟨Judge.app h_t_f h_r_t_f' (Judge.app h_t_g a h_t_x ?_) ?_, ?_⟩
          apply reduce_reduces
          rw [h]

def id_preservation (h : JudgeConv (DCC (Id(α) x)) α.reduce) : (JudgeConv x α.reduce) :=
  match h with
  | ⟨h_t, h_red⟩ => by
    cases h_t with
    | app h_t_id b h_t_x d =>
      cases h_t_id with
      | id =>
        cases reduce_arrow b.complete
        exact ⟨h_t_x, by assumption⟩

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
  | sort =>
    unfold infer
    rfl
  | sigma h_t_α h_red₁ h_t_β h_arrow₁ ih₁ ih₂ =>
    have ha := h_red₁.complete
    have hb := h_arrow₁.complete
    unfold infer
    rw [ih₁, ih₂]
    simp
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq =>
        rw [heq] at hb
        cases hb
        simp
        split
        rfl
      case h_2 h =>
        exact (h _ _ _ _ h_arrow₁ hb).elim
    case h_2 h =>
      exact (h _ ha).elim
  | quot h_t_α h_red_α h_t_β h_red_β h_t_x h_red_x ih₁ ih₂ ih₃ =>
    have ha := h_red_α.complete
    have hb := h_red_β.complete
    have hc := h_red_x.complete
    unfold infer
    rw [ih₁, ih₂, ih₃]
    simp
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq =>
        rw [heq] at hb
        cases hb
        simp [hc]
      case h_2 h =>
        exact (h _ hb).elim
    case h_2 h =>
      exact (h _ ha).elim
  | coup h_t_α h_red₁ h_t_β h_arrow₁ ih₁ ih₂ =>
    have ha := h_red₁.complete
    have hb := h_arrow₁.complete
    unfold infer
    rw [ih₁, ih₂]
    simp
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq =>
        rw [heq] at hb
        cases hb
        simp
      case h_2 h =>
        exact (h _ _ _ _ h_arrow₁ hb).elim
    case h_2 h =>
      exact (h _ ha).elim
  | app_e h_t_α h_red₁ ih =>
    have ha := h_red₁.complete
    unfold infer
    rw [ih]
    simp
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      rfl
    case h_2 h =>
      exact (h _ ha).elim
  | snd' h_t_α h_red₁ h_t_β h_red₂ ih₁ ih₂ =>
    have ha := h_red₁.complete
    have hb := h_red₂.complete
    unfold infer
    rw [ih₁, ih₂]
    simp
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq =>
        rw [heq] at hb
        cases hb
        rfl
      case h_2 h =>
        exact (h _ hb).elim
    case h_2 h =>
      exact (h _ ha).elim
  | snd h_t_α h_red₁ h_t_β h_arrow₁ ih₁ ih₂ =>
    have ha := h_red₁.complete
    have hb := h_arrow₁.complete
    unfold infer
    rw [ih₁, ih₂]
    simp
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq =>
        rw [heq] at hb
        cases hb
        simp
        split
        rfl
      case h_2 h =>
        exact (h _ _ _ _ h_arrow₁ hb).elim
    case h_2 h =>
      exact (h _ ha).elim
  | fst h_t_α h_red₁ h_t_β h_arrow₁ ih₁ ih₂ =>
    have ha := h_red₁.complete
    have hb := h_arrow₁.complete
    unfold infer
    rw [ih₁, ih₂]
    simp
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq =>
        rw [heq] at hb
        cases hb
        simp
        split
        rfl
      case h_2 h =>
        exact (h _ _ _ _ h_arrow₁ hb).elim
    case h_2 h =>
      exact (h _ ha).elim
  | curr' h_t_x h_arrow₁ h_t_β h_arrow₂ ih₁ ih₂ =>
    have ha := h_arrow₁.complete
    have hb := h_arrow₂.complete
    unfold infer
    rw [ih₁, ih₂]
    simp
    split
    case h_1 heq₁ heq₂ =>
      rw [heq₁] at ha
      rw [heq₂] at hb
      cases ha
      cases hb
      simp
      split
      rfl
    case h_2 h =>
      exact (h _ _ _ _ _ h_arrow₁ _ _ _ _ h_arrow₂ ha hb).elim
  | curr h_t_α h_red₁ h_t_x h_red₂ ih₁ ih₂ =>
    have ha := h_red₁.complete
    have hb := h_red₂.complete
    unfold infer
    rw [ih₁, ih₂]
    simp
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq =>
        rw [heq] at hb
        cases hb
        simp
        split
        rfl
      case h_2 h =>
        exact (h _ _ _ _ _ hb).elim
    case h_2 h =>
      exact (h _ ha).elim
  | pair h_t_f h_arrow₁ h_t_g h_red₁ ih₁ ih₂ =>
    have ha := h_arrow₁.complete
    have hb := h_red₁.complete
    unfold infer
    simp [ih₁, ih₂]
    split
    case h_1 heq₁ heq₂ =>
      rw [heq₁] at ha
      rw [heq₂] at hb
      cases ha
      cases hb
      simp
      split
      rfl
    case h_2 h =>
      exact (h _ _ _ _ h_arrow₁ _ _ _ _ _ _ _ ha  hb).elim
  | comp h_t_α h_red_α h_t_β h_arrow₁ h_t_γ h_arrow₂ ih₁ ih₂ ih₃ =>
    have ha := h_red_α.complete
    have hb := h_arrow₁.complete
    have hc := h_arrow₂.complete
    unfold infer
    simp [ih₁, ih₂, ih₃]
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq₁ heq₂ =>
        rw [heq₁] at hb
        rw [heq₂] at hc
        cases hb
        cases hc
        simp
        split
        rfl
      case h_2 h =>
        exact (h _ _ _ _ h_arrow₁ _ _ _ _ _ h_arrow₂ hb hc).elim
    case h_2 h =>
      exact (h _ ha).elim
  | comp' h_t_g h_arrow₁ h_t_f h_red ih₁ ih₂ =>
    have ha := h_red.complete
    have hb := h_arrow₁.complete
    unfold infer
    simp [ih₁, ih₂]
    split
    case h_1 heq_arrow heq_red =>
      rw [heq_arrow] at hb
      rw [heq_red] at ha
      cases hb
      cases ha
      simp
    case h_2 h =>
      exact (h _ _ _ _ h_arrow₁ _ _ _ _ hb ha).elim
  | pi => rfl
  | app h_t_f h_red_f h_t_x h_red_x ih₁ ih₂ =>
    have ha := h_red_f.complete
    have hb := h_red_x.complete
    unfold infer
    simp [ih₁, ih₂]
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      cases hb
      simp
    case h_2 h =>
      exact (h _ _ _ _ ha).elim
  | id h_t_α h_red ih =>
    have ha := h_red.complete
    unfold infer
    simp [ih]
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      rfl
    case h_2 h =>
      exact (h _ ha).elim
  | flip h_t_x h_arrow₁ h_arrow₂ ih =>
    have ha := h_arrow₁.complete
    have hb := h_arrow₂.complete
    unfold infer
    simp [ih]
    split
    case h_1 heq =>
      rw [heq] at ha
      cases ha
      split
      case h_1 heq =>
        rw [heq] at hb
        cases hb
        simp
      case h_2 h => exact (h _ _ _ _ h_arrow₂ hb).elim
    case h_2 h => exact (h _ _ _ _ h_arrow₁ ha).elim
  
  /-| quot _ _ _ ih₁ ih₂ ih₃ => unfold infer; rw [ih₁, ih₂, ih₃]; simp
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
    aesop-/

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

def JudgeConv.decide : JudgeConv e t ⊕ (JudgeConv e t → PLift False) :=
  if h : (infer e).isSome then
    if heq : ((infer e).get h).fst.reduce = t then
      .inl ⟨((infer e).get h).snd, reduce_reduces heq⟩
    else .inr fun ⟨ha, hb⟩ => by
      have h := ha.complete
      simp_all
      exact (heq hb.complete).elim
  else .inr fun ⟨ha, hb⟩ => by
    have h := ha.complete
    simp_all

def judge_sound (_h_t : Expr.infer e = .some ⟨t, h⟩) : e.Judge t := h

end Expr

/-
def point_free_id (h_t_α : α.Judge (DCC Sort m)) (h_t_x : x.Judge α) : (DCC (#(Expr.mk_id m) α x)).Judge α := by
  unfold Expr.mk_id
  have h := Expr.Judge.app 
  
  sorry
-/
