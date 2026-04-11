import Dcc.CC.Ast
import Dcc.CC.Step2

def arrow (α β : Expr) (m n : Level) : Expr :=
  DCC (Π(m, n) α `(Sort n, Σ(Sort m, Id(Sort m)), β))

def Pi.type (m n : Level) : Expr :=
  arrow (DCC Sort m)
    (arrow
      (arrow
        (DCC Σ(Sort m, Id(Sort m)))
        (DCC Sort n) m.succ n.succ)
      (DCC Sort n) n.succ n.succ) m.succ n.succ


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
γ is a function of (β, x)
good primitive for this is to be able to map over the snd component.

γ ∘ (map_fst g)

map_fst f (a, b) = (f a, b)
we might need pattern matching again for this.

I don't really want to add another primitive, though.

maybe we can derive this?

we can actually just do


-/
-- TODO: composition doesn't like the dependent Snd here.
-- can make nondependent Snd.
def comp.type (α β γ g : Expr) (m n o : Level) : Expr :=
  DCC (Π(m, o) α ((Λ(Id(Sort n), γ) β) ∘ (g ∘ Snd'(Sort m, α))))

/-
⟦α, γ⟧⟨f, x⟩ : Π(m, (max n o)) α (() ∘ f
-/

def pair.type (α β γ : Expr) (m n o : Level) : Expr :=
  (arrow α (DCC Σ(β, γ)) m (max n o))

def fst.type (α β : Expr) (m n : Level) : Expr :=
  (arrow (DCC Σ(α, β)) α (max m n) m)

def snd'.type (α β : Expr) (m n : Level) : Expr :=
  (DCC (Π(max m n, n)
    (Σ(α, `(Sort n, α, β)))
    `(Sort n, Σ(α, `(Sort n, α, β)), β)))

def snd.type (α β : Expr) (m n : Level) : Expr :=
  (DCC (Π(max m n, n)
    Σ(α, β) (β ∘ Fst(α, β) ∘ Snd'(Sort (max m n), Σ(α, β)))))

/-
α is type of x in (f, x)
f : ∀ α, β x
-/
def app_e.type (α β : Expr) (m n : Level) : Expr :=
  let t_f := DCC (Π(m, n) α β)
  let t_x := DCC `(Sort m, t_f, α)

  DCC (Π(max m n, n)
      Σ(t_f, t_x)
      ((Λ(Id(Sort m), β) α) ∘ (Snd(t_f, t_x) ∘ Snd'(Sort (max m n), Σ(t_f, t_x)))))

/-
x : Π (Σ α β) γ
Λ(x) : Π(m, o) α ((Flip(Π(n, o)) γ) ∘ β)
-/
def curr.type (α β γ : Expr) (m n o : Level) : Expr :=
  (DCC (Π(m, o) α ((Flip(Π(n, o)) γ) ∘ (β ∘ Snd'(Sort m, α)))))

def coup.type (α β : Expr) : Expr :=
  (DCC Σ(α, β))

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
    → Judge (DCC f ∘ g) (comp.type α β γ g m n o).reduce.fst
  /-
    ⟦m, α, γ⟧⟨f, g⟩ x = ⟦(γ ⟦Id(Sort m)⟧(α, x))⟧(f x, g x)
    f : α → β
    g : ∀ (x : α), γ x

    ⟦m, α, γ⟧⟨f, g⟩ x : (Σ(n, o) (β x) γ)
  -/
  | pair  : Judge f (arrow α β m n)
    → Judge g (DCC (Π(m, o) α (γ ∘ (f ∘ Snd'(Sort m, α)))))
    → Judge (DCC ⟦γ⟧⟨f, g⟩) (pair.type α β γ m n o).reduce.fst
  -- fst(α, β) : (Σ α β) → α
  | fst   : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Fst(α, β)) (fst.type α β m n).reduce.fst
  | snd'  : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Judge (DCC Snd'(α, β)) (snd'.type α β m n).reduce.fst
  /- snd(α, β) : 
  -/
  | snd   : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Snd(α, β)) (snd.type α β m n).reduce.fst
  /-
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
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Λ(β, x)) (curr.type α β γ m n o).reduce.fst
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
  | sigma : Judge α (DCC Sort m)
    → Judge β (arrow α (DCC Sort n) m n.succ)
    → Judge (DCC Σ(α, β)) (Sigma.type m n)
  | app   : Judge f (DCC (Π(m, n) α β))
    → Judge x α
    → Judge (DCC (f x)) (DCC (β ⟦Id(Sort m)⟧(α, x))).reduce.fst
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
    match α.infer, β.infer with
    | .some ⟨DCC Sort m, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match t_β.match_arrow with
      | .some ⟨α₂, DCC Sort n, m₂, n₂, ⟨heq⟩⟩ =>
        if heq₂ : α = α₂ ∧ n₂ = n.succ ∧ m = m₂ then
          have ⟨ha, hb, hc⟩ := heq₂
          .some ⟨_, .sigma h_t_α (by rw [heq, ← ha, hb, ← hc] at h_t_β; exact h_t_β)⟩
        else .none
      | _ => .none
    | _, _ => .none
  | DCC ⟦β⟧(a, b) =>
    match β.infer with
    | .some ⟨t_β, h_t_β⟩ =>
      match t_β.match_arrow with
      | .some ⟨α, DCC Sort n, m, n₂, ⟨heq₀⟩⟩ =>
        match a.infer, b.infer with
        | .some ⟨α₂, h_t_a⟩, .some ⟨t_b, h_t_b⟩ =>
          if heq₂ : α = α₂ then
            if heq₃ : t_b = (DCC (β a)).reduce.fst then
              if heq₄ : n₂ = n.succ then
                .some ⟨_, .coup (heq₄ ▸ (heq₀ ▸ h_t_β)) (heq₂ ▸ h_t_a) (heq₃ ▸ h_t_b)⟩
              else .none
            else .none
          else .none
        | _, _ => .none
      | _ => .none
    | _ => .none
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
      match t_β.match_arrow with
      | .some ⟨α₁, DCC Sort n, m₁, n₁, ⟨heq₁⟩⟩ =>
        if heq : α = α₁ ∧ n.succ = n₁ ∧ m = m₁ then
          have ⟨heqa, heqb, heqc⟩ := heq
          .some ⟨_, .fst h_t_α (by rw [heq₁, ← heqa, ← heqb, ← heqc] at h_t_β; exact h_t_β)⟩
        else .none
      | _ => .none
    | _, _ => .none
  | DCC Snd'(α, β) => match infer α, infer β with
    | .some ⟨DCC Sort m, h_t_α⟩, .some ⟨DCC Sort n, h_t_β⟩ =>
      .some ⟨_, .snd' h_t_α h_t_β⟩
    | _, _ => .none
  | DCC Snd(α, β) => match infer α, infer β with
    | .some ⟨DCC Sort m, h_t_α⟩, .some ⟨t_β, h_t_β⟩ =>
      match t_β.match_arrow with
      | .some ⟨α₁, DCC Sort n, m₁, n₁, ⟨heq₁⟩⟩ =>
        if heq : α = α₁ ∧ n.succ = n₁ ∧ m = m₁ then
          have ⟨heqa, heqb, heqc⟩ := heq
          .some ⟨_, .snd h_t_α (by rw [heq₁, ← heqa, ← heqb, ← heqc] at h_t_β; exact h_t_β)⟩
        else .none
      | _ => .none
    | _, _ => .none
  | DCC Flip(x) =>
    match x.infer with
    | .some ⟨t_x, h_t_x⟩ =>
      match t_x.match_arrow with
      | .some ⟨α, βγ, m, o, ⟨heq⟩⟩ =>
        match βγ.match_arrow with
        | .some ⟨β, γ, n, o₂, ⟨heq₂⟩⟩ =>
          if heq₃ : o = o₂ then
            .some ⟨_, .flip (by rw [heq, heq₂, ← heq₃] at h_t_x; exact h_t_x)⟩
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC App(n, α, β) =>
    match α.infer with
    | .some ⟨DCC Sort m, h_t_α⟩ =>
      .some ⟨_, .app_e h_t_α⟩
    | _ => .none
  | DCC Λ(β, x) =>
    match heq₀ : x.infer, β.infer with
    | .some ⟨DCC (Π(mn, o) Σ(α, β₂) γ), h_t_x⟩, .some ⟨t_β, h_t_β⟩ =>
      match t_β.match_arrow with
      | .some ⟨α₂, DCC Sort n, m₂, n₂, ⟨heq⟩⟩ =>
        if heq₂ : max m₂ n = mn ∧ β = β₂ ∧ α = α₂ ∧ n.succ = n₂ then
          have ⟨ha, hb, hc, hd⟩ := heq₂
          .some ⟨_, .curr (m := m₂) (n := n) (o := o) (α := α) (β := β) (γ := γ)
            (by simp_all; rw [← hc]; exact h_t_x)
            (by simp_all; rw [← hb, ← heq]; exact h_t_β)⟩
        else .none
      | _ => .none
    | _, _ => .none
  | DCC ⟦γ⟧⟨f, g⟩ =>
    match infer f, infer g with
    | .some ⟨t_f, h_t_f⟩, .some ⟨t_g, h_t_g⟩ =>
      match t_f.match_arrow, t_g with
      | .some ⟨α, β, m, n, ⟨heq₁⟩⟩,
        (DCC  (Π(m₂, o₂) α₂ (γ₂ ∘ (f₂ ∘ Snd'(Sort m₃, α₃))))) =>
        if heq₃ : m = m₂ ∧ m = m₂ ∧ α = α₂ ∧ γ = γ₂ ∧ f = f₂ ∧ m = m₃ ∧ α = α₃ then
          have ⟨h1, h2, h3, h4, h5, h6, h7⟩ := heq₃
          .some ⟨_, .pair
            (heq₁ ▸ h_t_f)
            (by
              rw [← h1, ← h3, ← h4, ← h5, ← h6, ← h7] at h_t_g
              exact h_t_g)⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC f ∘ g =>
    match g.infer, f.infer with
    | .some ⟨t_g, h_t_g⟩, .some ⟨t_f, h_t_f⟩ =>
      match t_g.match_arrow, t_f with
      | .some ⟨α, β₁, m, n₁, ⟨heq₁⟩⟩, DCC (Π(n₂, o) β₂ γ) =>
        if heq₃ : β₁ = β₂ ∧ n₁ = n₂ then
          .some ⟨_, .comp (heq₁ ▸ h_t_g) (by
            have ⟨heqa, heqb⟩ := heq₃
            rw [← heqa, ← heqb] at h_t_f
            exact h_t_f)⟩
        else .none
      | _, _ => .none
    | _, _ => .none
  | DCC (f x) => match f.infer, x.infer with
    | .some ⟨DCC (Π(m, n) α₁ β), h_f⟩, .some ⟨α₂, h_x⟩ =>
      if heq : α₁ = α₂ then
        .some ⟨(DCC (β ⟦Id(Sort m)⟧(α₁, x))).reduce.fst, .app h_f (heq ▸ h_x)⟩
      else .none
    | _, _ => .none

#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Id(Sort 1) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (⟦Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Fst(Sort 2, Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Snd(Sort 2, Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Σ(Sort 1, Id(Sort 1))))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Π(1, 1) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC Id(Sort 1))
#eval (Std.format ∘ Sigma.fst) <$> infer (id.type (DCC Sort 0) 1)
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (`(Sort 1, Sort 1, Sort 0) (Sort 0)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC ((`(Sort 1, Sort 2, Sort 0) ∘ Id(Sort 2)) (Sort 1)))
#eval (Std.format ∘ Sigma.fst) <$> infer (DCC (Λ(Id(Sort 2), Id((Σ(Sort 2,  Id(Sort 2))))) (Sort 1) (Sort 0)))

/-
⟦Id(Sort 2)⟧⟨Id(Sort 2), `(Sort 1, Sort 2, Sort 0)⟩
-/

#eval (Std.format ∘ Sigma.fst) <$> infer (DCC Id(Sort 2) ∘ Id(Sort 2))

def test_pair : Option Expr :=
  let f := DCC Id(Sort 2)
  let g := DCC Id(Sort 2) ∘ Id(Sort 2)
  -- γ receives (f x)
  /-
    Id(Sort 2) ∘ Id(Sort 2) :
    (some ((Π(3, 3) Sort 2) (Λ(Id(Sort 3),`(Sort 3, ((Σ(4, 3) Sort 3) Id(Sort 3)), Sort 2)) Sort 2)
      ∘ Id(Sort 2) ∘ Snd(Sort 3, Id(Sort 3))))
  -/
  let γ := DCC (Λ(Id(Sort 3),`(Sort 3, Σ(Sort 3, Id(Sort 3)), Sort 2)) Sort 2)
  let e := DCC (⟦γ⟧⟨f, g⟩ (Sort 1))
  Sigma.fst <$> e.infer

#eval test_pair.format

def test_app : Option Expr := do
  let f := DCC Id(Sort 2) ∘ Id(Sort 2)
  let x := DCC Sort 1
  let β ←
    match ← Sigma.fst <$> f.infer with
    | DCC (Π(_m, _n) _α β) => .some β
    | _ => .none

  let α := DCC Sort 2
  let t_f ← Sigma.fst <$> infer f
  let γ := DCC (`(Sort 3, t_f, α))

  dbg_trace γ
  dbg_trace t_f
  dbg_trace Sigma.fst <$> t_f.infer

  dbg_trace (Std.format ∘ Sigma.fst) <$> (DCC ⟦γ⟧(f, x)).infer

  Sigma.fst <$> (DCC (App(2, α, β) ⟦γ⟧(f, x))).infer

theorem Judge.complete (h_t : Judge e t) : infer e = .some ⟨t, h_t⟩ := by
  induction h_t with
  | curr _ _ ih₁ ih₂ =>
    unfold infer
    rw [ih₁, ih₂]
    split
    rename_i heq₁ heq₂
    simp at heq₁
    simp at heq₂
    simp_all
    have ⟨ha, hb⟩ := heq₂
    have ⟨hc, hd⟩ := heq₁
    cases ha
    simp [arrow, match_arrow]
    rename_i heq₁_1 h_t_β
    simp_all only [and_self, exists_true_left]
    obtain ⟨left, right⟩ := heq₁_1
    obtain ⟨left, right_1⟩ := left
    obtain ⟨left, right_2⟩ := left
    obtain ⟨left, right_3⟩ := left
    obtain ⟨left_1, right_2⟩ := right_2
    subst right_1 left right_3 left_1 right_2
    simp_all only [heq_eq_eq, cast_eq]
    subst hb
    split
    rename_i heq₂ ha hb hc hd
    simp_all only [heq_eq_eq, Nat.succ_eq_add_one, and_self]
  | pair _ _ ih₁ ih₂ =>
    simp [infer, ih₁, ih₂, arrow, match_arrow]
    split
    rename_i heq₃ h1 h2 h3 h4 h5
    simp_all only [and_self]
  | coup _ _ _ ih₁ ih₂ ih₃ => simp [infer, ih₁, ih₂, ih₃, arrow, match_arrow]
  | quot _ _ _ ih₁ ih₂ ih₃ => simp [infer, ih₁, ih₂, ih₃]
  | pi => simp [infer]
  | sigma _ _ ih₁ ih₂ =>
    simp [infer, ih₁, ih₂, arrow, match_arrow]
    split
    rfl
  | app_e _ ih => simp [infer, ih]
  | flip _ ih => simp [infer, ih, arrow, match_arrow]
  | comp _ _ ih₁ ih₂ =>
    simp [infer, ih₁, ih₂, arrow, match_arrow]
    split
    rename_i heq₃ heqa heqb
    simp_all only [and_self]
  | id h_t_α ih => simp [infer, ih]
  | fst _ _ ih₁ ih₂ =>
    simp [infer, ih₁, ih₂, arrow, match_arrow]
    simp_all only [Nat.succ_eq_add_one]
    split
    rename_i heq heqa heqb heqc
    simp_all only [Nat.succ_eq_add_one, and_self]
  | snd _ _ ih₁ ih₂ =>
    simp [infer, ih₁, ih₂, arrow, match_arrow]
    simp_all only [Nat.succ_eq_add_one]
    split
    rename_i heq heqa heqb heqc
    simp_all only [Nat.succ_eq_add_one, and_self]
  | snd' _ _ ih₁ ih₂ => simp [infer, ih₁, ih₂]
  | sort => simp [infer]
  | app a b ih₁ ih₂ => simp [infer, ih₁, ih₂]

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

end Expr
