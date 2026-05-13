import Dcc.Attrs
import Dcc.Ast

namespace Expr

syntax "(" expr ":" expr ")" "→" expr : expr
syntax "(" ":" expr ")" "→" expr : expr

@[dcc_judge] abbrev arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), Λ(Sort m, Id(Sort m), `(Coup(Id(Sort m)), β))) α)

macro_rules
  | `(DCC ($α:expr : Sort $m) → $β:expr) => `(arrow (DCC $α) (DCC $β) $m)
  | `(DCC (: Sort $m) → $β:expr) => `(DCC Λ(Sort $m, Id(Sort $m), `(Coup(Id(Sort $m)), $β)))

@[dcc_judge, inline]
abbrev arrow.matcher (t : Expr) : Option ((α β : Expr) × (m : Level) × PULift.{1, 0} (t = (DCC (α : Sort m) → β))) :=
  match heq₀ : t with
  | DCC (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
    if heq₁ : t = (DCC (α : Sort m) → β) then
      .some ⟨α, β, m, ⟨by rw [← heq₀, heq₁]⟩⟩
    else
      .none
  | _ => .none

def is_arrow (e : Expr) : Bool :=
  (arrow.matcher e).isSome

/-
Subst(x, Snd(f_β) env) ⟦β⟧(y, z)

= x y z

f_β env : ∀ (x : α), β x

x : ∀ (x : α) (y : β x), γ x y

Subst(x, Snd(f_β) env) : ∀ (s : Σ(f_β) env), Subst(γ, Snd(f_β) env)
-/
@[dcc_judge] abbrev Subst₂.type (f_β env γ : Expr) (n : Level) : Expr :=
  DCC (Π(Id(Sort n), `(Sort n, Subst(γ, (Snd(f_β) env)))) (Σ(f_β) env))

@[dcc_judge] abbrev Subst₂.x.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Π(β, γ))) α)

@[dcc_judge] abbrev Top.type : Expr :=
  DCC Sort 0

@[dcc_judge] abbrev Tintro.type : Expr :=
  DCC ⊤

@[dcc_judge] abbrev Bot.type : Expr :=
  DCC Sort 0

/-
TODO: x needs to depend on (env : δ)
-/
@[dcc_judge] abbrev fst.f_β.type (α δ : Expr) (m n o : Level) : Expr :=
  (DCC (δ : Sort o) → ((α : Sort m) → Sort n))

@[dcc_judge] abbrev snd.f_β.type (δ _β : Expr) (o : Level) : Expr :=
  (DCC (Π(Id(Sort o), _β) δ))

@[dcc_judge] abbrev id.type (α : Expr) (m : Level) : Expr :=
  DCC (α : Sort m) → α

/-
β : ∀ (x : α), Sort n
Fstc(β) : ∀ (s : Coup(β)), α
-/
@[dcc_judge] abbrev fstc.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Coup(β) : Sort (max m n)) → α

/-
β : ∀ (x : α), Sort n
Sndc(β) : ∀ (s : Coup(β)), (β ∘ Fstc(β)) s
-/
@[dcc_judge] abbrev sndc.type (β : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)), `(Sort (max m n), β ∘' Fstc(β))) Coup(β))

/-
f_β : δ → α → Sort n
Fst(f_β) : ∀ (env : δ) (s : Σ(f_β) env), α
-/

@[dcc_judge] abbrev fst.type (α f_β δ : Expr) (n o : Level) : Expr :=
  DCC (Π(Id(Sort o), `(Sort o, (Π(Id(Sort n), Λ(Sort n, Id(Sort n), `(Coup(Id(Sort n)), α))) ∘' Σ(f_β)))) δ)

/-
Snd(f_β) : ∀ (env : δ) (s : Σ(f_β) env), f_β env (Fst(f_β) env s)

snd : ∀ (env : δ) (s : Σ(f_β) env), Fst(f_β) env
-/
@[dcc_judge] abbrev snd.type (f_β δ : Expr) (o : Level) : Expr :=
  DCC (Π(Id(Sort o), `(Sort o, Π(Σ(f_β), Subst(f_β, Fst(f_β))))) δ)

/-
Λ(β, x) y z → x ⟦β⟧(y, z)

β receives x

x : ∀ (s : coup.type α β m), γ s
-/
@[dcc_judge] abbrev curr.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Π(β, Λ(α, β, γ)))) α) -- weaken α, keep x

/-
β : α → Sort n
-/
@[dcc_judge] abbrev curr.β.type (f_α x_α : Expr) (m n : Level) : Expr :=
  (DCC (Π(f_α, (: Sort m) → Sort n) x_α))

/-
Nondependent quotation.

x : α
`(β, x) : β → α
-/
@[dcc_judge] abbrev quot.type (α β : Expr) (n : Level) : Expr :=
  DCC (β : Sort n) → α

/-
⟨f, g⟩ x = (f x, g x (f x))

f : ∀ (x : α), β x
g : ∀ (x : α) (y : β x), γ x y
⟨f, g⟩ : ∀ (x : α), Σ(Λ(α, β, γ)) x
-/
@[dcc_judge] abbrev pair.type (α γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Σ(γ))) α)

@[dcc_judge] abbrev comp'.type (α γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, γ ∘' g)) α)

/-
g : ∀ (x : α), Σ(Λ(α, `(α, α), f_β ∘ Fstc(`(α, α)))) x
f : ∀ (s : Coup(f_β)), `(Sort n, γ)

f ∘ g : ∀ (x : α), γ ∘ g
-/

@[dcc_judge] abbrev comp.g.type (α f_β : Expr) (m : Level) :=
  (DCC (Π(Id(Sort m), Σ(Λ(α, `(α, α), f_β ∘' Fstc(`(α, α))))) α))

@[dcc_judge] abbrev comp.f.type (f_β f_γ : Expr) (n : Level) :=
  (DCC (Π(Id(Sort n), f_γ) Coup(f_β)))

@[dcc_judge] abbrev comp.type (α γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, γ ∘ g)) α)

@[dcc_judge] abbrev snd'.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Coup(`(α, β)) : Sort max m n) → β

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
@[dcc_judge] abbrev Pi.type (α : Expr) (m o : Level) : Expr :=
  DCC (α : Sort m) → Sort o

/-
(Π(Id(Sort 3), `(Sort 3, Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), (`(⊤, `(Coup(Id(Sort 2)), Sort 2)) ∗))))) Sort 2)
-/

@[dcc_judge] abbrev Pi.f_β.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(f_α), Sort o))))) α))

/-abbrev Pi.f_β.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(m, α, f_α), Sort o))))) α))-/

@[dcc_judge] abbrev pair.β.type (α : Expr) (m n : Level) : Expr :=
  DCC (Sort m : Sort m.succ) → ((α : Sort m) → Sort n)

/-
β : ∀ (env : δ) (x : f_α env), Sort n
x : ∀ (env : δ) (x : α), γ env x
Subst(x, Fst(β)) : ∀
-/
@[dcc_judge] abbrev Subst₁.type (β γ δ : Expr) (o : Level) : Expr :=
  (DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(β), Subst(γ, Fst(β))) ∘' Snd'(Sort o, δ))) δ))
-- (Π(Id(Sort 1), `(Sort 1, Π(Id(Sort 0), Λ(Sort 0, Id(Sort 0), `(Coup(Id(Sort 0)), Sort 2))))) Sort 0)
@[dcc_judge] abbrev Subst₁.x.type (α γ δ : Expr) (m o : Level) : Expr :=
  (DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), `(Coup(Id(Sort o)), (Π(Id(Sort m), γ) α)))) δ))

/-
f_β : ∀ (env : δ) (x : α), Sort n
x : ∀ (env : δ) (y : β),
β = f_β env x
Subst(x, Snd(f_β)) : ∀ (env : δ) (s : Σ(f_β) env),
-/

/-
Σ(f_β)

f_β : δ → α → Sort n

Σ(f_β) : δ → Sort n
-/
@[dcc_judge] abbrev Sigma.type (δ : Expr) (m n o : Level) : Expr :=
  DCC (δ : Sort o) → Sort max m n

@[dcc_judge] abbrev Coup.type (m n : Level) : Expr :=
  DCC Sort max m n

def toFormat (e : Expr) (pretty : Bool := False) : Std.Format :=
  let sepD (l : List Std.Format) (sep : Std.Format := ",") (indent : ℕ := 2) : Std.Format :=
    .nest indent (.fill (.joinSep l (sep ++ .line)))
  let paren (s : Std.Format) : Std.Format :=
    .bracket "(" (.fill s) ")"
  let angle (s : Std.Format) : Std.Format :=
    .bracket "⟨" (.fill s) "⟩"
  let bbracket (s : Std.Format) : Std.Format :=
    .bracket "⟦" (.fill s) "⟧"

  let comb (pre : Std.Format) (points : List Std.Format) : Std.Format :=
    .group (pre ++ (paren (sepD points (indent := pre.pretty.length))))

  match heq₀ : e with
  | (DCC ⊤)                   => "⊤"
  | (DCC ⊥)                   => "⊥"
  | (DCC ∗)                   => "∗"
  | (DCC `(β, x))             => comb "`" [β.toFormat pretty, x.toFormat pretty]
  | (DCC Id(α))               => comb "Id" [α.toFormat pretty]
  | (DCC Subst(β, x))         => comb "Subst" [β.toFormat pretty, x.toFormat pretty]
  | (DCC Sort m)              => "Sort " ++ (Std.format m)
  | (DCC Fstc(β))             => comb "Fstc" [β.toFormat pretty]
  | (DCC Fst(β))              => comb "Fst" [β.toFormat pretty]
  | (DCC Sndc(β))             => comb "Sndc" [β.toFormat pretty]
  | (DCC Snd(β))              => comb "Snd" [β.toFormat pretty]
  | (DCC Snd'(α, β))          => comb "Snd'" [α.toFormat pretty, β.toFormat pretty]
  | (DCC Λ(α, β, e))          => comb "Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC Π(α, β))             =>
    comb "Π" [α.toFormat pretty, β.toFormat pretty]
  | (DCC ⟨a, b⟩)              => (angle (sepD [a.toFormat pretty, b.toFormat pretty] (indent := 1)))
  | (DCC ⟦β⟧(a, b))           =>
    comb (bbracket (sepD [β.toFormat pretty])) [a.toFormat pretty, b.toFormat pretty]
  | (DCC Coup(β))             => comb "Coup" [β.toFormat pretty]
  | (DCC Σ(β))                => comb "Σ" [β.toFormat pretty]
  | (DCC f ∘ g)               =>
    sepD [f.toFormat pretty, g.toFormat pretty] " ∘"
  | (DCC f ∘' g)               =>
    sepD [f.toFormat pretty, g.toFormat pretty] " ∘'"
  | (DCC (f x))               =>
    if pretty then
      match heq₁ : (DCC (f x)) with
      | DCC (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
        have _h : sizeOf α < sizeOf e := by
          rw [heq₁] at heq₀
          rw [heq₀]
          simp [sizeOf, Expr._sizeOf_1]
          grind
        have _h : sizeOf β < sizeOf e := by
          rw [heq₁] at heq₀
          rw [heq₀]
          simp [sizeOf, Expr._sizeOf_1]
          grind
        sepD [(paren (sepD [(α.toFormat pretty), s!"Sort {m}"] " :")), β.toFormat pretty] " →"
      | _ => (paren (f.toFormat pretty ++ (.indentD (x.toFormat pretty))))
    else (paren (f.toFormat pretty ++ (.indentD (x.toFormat pretty))))
termination_by e

instance instToFormat : Std.ToFormat Expr := ⟨toFormat (pretty := true)⟩
instance instToString : ToString Expr     := ⟨toString ∘ toFormat (pretty := true)⟩
instance instRepr : Repr Expr := ⟨Function.const _ ∘ toFormat (pretty := false)⟩

instance instOptToFormat : Std.ToFormat (Option Expr) := ⟨fun me =>
  match me with
  | .none => Std.format me
  | .some e =>
    let l := "(some".length.succ
    .group ("(some " ++ (.fill (.nest l (e.toFormat (pretty := true)))) ++ ")")⟩

#eval (DCC ((Sort 1 : Sort 2) → Sort 2))

end Expr
