import Dcc.Attrs
import Dcc.Ast

namespace Expr

/-
β receives (x : α)

DCC (Σ(Λ(Sort m, Fst(`(Sort m, `(Sort m, α)), α), β)) α)
-/
@[dcc_judge] abbrev coup.type (β : Expr) : Expr :=
  DCC (Σ(`(⊤, β)) ∗)

syntax "Coup(" expr,* ")" : expr

/-
The main Fst is indexed by the environment map and the environment:

Fst(f_β, env).

Fstc is a derived version of Fst more closely aligned with traditional couples.

Fstc(α, β) ⟦β⟧(x, y) : α
Sndc(α, β) ⟦β⟧(x, y) : β (α, x)

Snd' is specifically for couples with this encoding.

Curry is also designed for couples with the (α, x) β encoding.
That is, β in ⟦β⟧(x, y) receives (α, x)
-/
@[dcc_judge] abbrev mk_fstc (β : Expr) : Expr :=
  DCC (Fst(`(⊤, β)) ∗)

@[dcc_judge] abbrev mk_sndc (β : Expr) : Expr :=
  DCC (Snd(`(⊤, β)) ∗)

syntax "Fstc(" expr,* ")" : expr
syntax "Sndc(" expr,* ")" : expr

syntax "(" expr ":" expr ")" "→" expr : expr

macro_rules
  | `(DCC Fstc($β:expr)) => `(DCC (Fst(`(⊤, $β)) ∗))
  | `(DCC Sndc($β:expr)) => `(DCC (Snd(`(⊤, $β)) ∗))
  | `(DCC Coup($β:expr)) => `(DCC (Σ(`(⊤, $β)) ∗))

@[dcc_judge] abbrev arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), Λ(Sort m, Id(Sort m), `(Coup(Id(Sort m)), β))) α)

macro_rules
  | `(DCC ($α:expr : Sort $m) → $β:expr) => `(arrow (DCC $α) (DCC $β) $m)

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

@[dcc_judge] abbrev id.type (α : Expr) (m : Level) : Expr :=
  DCC (α : Sort m) → α

/-
f_β : δ → α → Sort n
Fst(f_β) : ∀ (env : δ) (s : Σ(f_β) env), α
-/

@[dcc_judge] abbrev fst.type (α f_β δ : Expr) (o : Level) : Expr :=
  DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(f_β), Λ(δ, Σ(f_β), `(Coup(Σ(f_β)), α))) ∘ Snd'(Sort o, δ))) δ)

/-
Snd(f_β) : ∀ (env : δ) (s : Σ(f_β) env), f_β env (Fst(f_β) env s)
-/
@[dcc_judge] abbrev snd.type (f_β δ : Expr) (o : Level) : Expr :=
  DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(f_β), Subst(f_β, Fst(f_β))) ∘ Snd'(Sort o, δ))) δ)

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
@[dcc_judge] abbrev curr.β.type (α : Expr) (m n : Level) : Expr :=
  DCC (α : Sort m) → Sort n

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

@[dcc_judge] abbrev comp'.type (α β γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, (γ β) ∘ g)) α)

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
  (DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(β), Subst(γ, Fst(β))) ∘ Snd'(Sort o, δ))) δ))

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

def toFormat (e : Expr) : Std.Format :=
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

  match e with
  | (DCC ⊤)                   => "⊤"
  | (DCC ⊥)                   => "⊥"
  | (DCC ∗)                   => "∗"
  | (DCC `(β, x))             => comb "`" [β.toFormat, x.toFormat]
  | (DCC Id(α))               => comb "Id" [α.toFormat]
  | (DCC Subst(β, x))         => comb "Subst" [β.toFormat, x.toFormat]
  | (DCC Sort m)              => "Sort " ++ (Std.format m)
  | (DCC Fstc(β))             => comb "Fstc" [β.toFormat]
  | (DCC Fst(β))              => comb "Fst" [β.toFormat]
  | (DCC Sndc(β))             => comb "Sndc" [β.toFormat]
  | (DCC Snd(β))              => comb "Snd" [β.toFormat]
  | (DCC Snd'(α, β))          => comb "Snd'" [α.toFormat, β.toFormat]
  | (DCC Λ(α, β, e))          => comb "Λ" [α.toFormat, β.toFormat, e.toFormat]
  | (DCC Π(α, β))             => comb "Π" [α.toFormat, β.toFormat]
  | (DCC ⟨a, b⟩)              => (angle (sepD [a.toFormat, b.toFormat] (indent := 1)))
  | (DCC ⟦β⟧(a, b))           =>
    comb (bbracket (sepD [β.toFormat])) [a.toFormat, b.toFormat]
  | (DCC Coup(β))             => comb "Coup" [β.toFormat]
  | (DCC Σ(β))                => comb "Σ" [β.toFormat]
  | (DCC f ∘ g)               =>
    sepD [f.toFormat, g.toFormat] " ∘"
  | (DCC (f x))               => (paren (f.toFormat ++ (.indentD x.toFormat)))

instance instToFormat : Std.ToFormat Expr := ⟨toFormat⟩
instance instToString : ToString Expr     := ⟨toString ∘ toFormat⟩
instance instRepr : Repr Expr := ⟨Function.const _ ∘ toFormat⟩

instance instOptToFormat : Std.ToFormat (Option Expr) := ⟨fun me =>
  match me with
  | .none => Std.format me
  | .some e =>
    let l := "(some".length.succ
    .group ("(some " ++ (.fill (.nest l e.toFormat)) ++ ")")⟩

end Expr
