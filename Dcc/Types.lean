import Dcc.Ast

namespace Expr

/-
β receives (x : α)

DCC (Σ(Λ(Sort m, Fst(`(Sort m, `(Sort m, α)), α), β)) α)
-/
@[simp] def coup.type (β : Expr) : Expr :=
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
def mk_fstc (β : Expr) : Expr :=
  DCC (Fst(`(⊤, β)) ∗)

def mk_sndc (β : Expr) : Expr :=
  DCC (Snd(`(⊤, β)) ∗)

syntax "Fstc(" expr,* ")" : expr
syntax "Sndc(" expr,* ")" : expr

syntax "(" expr ":" expr ")" "→" expr : expr

macro_rules
  | `(DCC Fstc($β:expr)) => `(DCC (Fst(`(⊤, $β)) ∗))
  | `(DCC Sndc($β:expr)) => `(DCC (Snd(`(⊤, $β)) ∗))
  | `(DCC Coup($β:expr)) => `(DCC (Σ(`(⊤, $β)) ∗))

def arrow (α β : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), Λ(Sort m, Id(Sort m), `(Coup(Id(Sort m)), β))) α)

macro_rules
  | `(DCC ($α:expr : Sort $m) → $β:expr) => `(arrow (DCC $α) (DCC $β) $m)

@[grind →, grind ., simp] def App'.type (α f_α f_β env : Expr) (n : Level) : Expr :=
  let t_f := DCC (Π(f_α, f_β) env)
  DCC (Π(Id(Sort n), `(Sort n, (f_β env) ∘ Snd'(t_f, α))) Coup(`(t_f, α)))

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
  | (DCC App'(α, β))          => comb "App'" [α.toFormat, β.toFormat]
  | (DCC App(m, n, f_α, f_β)) => comb "App" [Std.format m, Std.format n, f_α.toFormat, f_β.toFormat]
  | (DCC Λ(α, β, e))          => comb "Λ" [α.toFormat, β.toFormat, e.toFormat]
  | (DCC Π(α, β))             => comb "Π" [α.toFormat, β.toFormat]
  | (DCC ⟦m, α, β, γ⟧⟨a, b⟩)  =>
    let pts := (bbracket (sepD [Std.format m, α.toFormat, β.toFormat, γ.toFormat]))
    let pts_length := match pts.pretty.splitOn "\n" |>.head? with
    | .some line => line.length
    | .none      => 0
    pts ++ (angle (sepD [a.toFormat, b.toFormat] (indent := pts_length)))
  | (DCC ⟦β⟧(a, b))           =>
    comb (bbracket (sepD [β.toFormat])) [a.toFormat, b.toFormat]
  | DCC Coup(β)               => comb "Coup" [β.toFormat]
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

#eval (DCC (Fstc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0)))

def Top.type : Expr :=
  DCC Sort 0

def Tintro.type : Expr :=
  DCC ⊤

def Bot.type : Expr :=
  DCC Sort 0


def fst.f_β.type (α δ : Expr) (m n o : Level) : Expr :=
  (DCC (δ : Sort o) → ((α : Sort m) → Sort n))

def id.type (α : Expr) (m : Level) : Expr :=
  DCC (α : Sort m) → α

/-
f_β : δ → α → Sort n
Fst(f_β) : ∀ (env : δ) (s : Σ(f_β) env), α
-/

def fst.type (α f_β δ : Expr) (o : Level) : Expr :=
  DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(f_β), Λ(δ, Σ(f_β), `(Coup(Σ(f_β)), α))) ∘ Snd'(Sort o, δ))) δ)

/-
Snd(f_β) : ∀ (env : δ) (s : Σ(f_β) env), f_β env (Fst(f_β) env s)
-/
def snd.type (f_β δ : Expr) (o : Level) : Expr :=
  DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(f_β), Subst(f_β, Fst(f_β))) ∘ Snd'(Sort o, δ))) δ)

/-
Λ(β, x) y z → x ⟦β⟧(y, z)

β receives x

x : ∀ (s : coup.type α β m), γ s
-/
def curr.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Π(β, Λ(α, β, γ)))) α) -- weaken α, keep x

/-
β : α → Sort n
-/
def curr.β.type (α : Expr) (m n : Level) : Expr :=
  DCC (α : Sort m) → Sort n

/-
Nondependent quotation.

x : α
`(β, x) : β → α
-/
def quot.type (α β : Expr) (n : Level) : Expr :=
  DCC (β : Sort n) → α

/-
f : (Π(Id(Sort m), f_β) α)
g : (Π(Id(Sort m), f_γ) α)

⟦α, f_β, f_γ⟧⟨f, g⟩ : (Π(Id(Sort m), Σ(Λ(α, (f_β α), f_γ ∘ Fstc(α, (f_β α))))) α)
-/
def pair.type (α f_β f_γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Σ(Λ(α, (f_β α), f_γ ∘ Fstc((f_β α)))))) α)

def comp'.type (α β γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, (γ β) ∘ g)) α)

def App.type (δ : Expr) (u_δ o : Level) : Expr :=
  DCC (δ : Sort u_δ) → Sort o

def App'.type₂ (f_α f_β δ : Expr) (u_δ u_α u_β : Level) : Expr :=
  DCC (Π(Id(Sort u_δ), `(Sort u_δ, App(u_α, u_β, f_α, f_β))) δ)

def snd'.type (α β : Expr) (m n : Level) : Expr :=
  DCC (Coup(`(α, β)) : Sort max m n) → β

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
def Pi.type (α : Expr) (m o : Level) : Expr :=
  DCC (α : Sort m) → Sort o

/-
(Π(Id(Sort 3), `(Sort 3, Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), (`(⊤, `(Coup(Id(Sort 2)), Sort 2)) ∗))))) Sort 2)
-/

@[simp] def Pi.f_β.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(f_α), Sort o))))) α))

/-def Pi.f_β.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(m, α, f_α), Sort o))))) α))-/

def pair.β.type (α : Expr) (m n : Level) : Expr :=
  DCC (Sort m : Sort m.succ) → ((α : Sort m) → Sort n)

/-
β : δ → α → Sort n
x : ∀ (env : δ) (x : α), γ env x
Subst(x, Fst(β)) : ∀
-/
def Subst₁.type (β γ δ : Expr) (o : Level) : Expr :=
  (DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(Σ(β), Subst(γ, Fst(β))) ∘ Snd'(Sort o, δ))) δ))

/-
(Π(Id(Sort o), `(_a, Π(f_α, Λ(δ, _b, Π(((App(Id(_c), `(_d, _e), Λ(_f, _g, `((Σ(`(_h, _i)) _j), Sort n))) _k) _l), Λ(_m, ((App(Id(_n), `(_o, _p), Λ(_q, _r, `(_s, _t))) _u) f_β), `(_v, Sort p))))))) _w)
-/

/-
(Π(Id(Sort m), `(_a,Π(f_α, Λ(δ, _b, Π(((App(Id(Sort _c), `(Sort _d, _e), Λ(_f, f_g, `((Σ(`(_g, _h)) _j), Sort n))) _k) f_β), ((App(Id(_l), `(_mm, _n), Λ(_o, _p, `((Σ(`(_q, _r)) _s), _t))) _u) f_γ)))))) _v)
-/

/-
Σ(f_β)

f_β : δ → α → Sort n

Σ(f_β) : δ → Sort n
-/
def Sigma.type (δ : Expr) (m n o : Level) : Expr :=
  DCC (δ : Sort o) → Sort max m n

end Expr
