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

/-
TODO: Replace App with

let s_β := Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(δ, Π(f_α, f_β)))
let t_s := Σ(s_β)
Π(t_s, Λ(δ, t_s, Subst(f_β, `(Sort n, (f_β env) ∘ Snd'(t_f, α)))

...
-/

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
