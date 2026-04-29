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

@[dcc_judge, grind →, grind .] abbrev App'.type (α f_α f_β env : Expr) (n : Level) : Expr :=
  let t_f := DCC (Π(f_α, f_β) env)
  DCC (Π(Id(Sort n), `(Sort n, (f_β env) ∘ Snd'(t_f, α))) Coup(`(t_f, α)))

/-
TODO: Need to put this back in, remove App vs App' distinction.

f_β depends on the environment and x. x depends on the environment,
but not fst.

assuming

Subst(f_β, Snd(...)) env (y, z) = f_β env y z

@[dcc_judge, grind →, grind .] abbrev App.type (f_α f_β δ : Expr) (o : Level) : Expr :=
  let t_x_y_β := DCC Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(Π(f_α, f_β)))
  let t_x_y   := DCC Σ(t_x_y_β)
  DCC (Π(Id(Sort o), `(Sort o, Π(t_x_y, Subst(f_β, Snd(t_x_y_β))))) δ)
-/

/-
Subst(x, Snd(f_β)) refers to the "simply-typed" Snd.
As in, Snd is only determined by the environment, not fst.

x : ∀ (env : δ) (x : f_t_snd env), β(env, x)

x : (Π(Id(Sort o), `(Sort o, Π(f_t_snd, β))) δ)

so s : Σ(Λ(δ, f_α, f_β ∘ Fstc(f_α))

x   : ∀ (env : δ) (x : f_α₁ env), β env x
x   : (Π(Id(Sort o), `(Sort o, Π(f_α₁, β))) δ)
f_β : (Π(Id(Sort o), `(Sort o, Π(f_α₂, Λ(δ, f_α₂, `(Coup(f_α₂), Sort n))))) δ)

f_β : ∀ (env : δ) (x : f_α x), Sort n

Subst(x, Snd(f_β)) env (y, z) = x env z

f_α₁ = f_α₂

Sigma snd type:
f_β : ∀ (env : δ) (x : f_α₂ env), Sort n
-/
@[dcc_judge] abbrev Subst₂.type (f_α f_β β δ : Expr) (o : Level) : Expr :=
  let f_β_s := DCC Λ(δ, f_α, f_β ∘ Fstc(f_α))
  DCC (Π(Id(Sort o), `(Sort o, Π(Σ(f_β_s),
    Subst(β, Snd(f_β_s))))) δ)

@[dcc_judge] abbrev Subst₂.x.type (f_t_snd β δ : Expr) (o : Level) : Expr :=
  DCC (Π(Id(Sort o), `(Sort o, Π(f_t_snd, β))) δ)

/-
TODO: Replace App with

let s_β := Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(δ, Π(f_α, f_β)))
let t_s := Σ(s_β)
Π(t_s, Λ(δ, t_s, Subst(f_β, `(Sort n, (f_β env) ∘ Snd'(t_f, α)))

...
-/

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
f : (Π(Id(Sort m), f_β) α)
g : (Π(Id(Sort m), f_γ) α)

⟦α, f_β, f_γ⟧⟨f, g⟩ : (Π(Id(Sort m), Σ(Λ(α, (f_β α), f_γ ∘ Fstc(α, (f_β α))))) α)
-/
@[dcc_judge] abbrev pair.type (α f_β f_γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Σ(Λ(α, (f_β α), f_γ ∘ Fstc((f_β α)))))) α)

@[dcc_judge] abbrev comp'.type (α β γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, (γ β) ∘ g)) α)

@[dcc_judge, grind →, grind .] abbrev App.type (f_α f_β δ : Expr) (o : Level) : Expr :=
  let t_x_y_β := DCC Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(Π(f_α, f_β)))
  let t_x_y   := DCC Σ(t_x_y_β)
  DCC (Π(Id(Sort o), `(Sort o, Π(t_x_y, Subst(f_β, Snd(t_x_y_β))))) δ)

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
@[dcc_judge] abbrev Sigma.type (δ : Expr) (m n o : Level) : Expr :=
  DCC (δ : Sort o) → Sort max m n

end Expr
