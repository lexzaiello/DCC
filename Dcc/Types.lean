import Dcc.Ast

namespace Expr

syntax "(" gen_dcc ":" gen_dcc ")" "→" gen_dcc : gen_dcc
syntax "(" ":" gen_dcc ")" "→" gen_dcc : gen_dcc

macro_rules
  | `(DCC[$ty:ident] ($α:gen_dcc : Sort $m) → $β:gen_dcc) =>
    `(DCC[$ty:ident] (Π(Id(Sort $m), Λ(Sort $m, Id(Sort $m), `(Coup(Id(Sort $m)), $β))) $α))
  | `(DCC[$ty:ident] (: Sort $m) → $β:gen_dcc) =>
    `(DCC[$ty:ident] Λ(Sort $m, Id(Sort $m), `(Coup(Id(Sort $m)), $β)))

inductive Arrow : Expr → Expr → Level → Expr → Type
  | simple : Arrow α β m (DCC (Π(Id(Sort m), `(Sort m, `(α, β))) α))
  | dep    : Arrow α β m (DCC ((α : Sort m) → β))
  | eval   : Arrow α β m (DCC (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α))
  | eval'  : Arrow α β m (DCC (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α))

@[dcc_judge, inline]
def read_arrow (τ : Expr) : Option ((α β : Expr) × (m : Level) × (Arrow α β m τ)) :=
  match heq : τ with
  | DCC (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
    if heq₁ : τ = (DCC (α : Sort m) → β) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .dep⟩
    else .none
  | (DCC (Π(Id(Sort m), `(_a, `(_b, β))) α)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, `(α, β))) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .simple⟩
    else .none
  | (DCC (Π(Id(Sort m), `(_m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .eval⟩
    else .none
  | (DCC (Π(Id(Sort m), `(_m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .eval'⟩
    else .none
  | _ => .none

@[dcc_judge, inline]
def read_arrow₁ (τ α : Expr) : Option ((β : Expr) × (m : Level) × (Arrow α β m τ)) :=
  match heq : τ with
  | DCC (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) _d) =>
    if heq₁ : τ = (DCC (α : Sort m) → β) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .dep⟩
    else .none
  | (DCC (Π(Id(Sort m), `(_a, `(_b, β))) _d)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, `(α, β))) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .simple⟩
    else .none
  | (DCC (Π(Id(Sort m), `(_m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) _α)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .eval⟩
    else .none
  | (DCC (Π(Id(Sort m), `(_m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) _α)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .eval'⟩
    else .none
  | _ => .none

@[dcc_judge]
theorem Arrow.read₁_complete (h : Arrow α β m τ) : τ.read_arrow₁ α = .some ⟨β, m, h⟩ := by
  cases h <;> simp [read_arrow₁]


@[dcc_judge, inline]
def view_arrow (τ α β : Expr) (m : Level) : Option (Arrow α β m τ) :=
  match heq : τ with
  | DCC (Π(__a, Λ(_a, _b, `(_c, _d))) _e) =>
    if heq₁ : τ = (DCC (α : Sort m) → β) then
      .some <| by rw [← heq, heq₁]; exact .dep
    else .none
  | (DCC (Π(__a, `(_a, `(_b, _c))) _d)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, `(α, β))) α)) then
      .some <| by rw [← heq, heq₁]; exact .simple
    else .none
  | (DCC (Π(_m₁, `(_m, Eval(_a, _b, `(τ_x, `(τ_y, _β))) ∘∘ _g)) _α)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) then
      .some (by rw [← heq, heq₁]; exact .eval)
    else .none
  | (DCC (Π(_m₁, `(_m, Eval(_a, _b, `(τ_x, `(τ_y, _β))) ∘' _g)) _α)) =>
    if heq₁ : τ = (DCC (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) then
      .some (by rw [← heq, heq₁]; exact .eval')
    else .none
  | _ => .none

-- (Π(Id(Sort 0), `(Sort 0, Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 1))))) ⊤)
inductive Pi.f_β.type (f_α δ : Expr) (o : Level) : Level → Expr → Type
  | canon : Pi.f_β.type f_α δ o n
    (DCC (Π(Id(Sort o), `(Sort o, Π(f_α, Λ(δ, f_α, `(Coup(f_α), Sort n))))) δ))
  | semi  : Pi.f_β.type f_α δ o n (DCC (Π(Id(Sort o), `(Sort o, Π(f_α, `(δ, `(f_α₂, Sort n))))) δ))
  | arrow : Pi.f_β.type f_α δ o n
    (DCC (Π(Id(Sort o), `(Sort o, `(δ, (Π(Id(Sort m), `(Sort m, `(α, Sort n))) α)))) δ))

@[dcc_judge]
def view_pi_f_β (τ f_α δ : Expr) (o : Level) : Option ((n : Level) × (Pi.f_β.type f_α δ o n τ)) :=
  match heq₁ : τ with
  | (DCC (Π(__b, `(_a, Π(__a, Λ(_b, _c, `(_d, Sort n))))) _e)) =>
    if heq₂ : τ = (DCC (Π(Id(Sort o), `(Sort o, Π(f_α, Λ(δ, f_α, `(Coup(f_α), Sort n))))) δ)) then
      .some ⟨n, by rw [← heq₁, heq₂]; exact .canon (f_α := f_α) (δ := δ) (o := o) (n := n)⟩
    else .none
  | (DCC (Π(_a, `(_b, `(_c, (Π(Id(Sort m), `(_d, `(_e, Sort n))) α)))) _f)) =>
    if heq₂ : τ = (DCC (Π(Id(Sort o), `(Sort o, `(δ, (Π(Id(Sort m), `(Sort m, `(α, Sort n))) α)))) δ)) then
      .some ⟨n, by rw [← heq₁, heq₂]; exact .arrow (f_α := f_α) (δ := δ) (o := o) (n := n)⟩
    else .none
  | (DCC (Π(_a, `(_b, Π(_c, `(_d, `(f_α₂, Sort n))))) _e)) =>
    if heq₂ : τ = (DCC (Π(Id(Sort o), `(Sort o, Π(f_α, `(δ, `(f_α₂, Sort n))))) δ)) then
      .some ⟨n, by rw [← heq₁, heq₂]; exact .semi⟩
    else .none
  | _ => .none

@[dcc_judge]
theorem Pi.f_β.type.complete (h : Pi.f_β.type f_α δ o n τ) : view_pi_f_β τ f_α δ o = .some ⟨n, h⟩ := by
  cases h <;> simp [view_pi_f_β]

@[dcc_judge] abbrev Pi.f_β.type' (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(f_α), Sort o))))) α))

@[dcc_judge]
theorem Arrow.view_complete (h : Arrow α β m τ) : τ.view_arrow α β m = .some h := by
  cases h <;> simp [view_arrow]

@[dcc_judge]
theorem Arrow.read_complete (h : Arrow α β m τ) : τ.read_arrow = .some ⟨α, β, m, h⟩ := by
  cases h <;> simp [read_arrow]

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
  DCC (Π(Id(Sort o), `(Sort o, (Π(Id(Sort n), Λ(Sort n, Id(Sort n), `(Coup(Id(Sort n)), α))) ∘' Σ(α, f_β)))) δ)

/-
Λ(β, x) y z → x ⟦β⟧(y, z)

β receives x

x : ∀ (s : coup.type α β m), γ s
-/
@[dcc_judge] abbrev curr.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Π(β, Λ(α, β, γ)))) α) -- weaken α, keep x

@[dcc_judge] abbrev curr'.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Π(!<β>, !Λ(α, β, γ)))) !(α)) -- weaken α, keep x

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
@[dcc_judge] abbrev pair.type (α β γ : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, Σ(β, γ) ∘' *(α))) !(α))

@[dcc_judge] abbrev comp'.type (α γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, γ ∘' g)) α)

/-
g : ∀ (x : α), Σ(Λ(α, `(α, α), f_β ∘ Fstc(`(α, α)))) x
f : ∀ (s : Coup(f_β)), `(Sort n, γ)

f ∘ g : ∀ (x : α), γ ∘ g
-/

@[dcc_judge] abbrev comp.g.type (α β : Expr) (m : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Σ(`(α, α), Λ(α, `(α, α), `(Coup(`(α, α)), β))) ∘' *(α))) !(α)))

/-
(some (Π(Id(Sort 1),
   `(Sort 1,
     (Σ(`(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))), `(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0))) ∘'
        *(Coup(`(⊤, Sort 0))))))
   !(Coup(`(⊤, Sort 0)))))
`(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0))
-/

@[dcc_judge] abbrev comp₂.g.type (α β : Expr) (m : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Σ(`(α, α), Λ(α, `(α, α), β ∘' Fstc(`(α, α)))) ∘' *(α))) !(α)))

inductive Comp₂.g.type : Expr → Expr → Level → Expr → Type
  | dep    : Comp₂.g.type α β m (comp₂.g.type α β m)
  | simple : Comp₂.g.type α β m (DCC (Π(Id(Sort m), `(Sort m, Σ(`(α, α), `(α, β)) ∘' *(α))) !(α)))

def read_comp₂_g_type (τ : Expr) : Option ((α β : Expr) × (m : Level) × (Comp₂.g.type α β m τ)) :=
  match τ with
  | (DCC (Π(Id(Sort m), `(_a, Σ(_b, Λ(_c, _d, β ∘' _e)) ∘' _f)) !(α))) =>
    if heq : (DCC (Π(Id(Sort m), `(_a, Σ(_b, Λ(_c, _d, β ∘' _e)) ∘' _f)) !(α))) = (comp₂.g.type α β m) then
      .some ⟨α, β, m, (by
        cases heq
        exact .dep )⟩
    else .none
  | (DCC (Π(Id(Sort m), `(_a, Σ(_b, `(_c, β)) ∘' _e)) !(α))) =>
    if heq : (DCC (Π(Id(Sort m), `(_a, Σ(_b, `(_c, β)) ∘' _e)) !(α))) = (DCC (Π(Id(Sort m), `(Sort m, Σ(`(α, α), `(α, β)) ∘' *(α))) !(α))) then
      .some ⟨α, β, m, (by
        cases heq
        exact .simple )⟩
    else .none
  | _ => none

@[dcc_judge]
theorem Comp₂.g.type.complete (h : Comp₂.g.type α β m τ) : τ.read_comp₂_g_type = .some ⟨α, β, m, h⟩ := by
  cases h <;> simp [read_comp₂_g_type]

@[dcc_judge] abbrev comp.f.type (f_β f_γ : Expr) (n : Level) :=
  (DCC (Π(Id(Sort n), f_γ) Coup(f_β)))

@[dcc_judge] abbrev comp₂.f.type (β f_γ : Expr) (n : Level) :=
  (DCC (Π(Id(Sort n), f_γ) Coup(β)))

/-
(Π(Id(Sort 1),
   `(Sort 1, Eval(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0), `(Coup(`(⊤, Sort 0)), `(Sort 0, Sort 0)))))
   Coup(`(Coup(`(⊤, Sort 0)), Sort 0)))
-/

@[dcc_judge] abbrev comp.type (α γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, γ ∘ g)) !(α))

@[dcc_judge] abbrev comp₂.type (α γ g : Expr) (m : Level) : Expr :=
  DCC (Π(Id(Sort m), `(Sort m, γ ∘∘ g)) !(α))

@[dcc_judge] abbrev eql.type (f_α δ : Expr) (o : Level) : Expr :=
  (DCC (Π(Id(Sort o),
      `(Sort o, Π(!<f_α>, Λ(!(δ), !<f_α>, `(Coup(!<f_α>), Sort 0))))) !(δ)))

@[dcc_judge] abbrev refl.type (f_α δ : Expr) (o : Level) : Expr :=
  (DCC (Π(Id(Sort o), `(Sort o, Π(!<f_α>, Eql(f_α)))) !(δ)))

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
@[dcc_judge] abbrev Pi.type (α : Expr) (o n : Level) : Expr :=
  DCC (α : Sort o) → Sort n

/-abbrev Pi.f_β.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(m, α, f_α), Sort o))))) α))-/

@[dcc_judge] abbrev pair.β.type (α : Expr) (m n : Level) : Expr :=
  DCC (Sort m : Sort m.succ) → ((α : Sort m) → Sort n)

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

/-
f_α : δ → Sort m
Eval(f_α, f_β) : ∀ (s : ∀ (env : δ), (Σ(f_α, f_β) env)) (env : δ),
  f_β env (Fstc(f_β env) (s env))

Fstc ({ f, g } x) = f x

Eval(f_α, f_β) f x = (Snd ∘ f) x

Eval(f_α, f_β) : ∀ (s : ∀ (env : δ), (Σ(f_α, f_β) env)) (env : δ),
  f_β env (Fstc(f_β env) (s env))

Eval takes M and N explicitly?

Eval(M, N)

but then we can't destructure couple back into data.
Need actual eval.

Eval(x) ⟦β⟧(y, z) = x y z?

x : ∀ (x : α) (y : β x), γ x y
Eval(x) : ∀ (c : Coup(β)), Eval(γ) c

This is canonical.
-/

@[dcc_judge] abbrev Eval.type (α β γ : Expr) (m n : Level) : Expr :=
  DCC (Π(Id(Sort (max m n)), `(Sort (max m n), Eval(α, β, γ))) Coup(β))

open Std (ToFormat Format format) in
def toFormat (e : Expr) (pretty : Bool := False) : Std.Format :=
  let sepD (l : List Std.Format) (sep : Std.Format := ",") (indent : ℕ := 2) : Std.Format :=
    .nest indent (.fill (.joinSep l (sep ++ .line)))
  let paren (s : Std.Format) : Std.Format :=
    .bracket "(" (.fill s) ")"
  let angle (s : Std.Format) : Std.Format :=
    .bracket "⟨" (.fill s) "⟩"
  let angle_hard (s : Std.Format) : Std.Format :=
    .bracket "<" (.fill s) ">"
  let bbracket (s : Std.Format) : Std.Format :=
    .bracket "⟦" (.fill s) "⟧"

  let comb (pre : Std.Format) (points : List Std.Format) (paren : Std.Format → Std.Format := paren) : Std.Format :=
    .group (pre ++ (paren (sepD points (indent := min pre.pretty.length 30))))

  match heq₀ : e with
  | (DCC ⊤)                   => "⊤"
  | (DCC ⊥)                   => "⊥"
  | (DCC ∗)                   => "∗"
  | (DCC !<f>)                => comb "!" (paren := angle_hard) [f.toFormat pretty]
  | (DCC $<f>)                => comb "$" (paren := angle_hard) [f.toFormat pretty]
  | (DCC &(x))                => "&" ++ (paren (x.toFormat pretty))
  | (DCC *(x))                => "*" ++ (paren (x.toFormat pretty))
  | (DCC !(x))                => "!" ++ (paren (x.toFormat pretty))
  | (DCC Eval(α, β, x))       => comb "Eval" [α.toFormat pretty, β.toFormat pretty, x.toFormat pretty]
  | (DCC `(β, x))             => comb "`" [β.toFormat pretty, x.toFormat pretty]
  | (DCC Id(α))               => comb "Id" [α.toFormat pretty]
  | (DCC Sort m)              => "Sort " ++ (Std.format m)
  | (DCC Fstc(β))             => comb "Fstc" [β.toFormat pretty]
  | (DCC Sndc(β))             => comb "Sndc" [β.toFormat pretty]
  | (DCC Λ(α, β, e))          => comb "Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC !Λ(α, β, e))         => comb "!Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC Π(α, β))             =>
    comb "Π" [α.toFormat pretty, β.toFormat pretty]
  | (DCC ⟦β⟧⟨a, b⟩)           =>
    comb (paren := angle) (bbracket (sepD [β.toFormat pretty])) [a.toFormat pretty, b.toFormat pretty]
  | (DCC ⟦β⟧(a, b))           =>
    comb (bbracket (sepD [β.toFormat pretty])) [a.toFormat pretty, b.toFormat pretty]
  | (DCC Coup(β))             => comb "Coup" [β.toFormat pretty]
  | (DCC Σ(α, β))             => comb "Σ" [α.toFormat pretty, β.toFormat pretty]
  | (DCC x = y)               => sepD [x.toFormat pretty, y.toFormat pretty] " ="
  | (DCC Eql(f_α))            => comb "Eql" [f_α.toFormat pretty]
  | (DCC refl(f_α))           => comb "refl" [f_α.toFormat pretty]
  | (DCC f ∘ g)               =>
    paren (sepD [f.toFormat pretty, g.toFormat pretty] " ∘")
  | (DCC f ∘∘ g)               =>
    paren (sepD [f.toFormat pretty, g.toFormat pretty] " ∘∘")
  | (DCC f ∘' g)               =>
    paren (sepD [f.toFormat pretty, g.toFormat pretty] " ∘'")
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

end Expr

open Std (ToFormat Format format) in
instance (priority := high) instToFormat : Std.ToFormat (Expr) :=
  ⟨Expr.toFormat (pretty := true)⟩
open Std (ToFormat Format format) in
instance (priority := high) instToString : ToString Expr :=
  ⟨toString ∘ Expr.toFormat (pretty := true)⟩
open Std (ToFormat Format format) in

def Expr.raw_repr (e : Expr) : Std.Format :=
  repr e

open Std (ToFormat Format format) in
instance (priority := high) instRepr : Repr Expr :=
  { reprPrec := fun e _ =>
    Expr.toFormat e (pretty := true) }

instance instOptToFormat : Std.ToFormat (Option Expr) := ⟨fun me =>
  match me with
  | .none => Std.format me
  | .some e =>
    let l := "(some".length.succ
    .group ("(some " ++ (.fill (.nest l (e.toFormat (pretty := true)))) ++ ")")⟩

#eval (DCC ((Sort 1 : Sort 2) → Sort 2))
