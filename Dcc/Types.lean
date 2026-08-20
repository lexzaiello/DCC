import Dcc.Ast
import Dcc.Attrs

namespace GenericExpr

inductive Arrow.{u} {τ : Type u} : GenericExpr (τ := τ) → GenericExpr (τ := τ) → Level → GenericExpr (τ := τ) → Type u
  | simple : Arrow α β m (DCC? (Π(Id(Sort m), `(Sort m, `(α, β))) α))
  | dep    : Arrow α β m (DCC? (Π(Id(Sort m), Λ(Sort m, Id(Sort m), `(Coup(Id(Sort m)), β))) α))
  | dep'   : Arrow α β m (DCC? (Π(Id(Sort m), !Λ(Sort m, Id(Sort m), `(!(Coup(Id(Sort m))), β))) α))
  | eval   : Arrow α β m (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α))
  | eval'  : Arrow α β m (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α))
  | curr   : Arrow α β m (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, β))) ∘∘ _g)) α))

/-
(Π(Id(Sort 2),
             `(Sort 2,
               Π(!<Snd(`(⊤, Sort 1))>,
                 !Λ(Coup(`(⊤, Sort 1)), Snd(`(⊤, Sort 1)), `(!(Coup(Snd(`(⊤, Sort 1)))), Sort 2)))))
             !(Coup(`(⊤, Sort 1))))
-/

@[dcc_judge, inline]
def read_arrow.{u} {τ_c : Type u} [DecidableEq τ_c]
  (τ : GenericExpr (τ := τ_c)) : Option ((α β : GenericExpr (τ := τ_c)) × (m : Level) × (Arrow (τ := τ_c) α β m τ)) :=
  match heq : τ with
  | DCC? (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
    if heq₁ : τ = (DCC? (α : Sort m) → β) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .dep⟩
    else .none
  | DCC? (Π(Id(Sort m), !Λ(_a, _b, `(_c, β))) α) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), !Λ(Sort m, Id(Sort m), `(!(Coup(Id(Sort m))), β))) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .dep'⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_a, `(_b, β))) α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, `(α, β))) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .simple⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .eval⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .eval'⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, β))) ∘∘ _g)) α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, β))) ∘∘ _g)) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .curr⟩
    else .none
  | _ => .none

@[dcc_judge, inline]
def read_arrow₁.{u} {τ_c : Type u} [DecidableEq τ_c] (τ α : GenericExpr τ_c) : Option ((β : GenericExpr τ_c) × (m : Level) × (Arrow α β m τ)) :=
  match heq : τ with
  | DCC? (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) _d) =>
    if heq₁ : τ = (DCC? (α : Sort m) → β) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .dep⟩
    else .none
  | DCC? (Π(Id(Sort m), !Λ(_a, _b, `(_c, β))) _d) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), !Λ(Sort m, Id(Sort m), `(!(Coup(Id(Sort m))), β))) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .dep'⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_a, `(_b, β))) _d)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, `(α, β))) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .simple⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .eval⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .eval'⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, β))) ∘∘ _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, β))) ∘∘ _g)) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .curr⟩
    else .none
  | _ => .none

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read₁_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} (h : Arrow α β m τ) : τ.read_arrow₁ α = .some ⟨β, m, h⟩ := by
  cases h <;> simp [read_arrow₁]


@[dcc_judge, inline]
def view_arrow.{u} {τ_c : Type u} [DecidableEq τ_c] (τ α β : GenericExpr (τ := τ_c)) (m : Level) : Option (Arrow α β m τ) :=
  match heq : τ with
  | DCC? (Π(__a, Λ(_a, _b, `(_c, _d))) _e) =>
    if heq₁ : τ = (DCC? (α : Sort m) → β) then
      .some <| by rw [← heq, heq₁]; exact .dep
    else .none
  | DCC? (Π(__a, !Λ(_a, _b, `(_c, _d))) _e) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), !Λ(Sort m, Id(Sort m), `(!(Coup(Id(Sort m))), β))) α)) then
      .some <| by rw [← heq, heq₁]; exact .dep'
    else .none
  | (DCC? (Π(__a, `(_a, `(_b, _c))) _d)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, `(α, β))) α)) then
      .some <| by rw [← heq, heq₁]; exact .simple
    else .none
  | (DCC? (Π(_m₁, `(_m, Eval(_a, _b, `(τ_x, `(τ_y, _β))) ∘∘ _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) then
      .some (by rw [← heq, heq₁]; exact .eval)
    else .none
  | (DCC? (Π(_m₁, `(_m, Eval(_a, _b, `(τ_x, `(τ_y, _β))) ∘' _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) then
      .some (by rw [← heq, heq₁]; exact .eval')
    else .none
  | (DCC? (Π(__m, `(_m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, _β))) ∘∘ _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, β))) ∘∘ _g)) α)) then by
      rw [← heq, heq₁]
      exact .some .curr
    else .none
  | _ => .none

/-
(Π(Id(Sort 3),
                     `(Sort 3,
                       Π(!<Snd(`(⊤, Sort 2))>,
                         !Λ(Coup(`(⊤, Sort 2)), Snd(`(⊤, Sort 2)), `(!(Coup(Snd(`(⊤, Sort 2)))), Sort 3)))))
                     !(Coup(`(⊤, Sort 2))))
-/

-- (Π(Id(Sort 0), `(Sort 0, Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 1))))) ⊤)
inductive Pi.f_β.type.{u} {τ_c : Type u} :
  (GenericExpr τ_c) → (GenericExpr τ_c) → Level → Level → (GenericExpr τ_c) → Type u
  | canon  : Pi.f_β.type f_α δ o n
    (DCC? (Π(Id(Sort o), `(Sort o, Π(f_α, Λ(δ, f_α, `(Coup(f_α), Sort n))))) δ))
  | canon' : Pi.f_β.type (DCC? !<f_α>) (DCC? !(δ)) o n
    (DCC? (Π(Id(Sort o), `(Sort o, Π(!<f_α>, !Λ(δ, f_α, `(!(Coup(f_α)), Sort n))))) !(δ)))
  | semi   : Pi.f_β.type f_α δ o n (DCC? (Π(Id(Sort o), `(Sort o, Π(f_α, `(δ, `(f_α₂, Sort n))))) δ))
  | arrow  : Pi.f_β.type (DCC? Id(Sort m)) δ o n
    (DCC? (Π(Id(Sort o), `(Sort o, `(δ, (Π(Id(Sort m), `(Sort m, `(α, Sort n))) α)))) δ))

def read_pi_f_β_cod.{u} {τ_c : Type u} (τ : GenericExpr τ_c) : Option (GenericExpr τ_c) :=
  match _heq₁ : τ with
  | (DCC? (Π(Id(Sort _o), `(_a, Π(__a, Λ(_b, _c, `(_d, Sort n))))) _e)) =>
      .some (DCC? (Sort n))
  | (DCC? (Π(Id(Sort _o), `(_a, Π(__a, !Λ(_b, _c, `(_d, Sort n))))) _e)) =>
      .some (DCC? (Sort n))
  | (DCC? (Π(_a, `(_b, `(_c, (Π(Id(Sort _m), `(_d, `(_e, Sort n))) _α)))) _f)) =>
    .some (DCC? (Sort n))
  | (DCC? (Π(_a, `(_b, Π(_c, `(_d, `(_f_α₂, Sort n))))) _e)) =>
    .some (DCC? Sort n)
  | _ => .none

@[dcc_judge]
def view_pi_f_β.{u} {τ_c : Type u} [DecidableEq τ_c] (τ f_α δ : GenericExpr τ_c) (o : Level) : Option ((n : Level) × (Pi.f_β.type f_α δ o n τ)) :=
  match heq₁ : τ with
  | (DCC? (Π(__b, `(_a, Π(__a, Λ(_b, _c, `(_d, Sort n))))) _e)) =>
    if heq₂ : τ = (DCC? (Π(Id(Sort o), `(Sort o, Π(f_α, Λ(δ, f_α, `(Coup(f_α), Sort n))))) δ)) then
      .some ⟨n, by rw [← heq₁, heq₂]; exact .canon (f_α := f_α) (δ := δ) (o := o) (n := n)⟩
    else .none
  | (DCC? (Π(__b, `(_a, Π(__a, !Λ(_b, _c, `(_d, Sort n))))) _e)) =>
    match f_α, δ with
    | DCC? !<f_α>, DCC? !(δ) =>
      if heq₂ : τ = (DCC? (Π(Id(Sort o), `(Sort o, Π(!<f_α>, !Λ(δ, f_α, `(!(Coup(f_α)), Sort n))))) !(δ))) then
        .some ⟨n, by rw [← heq₁, heq₂]; exact .canon' (f_α := f_α) (δ := δ) (o := o) (n := n)⟩
      else .none
    | _, _ => .none
  | (DCC? (Π(_a, `(_b, `(_c, (Π(Id(Sort m), `(_d, `(_e, Sort n))) α)))) _f)) =>
    if heq₂ : τ = (DCC? (Π(Id(Sort o), `(Sort o, `(δ, (Π(Id(Sort m), `(Sort m, `(α, Sort n))) α)))) δ)) then
      if heq₃ : f_α = (DCC? Id(Sort m)) then
        .some ⟨n, by rw [← heq₁, heq₂, heq₃]; exact .arrow (δ := δ) (o := o) (n := n)⟩
      else .none
    else .none
  | (DCC? (Π(_a, `(_b, Π(_c, `(_d, `(f_α₂, Sort n))))) _e)) =>
    if heq₂ : τ = (DCC? (Π(Id(Sort o), `(Sort o, Π(f_α, `(δ, `(f_α₂, Sort n))))) δ)) then
      .some ⟨n, by rw [← heq₁, heq₂]; exact .semi⟩
    else .none
  | _ => .none

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Pi.f_β.type.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α δ τ : GenericExpr τ_c}
  (h : Pi.f_β.type f_α δ o n τ) : view_pi_f_β τ f_α δ o = .some ⟨n, h⟩ := by
  cases h <;> simp [view_pi_f_β]

@[dcc_judge] abbrev Pi.f_β.type'.{u} {τ_c : Type u} (f_α α : GenericExpr τ_c) (m o : Level) :=
  (DCC? (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(f_α), Sort o))))) α))

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.view_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} (h : Arrow α β m τ) : view_arrow τ α β m = Option.some h := by
  cases h <;> simp [view_arrow]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c}
  (h : Arrow α β m τ) : τ.read_arrow = .some ⟨α, β, m, h⟩ := by
  cases h <;> simp [read_arrow]

@[dcc_judge, inline]
abbrev arrow.matcher.{u} {τ_c : Type u} [DecidableEq τ_c] (t : GenericExpr τ_c) : Option ((α β : GenericExpr τ_c) × (m : Level) × PULift.{1, 0} (t = (DCC? (α : Sort m) → β))) :=
  match heq₀ : t with
  | DCC? (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
    if heq₁ : t = (DCC? (α : Sort m) → β) then
      .some ⟨α, β, m, ⟨by rw [← heq₀, heq₁]⟩⟩
    else
      .none
  | _ => .none

def is_arrow.{u} {τ_c : Type u} [DecidableEq τ_c] (e : GenericExpr τ_c) : Bool :=
  (arrow.matcher e).isSome

@[dcc_judge] abbrev Top.type.{u} {τ_c : Type u} : GenericExpr τ_c :=
  DCC? Sort 0

@[dcc_judge] abbrev Tintro.type.{u} {τ_c : Type u} : GenericExpr τ_c :=
  DCC? ⊤

@[dcc_judge] abbrev Bot.type.{u} {τ_c : Type u} : GenericExpr τ_c :=
  DCC? Sort 0

/-
TODO: x needs to depend on (env : δ)
-/
@[dcc_judge] abbrev fst.f_β.type.{u} {τ_c : Type u} (α δ : GenericExpr τ_c) (m n o : Level) : GenericExpr τ_c :=
  (DCC? (δ : Sort o) → ((α : Sort m) → Sort n))

@[dcc_judge] abbrev snd.f_β.type.{u} {τ_c : Type u} (δ _β : GenericExpr τ_c) (o : Level) : GenericExpr τ_c :=
  (DCC? (Π(Id(Sort o), _β) δ))

@[dcc_judge] abbrev id.type.{u} {τ_c : Type u} (α : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? (α : Sort m) → α

/-
β : ∀ (x : α), Sort n
Fst(β) : ∀ (s : Coup(β)), α
-/
@[dcc_judge] abbrev fstc.type.{u} {τ_c : Type u} (α β : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  DCC? (Coup(β) : Sort (max m n)) → α

/-
β : ∀ (x : α), Sort n
Snd(β) : ∀ (s : Coup(β)), (β ∘ Fst(β)) s
-/
@[dcc_judge] abbrev sndc.type.{u} {τ_c : Type u} (β : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort (max m n)), `(Sort (max m n), β ∘' Fst(β))) Coup(β))

/-
f_β : δ → α → Sort n
Fst(f_β) : ∀ (env : δ) (s : Σ(f_β) env), α
-/

@[dcc_judge] abbrev fst.type.{u} {τ_c : Type u} (α f_β δ : GenericExpr τ_c) (n o : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort o), `(Sort o, (Π(Id(Sort n), Λ(Sort n, Id(Sort n), `(Coup(Id(Sort n)), α))) ∘' Σ(α, f_β)))) δ)

/-
Λ(β, x) y z → x ⟦β⟧(y, z)

β receives x

x : ∀ (s : coup.type α β m), γ s
-/
@[dcc_judge] abbrev curr.type.{u} {τ_c : Type u} (α β γ : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort m), `(Sort m, Π(β, Λ(α, β, γ)))) α) -- weaken α, keep x

@[dcc_judge] abbrev curr'.type.{u} {τ_c : Type u} (α β γ : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort m), `(Sort m, Π(!<β>, !Λ(α, β, γ)))) !(α)) -- weaken α, keep x

/-
*(f) &(x) = (f x)
-/

/-
β : α → Sort n
-/
@[dcc_judge] abbrev curr.β.type.{u} {τ_c : Type u} (f_α x_α : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  (DCC? (Π(f_α, (: Sort m) → Sort n) x_α))

/-
Nondependent quotation.

x : α
`(β, x) : β → α
-/
@[dcc_judge] abbrev quot.type.{u} {τ_c : Type u} (α β : GenericExpr τ_c) (n : Level) : GenericExpr τ_c :=
  DCC? (β : Sort n) → α

/-
⟨f, g⟩ x = (f x, g x (f x))

f : ∀ (x : α), β x
g : ∀ (x : α) (y : β x), γ x y
⟨f, g⟩ : ∀ (x : α), Σ(Λ(α, β, γ)) x
-/
@[dcc_judge] abbrev pair.type.{u} {τ_c : Type u} (α β γ : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort m), `(Sort m, *<Σ(β, γ)>)) !(α))

@[dcc_judge] abbrev comp'.type.{u} {τ_c : Type u} (α γ g : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort m), `(Sort m, γ ∘' g)) α)

/-
g : ∀ (x : α), Σ(Λ(α, `(α, α), f_β ∘ Fst(`(α, α)))) x
f : ∀ (s : Coup(f_β)), `(Sort n, γ)

f ∘ g : ∀ (x : α), γ ∘ g
-/

@[dcc_judge] abbrev comp.g.type.{u} {τ_c : Type u} (α β : GenericExpr τ_c) (m : Level) :=
  (DCC? (Π(Id(Sort m), `(Sort m, *<Σ(`(α, α), Λ(α, `(α, α), `(Coup(`(α, α)), β)))>)) !(α)))

/-
(some (Π(Id(Sort 1),
   `(Sort 1,
     (Σ(`(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))), `(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0))) ∘'
        *(Coup(`(⊤, Sort 0))))))
   !(Coup(`(⊤, Sort 0)))))
`(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0))
-/

@[dcc_judge] abbrev comp₂.g.type.{u} {τ_c : Type u} (α β : GenericExpr τ_c) (m : Level) :=
  (DCC? (Π(Id(Sort m), `(Sort m, *<Σ(`(α, α), Λ(α, `(α, α), β ∘' Fst(`(α, α))))>)) !(α)))

inductive Comp₂.g.type.{u} {τ_c : Type u} : GenericExpr τ_c → GenericExpr τ_c → Level → GenericExpr τ_c → Type u
  | dep    : Comp₂.g.type α β m (comp₂.g.type α β m)
  | simple : Comp₂.g.type α β m (DCC? (Π(Id(Sort m), `(Sort m, *<Σ(`(α, α), `(α, β))>)) !(α)))

def read_comp₂_g_type.{u} {τ_c : Type u} [DecidableEq τ_c] (τ : GenericExpr τ_c) : Option ((α β : GenericExpr τ_c) × (m : Level) × (Comp₂.g.type α β m τ)) :=
  match τ with
  | (DCC? (Π(Id(Sort m), `(_a, *<Σ(_b, Λ(_c, _d, β ∘' _e))>)) !(α))) =>
    if heq : (DCC? (Π(Id(Sort m), `(_a, *<Σ(_b, Λ(_c, _d, β ∘' _e))>)) !(α))) = (comp₂.g.type α β m) then
      .some ⟨α, β, m, (by
        cases heq
        exact .dep )⟩
    else .none
  | (DCC? (Π(Id(Sort m), `(_a, *<Σ(_b, `(_c, β))>)) !(α))) =>
    if heq : (DCC? (Π(Id(Sort m), `(_a, *<Σ(_b, `(_c, β))>)) !(α))) = (DCC? (Π(Id(Sort m), `(Sort m, *<Σ(`(α, α), `(α, β))>)) !(α))) then
      .some ⟨α, β, m, (by
        cases heq
        exact .simple )⟩
    else .none
  | _ => none

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Comp₂.g.type.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} (h : Comp₂.g.type α β m τ) : τ.read_comp₂_g_type = .some ⟨α, β, m, h⟩ := by
  cases h <;> simp [read_comp₂_g_type]

@[dcc_judge] abbrev comp.f.type.{u} {τ_c : Type u} (f_β f_γ : GenericExpr τ_c) (n : Level) :=
  (DCC? (Π(Id(Sort n), f_γ) Coup(f_β)))

@[dcc_judge] abbrev comp₂.f.type.{u} {τ_c : Type u} (β f_γ : GenericExpr τ_c) (n : Level) :=
  (DCC? (Π(Id(Sort n), f_γ) Coup(β)))

/-
(Π(Id(Sort 1),
   `(Sort 1, Eval(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0), `(Coup(`(⊤, Sort 0)), `(Sort 0, Sort 0)))))
   Coup(`(Coup(`(⊤, Sort 0)), Sort 0)))
-/

@[dcc_judge] abbrev comp.type.{u} {τ_c : Type u} (α γ g : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort m), `(Sort m, γ ∘ g)) !(α))

@[dcc_judge] abbrev comp₂.type.{u} {τ_c : Type u} (α γ g : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort m), `(Sort m, γ ∘∘ g)) !(α))

@[dcc_judge] abbrev eql.type.{u} {τ_c : Type u} (f_α δ : GenericExpr τ_c) (o : Level) : GenericExpr τ_c :=
  (DCC? (Π(Id(Sort o),
      `(Sort o, Π(!<f_α>, Λ(!(δ), !<f_α>, `(Coup(!<f_α>), Sort 0))))) !(δ)))

@[dcc_judge] abbrev refl.type.{u} {τ_c : Type u} (f_α δ : GenericExpr τ_c) (o : Level) : GenericExpr τ_c :=
  (DCC? (Π(Id(Sort o), `(Sort o, Π(!<f_α>, Eql(f_α)))) !(δ)))

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
@[dcc_judge] abbrev Pi.type.{u} {τ_c : Type u} (α : GenericExpr τ_c) (o m n : Level) : GenericExpr τ_c :=
  DCC? (α : Sort o) → Sort (max m n)

/-abbrev Pi.f_β.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(m, α, f_α), Sort o))))) α))-/

@[dcc_judge] abbrev pair.β.type.{u} {τ_c : Type u} (α : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  DCC? (Sort m : Sort m.succ) → ((α : Sort m) → Sort n)

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
@[dcc_judge] abbrev Sigma.type.{u} {τ_c : Type u} (δ : GenericExpr τ_c) (m n o : Level) : GenericExpr τ_c :=
  DCC? (δ : Sort o) → Sort max m n

@[dcc_judge] abbrev Coup.type.{u} {τ_c : Type u} (m n : Level) : GenericExpr τ_c :=
  DCC? Sort max m n

/-
f_α : δ → Sort m
Eval(f_α, f_β) : ∀ (s : ∀ (env : δ), (Σ(f_α, f_β) env)) (env : δ),
  f_β env (Fst(f_β env) (s env))

Fst ({ f, g } x) = f x

Eval(f_α, f_β) f x = (Snd ∘ f) x

Eval(f_α, f_β) : ∀ (s : ∀ (env : δ), (Σ(f_α, f_β) env)) (env : δ),
  f_β env (Fst(f_β env) (s env))

Eval takes M and N explicitly?

Eval(M, N)

but then we can't destructure couple back into data.
Need actual eval.

Eval(x) ⟦β⟧(y, z) = x y z?

x : ∀ (x : α) (y : β x), γ x y
Eval(x) : ∀ (c : Coup(β)), Eval(γ) c

This is canonical.
-/

@[dcc_judge] abbrev Eval.type.{u} {τ_c : Type u} (α β γ : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  DCC? (Π(Id(Sort (max m n)), `(Sort (max m n), Eval(α, β, γ))) Coup(β))

open Std (ToFormat Format format) in
def toFormat.{u} {τ : Type u} [hFmt : Std.ToFormat τ]
  (e : GenericExpr τ) (pretty : Bool := False) : Std.Format :=
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
  | (DCC? ⊤)                   => "⊤"
  | (DCC? ⊥)                   => "⊥"
  | (DCC? ∗)                   => "∗"
  | (DCC? !<f>)                => comb "!" (paren := angle_hard) [f.toFormat pretty]
  | (DCC? $<f>)                => comb "$" (paren := angle_hard) [f.toFormat pretty]
  | (DCC? &(x))                => "&" ++ (paren (x.toFormat pretty))
  | (DCC? *<x>)                => comb "*" (paren := angle_hard) [x.toFormat pretty]
  | (DCC? !(x))                => "!" ++ (paren (x.toFormat pretty))
  | (DCC? Eval(α, β, x))       => comb "Eval" [α.toFormat pretty, β.toFormat pretty, x.toFormat pretty]
  | (DCC? `(β, x))             => comb "`" [β.toFormat pretty, x.toFormat pretty]
  | (DCC? Id(α))               => comb "Id" [α.toFormat pretty]
  | (DCC? Sort m)              => "Sort " ++ (Std.format m)
  | (DCC? Fst(β))             => comb "Fst" [β.toFormat pretty]
  | (DCC? Snd(β))             => comb "Snd" [β.toFormat pretty]
  | (DCC? Λ(α, β, e))          => comb "Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC? !Λ(α, β, e))         => comb "!Λ" [α.toFormat pretty, β.toFormat pretty, e.toFormat pretty]
  | (DCC? Π(α, β))             =>
    comb "Π" [α.toFormat pretty, β.toFormat pretty]
  | (DCC? ⟦β⟧⟨a, b⟩)           =>
    comb (paren := angle) (bbracket (sepD [β.toFormat pretty])) [a.toFormat pretty, b.toFormat pretty]
  | (DCC? ⟦β⟧(a, b))           =>
    comb (bbracket (sepD [β.toFormat pretty])) [a.toFormat pretty, b.toFormat pretty]
  | (DCC? Coup(β))             => comb "Coup" [β.toFormat pretty]
  | (DCC? Σ(α, β))             => comb "Σ" [α.toFormat pretty, β.toFormat pretty]
  | (DCC? x = y)               => sepD [x.toFormat pretty, y.toFormat pretty] " ="
  | (DCC? Eql(f_α))            => comb "Eql" [f_α.toFormat pretty]
  | (DCC? refl(f_α))           => comb "refl" [f_α.toFormat pretty]
  | (DCC? f ∘ g)               =>
    paren (sepD [f.toFormat pretty, g.toFormat pretty] " ∘")
  | (DCC? f ∘∘ g)               =>
    paren (sepD [f.toFormat pretty, g.toFormat pretty] " ∘∘")
  | (DCC? f ∘' g)               =>
    paren (sepD [f.toFormat pretty, g.toFormat pretty] " ∘'")
  | (DCC? (f x))               =>
    if pretty then
      match heq₁ : (DCC? (f x)) with
      | DCC? (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
        have _h : sizeOf α < sizeOf e := by
          rw [heq₁] at heq₀
          rw [heq₀]
          simp [sizeOf, GenericExpr._sizeOf_1]
          grind
        have _h : sizeOf β < sizeOf e := by
          rw [heq₁] at heq₀
          rw [heq₀]
          simp [sizeOf, GenericExpr._sizeOf_1]
          grind
        sepD [(paren (sepD [(α.toFormat pretty), s!"Sort {m}"] " :")), β.toFormat pretty] " →"
      | _ => (paren (f.toFormat pretty ++ (.indentD (x.toFormat pretty))))
    else (paren (f.toFormat pretty ++ (.indentD (x.toFormat pretty))))
  | .const c => Std.format c
termination_by e

end GenericExpr

open Std (ToFormat Format format) in
instance (priority := high) instToFormat [ToFormat τ] : Std.ToFormat (GenericExpr τ) :=
  ⟨GenericExpr.toFormat (pretty := true)⟩

open Std (ToFormat Format format) in
instance (priority := high) instToFormat' [Repr τ] : Std.ToFormat (GenericExpr τ) :=
  ⟨GenericExpr.toFormat (pretty := true) (hFmt := ⟨repr⟩)⟩

open Std (ToFormat Format format) in
instance (priority := high) instToString [ToFormat τ] : ToString (GenericExpr τ) :=
  ⟨toString ∘ GenericExpr.toFormat (pretty := true)⟩
open Std (ToFormat Format format) in

open Std (ToFormat Format format) in
instance (priority := high) instToString' [Repr τ] : ToString (GenericExpr τ) :=
  ⟨toString ∘ GenericExpr.toFormat (pretty := true) (hFmt := ⟨repr⟩)⟩
open Std (ToFormat Format format) in

def GenericExpr.raw_repr.{u} {τ : Type u} [Repr τ] (e : GenericExpr τ) : Std.Format :=
  repr e

open Std (ToFormat Format format) in
instance (priority := high) instRepr.{u} {τ : Type u} [ToFormat τ] : Repr (GenericExpr τ) :=
  { reprPrec := fun e _ =>
    GenericExpr.toFormat e (pretty := true) }

instance instOptToFormat : Std.ToFormat (Option Expr) := ⟨fun me =>
  match me with
  | .none => Std.format me
  | .some e =>
    let l := "(some".length.succ
    .group ("(some " ++ (.fill (.nest l (e.toFormat (pretty := true)))) ++ ")")⟩

#eval (DCC ((Sort 1 : Sort 2) → Sort 2))
