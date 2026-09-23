import Dcc.Ast
import Dcc.Attrs

namespace GenericExpr

open Dsl in
inductive Arrow.{u} {τ : Type u} : GenericExpr (τ := τ) → GenericExpr (τ := τ) → Level → GenericExpr (τ := τ) → Type u
  | simple : Arrow α β u (DCC? ((Π (Id Sort u) (`Sort u (`α β))) α))
deriving Repr
  /-| dep    : Arrow α β u (DCC? ((Π (Id Sort u) (Λ Sort u (Id Sort u) (` (Σ (Id Sort u)) β))) α))
  | dep'   : Arrow α β u (DCC? ((Π (Id Sort u) (!Λ Sort u (Id Sort u) (` (! (Σ (Id Sort u))) β))) α))-/

/-
(Π(Id(Sort 2),
             `(Sort 2,
               Π(!<Snd(`(⊤, Sort 1))>,
                 !Λ(Coup(`(⊤, Sort 1)), Snd(`(⊤, Sort 1)), `(!(Coup(Snd(`(⊤, Sort 1)))), Sort 2)))))
             !(Coup(`(⊤, Sort 1))))
-/

/-
(Swap B C) (& (,B₂ x y)) = (,(C x) y x)

B : A → Sort u       C : (x : A) (y : B x) → Sort v
---------------------------------------------------
(Swap B C) : (x : (! (Σ B))) → ((∘ (Σ (∘ B (Fst B)) (∘ C (Fst B))) (* (Σ B))) x)
-/

open Dsl in
def Swap.type (A B : GenericExpr τ) (u v : Level) : GenericExpr τ :=
  DCC? (((Σ (`A B)): Sort (max u v)) → (Σ (`B A)))

@[dcc_judge, inline]
def read_arrow.{u} {τ_c : Type u} [DecidableEq τ_c]
  (τ : GenericExpr (τ := τ_c)) : Option ((α β : GenericExpr (τ := τ_c)) × (m : Level) × (Arrow (τ := τ_c) α β m τ)) :=
  open Dsl in match heq : τ with
  /-| DCC? ((Π (Id Sort m) (Λ _a _b (` _c β))) α) =>
    if heq₁ : τ = (DCC? ((Π (Id Sort m) (`Sort m (Λ then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .dep⟩
    else .none
  | DCC? ((Π (Id Sort m) (!Λ _a _b (` _c β))) α) =>
    if heq₁ : τ = (DCC? ((Π (Id Sort m) (!Λ Sort m (Id Sort m) (` (! (Σ (Id Sort m))) β))) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .dep'⟩
    else .none-/
  | (DCC? ((Π (Id Sort m) (` _a (` _b β))) α)) =>
    if heq₁ : τ = (DCC? ((Π (Id Sort m) (`Sort m (`α β))) α)) then
      .some ⟨α, β, m, by rw [← heq, heq₁]; exact .simple⟩
    else .none
  | _ => .none

@[dcc_judge, inline]
def read_arrow₁.{u} {τ_c : Type u} [DecidableEq τ_c] (τ α : GenericExpr τ_c) : Option ((β : GenericExpr τ_c) × (m : Level) × (Arrow α β m τ)) :=
  open Dsl in match heq : τ with
  /-| DCC? (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) _d) =>
    if heq₁ : τ = (DCC? (α : Sort m) → β) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .dep⟩
    else .none
  | DCC? (Π(Id(Sort m), !Λ(_a, _b, `(_c, β))) _d) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), !Λ(Sort m, Id(Sort m), `(!(Coup(Id(Sort m))), β))) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .dep'⟩
    else .none-/
  | (DCC? ((Π (Id Sort m) (`_a (`_b β))) _d)) =>
    if heq₁ : τ = (DCC? ((Π (Id Sort m) (`Sort m (`α β))) α)) then
      .some ⟨β, m, by rw [← heq, heq₁]; exact .simple⟩
    else .none
  /-| (DCC? ((Π (Id Sort m) (`_m (Eval _a _b (`τ_x (`τ_y β))) ∘∘ _g)) _α)) =>
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
    else .none-/
  | _ => .none

@[dcc_judge, inline]
def read_arrow₂.{u} {τ_c : Type u} [DecidableEq τ_c] (τ α : GenericExpr τ_c) (m : Level) : Option ((β : GenericExpr τ_c) × (Arrow α β m τ)) :=
  open Dsl in match heq : τ with
  /-| DCC? (Π(Id(Sort _m), Λ(_a, _b, `(_c, β))) _d) =>
    if heq₁ : τ = (DCC? (α : Sort m) → β) then
      .some ⟨β, by rw [← heq, heq₁]; exact .dep⟩
    else .none
  | DCC? (Π(Id(Sort _m), !Λ(_a, _b, `(_c, β))) _d) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), !Λ(Sort m, Id(Sort m), `(!(Coup(Id(Sort m))), β))) α)) then
      .some ⟨β, by rw [← heq, heq₁]; exact .dep'⟩
    else .none-/
  | (DCC? ((Π (Id Sort _m) (`_a (`_b β))) _d)) =>
    if heq₁ : τ = (DCC? ((Π (Id Sort m) (`Sort m (`α β))) α)) then
      .some ⟨β, by rw [← heq, heq₁]; exact .simple⟩
    else .none
  /-| (DCC? (Π(Id(Sort _m), `(__m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘∘ _g)) α)) then
      .some ⟨β, by rw [← heq, heq₁]; exact .eval⟩
    else .none
  | (DCC? (Π(Id(Sort _m), `(__m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, `(τ_x, `(τ_y, β))) ∘' _g)) α)) then
      .some ⟨β, by rw [← heq, heq₁]; exact .eval'⟩
    else .none
  | (DCC? (Π(Id(Sort _m), `(__m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, β))) ∘∘ _g)) _α)) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), `(Sort m, Eval(_a, _b, Λ(τ_x, τ_y, `(f_τ, β))) ∘∘ _g)) α)) then
      .some ⟨β, by rw [← heq, heq₁]; exact .curr⟩
    else .none-/
  | _ => .none

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read₁_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} (h : Arrow α β m τ) : τ.read_arrow₁ α = .some ⟨β, m, h⟩ := by
  cases h; simp [read_arrow₁]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read₂_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} {m : Level} (h : Arrow α β m τ) : τ.read_arrow₂ α m = .some ⟨β, h⟩ := by
  cases h; simp [read_arrow₂]

@[dcc_judge, inline]
def view_arrow.{u} {τ_c : Type u} [DecidableEq τ_c] (τ α β : GenericExpr (τ := τ_c)) (m : Level) : Option (Arrow α β m τ) :=
  open Dsl in match heq : τ with
  /-| DCC? (Π(__a, Λ(_a, _b, `(_c, _d))) _e) =>
    if heq₁ : τ = (DCC? (α : Sort m) → β) then
      .some <| by rw [← heq, heq₁]; exact .dep
    else .none
  | DCC? (Π(__a, !Λ(_a, _b, `(_c, _d))) _e) =>
    if heq₁ : τ = (DCC? (Π(Id(Sort m), !Λ(Sort m, Id(Sort m), `(!(Coup(Id(Sort m))), β))) α)) then
      .some <| by rw [← heq, heq₁]; exact .dep'
    else .none-/
  | (DCC? ((Π __a (`_a (`_b _c))) _d)) =>
    if heq₁ : τ = (DCC? ((Π (Id Sort m) (`Sort m (`α β))) α)) then
      .some <| by rw [← heq, heq₁]; exact .simple
    else .none
  /-| (DCC? (Π(_m₁, `(_m, Eval(_a, _b, `(τ_x, `(τ_y, _β))) ∘∘ _g)) _α)) =>
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
    else .none-/
  | _ => .none

/-
(Π(Id(Sort 3),
                     `(Sort 3,
                       Π(!<Snd(`(⊤, Sort 2))>,
                         !Λ(Coup(`(⊤, Sort 2)), Snd(`(⊤, Sort 2)), `(!(Coup(Snd(`(⊤, Sort 2)))), Sort 3)))))
                     !(Coup(`(⊤, Sort 2))))
-/

-- (Π(Id(Sort 0), `(Sort 0, Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 1))))) ⊤)
open Dsl in inductive Pi.C.type.{u} {τ_c : Type u} :
  (GenericExpr τ_c) → (GenericExpr τ_c) → Level → Level → (GenericExpr τ_c) → Type u
  | canon  : Pi.C.type B δ o n
    (DCC? ((Π (Id Sort o) (`Sort o (Π B (Λ δ B (` (Σ B) Sort n))))) δ))
  | canon' : Pi.C.type (DCC? (!<> B)) (DCC? (!δ)) o n
    (DCC? ((Π(Id Sort o) (`Sort o (Π (!<> B) (!Λ δ B (` (! (Σ B)) Sort n))))) (! δ)))
  | arrow  : Pi.C.type B δ o n
    (DCC? ((Π (Id Sort o) (`Sort o (`δ ((Π B (`x₂ (`α Sort n))) α)))) δ))
  | semi   : Pi.C.type B δ o n (DCC? ((Π (Id Sort o) (`Sort o (Π B (`δ₂ (`δ₃ Sort n))))) δ))
deriving Repr

open Dsl in
def read_pi_f_β_cod.{u} {τ_c : Type u} (τ : GenericExpr τ_c) : Option (GenericExpr τ_c) :=
  match _heq₁ : τ with
  | (DCC? ((Π (Id Sort _o) (`_a (Π __a (Λ _b _c (`_d Sort n))))) _e)) =>
      .some (DCC? (Sort n))
  | (DCC? ((Π (Id Sort _o) (`_a (Π __a (!Λ _b _c (`_d Sort n))))) _e)) =>
      .some (DCC? (Sort n))
  | (DCC? ((Π _a (`_b (`_c ((Π (Id Sort _m) (`_d (`_e Sort n))) _α)))) _f)) =>
    .some (DCC? (Sort n))
  | _ => .none

@[dcc_judge]
def view_pi_f_β.{u} {τ_c : Type u} [DecidableEq τ_c] (τ f_α δ : GenericExpr τ_c) (o : Level) : Option ((n : Level) × (Pi.C.type f_α δ o n τ)) :=
  open Dsl in match heq₁ : τ with
  | (DCC? ((Π __b (`_a (Π __a (Λ _b _c (`_d Sort n))))) _e)) =>
    if heq₂ : τ = (DCC? ((Π (Id Sort o) (`Sort o (Π f_α (Λ δ f_α (` (Σ f_α) Sort n))))) δ)) then
      .some ⟨n, by rw [← heq₁, heq₂]; exact .canon (B := f_α) (δ := δ) (o := o) (n := n)⟩
    else .none
  | (DCC? ((Π __b (` _a (Π __a (!Λ _b _c (`_d Sort n))))) _e)) =>
    match f_α, δ with
    | DCC? (!<> f_α), DCC? (! δ) =>
      if heq₂ : τ = (DCC? ((Π (Id Sort o) (`Sort o (Π (!<> f_α) (!Λ δ f_α (`(! (Σ f_α)) Sort n))))) (! δ))) then
        .some ⟨n, by rw [← heq₁, heq₂]; exact .canon' (B := f_α) (δ := δ) (o := o) (n := n)⟩
      else .none
    | _, _ => .none
  | (DCC? ((Π _a (`_b (`_c ((Π B (`_d (`_e Sort n))) α)))) _f)) =>
    if heq₂ : τ = (DCC? ((Π (Id Sort o) (`Sort o (`δ ((Π B (`_d (`α Sort n))) α)))) δ)) then
      if heq₃ : f_α = B then
        .some ⟨n, by rw [← heq₁, heq₂, heq₃]; exact .arrow (δ := δ) (o := o) (n := n)⟩
      else .none
    else .none
  | (DCC? ((Π __a (`_a (Π _B (`δ₂ (`δ₃ Sort n))))) _δ)) =>
    if heq : (DCC? ((Π __a (`_a (Π _B (`δ₂ (`δ₃ Sort n))))) _δ)) = (DCC? ((Π (Id Sort o) (`Sort o (Π f_α (`δ₂ (`δ₃ Sort n))))) δ)) then
      .some ⟨n, heq ▸ .semi (B := f_α) (δ := δ) (δ₂ := δ₂) (δ₃ := δ₃)⟩
    else .none
  | _ => .none

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Pi.C.type.complete.{u} {τ_c : Type u} [DecidableEq τ_c] {f_α δ τ : GenericExpr τ_c}
  (h : Pi.C.type f_α δ o n τ) : view_pi_f_β τ f_α δ o = .some ⟨n, h⟩ := by
  cases h <;> simp [view_pi_f_β]

open Dsl in
@[dcc_judge] abbrev Pi.C.type'.{u} {τ_c : Type u} (f_α α : GenericExpr τ_c) (m o : Level) :=
  (DCC? ((Π (Id Sort m) (`Sort m (Π f_α (Λ α f_α (`(Σ f_α) Sort o))))) α))

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.view_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c} (h : Arrow α β m τ) : view_arrow τ α β m = Option.some h := by
  cases h; simp [view_arrow]

@[dcc_judge, aesop safe destruct (rule_sets := [DccReduce])]
theorem Arrow.read_complete.{u} {τ_c : Type u} [DecidableEq τ_c] {α β τ : GenericExpr τ_c}
  (h : Arrow α β m τ) : τ.read_arrow = .some ⟨α, β, m, h⟩ := by
  cases h; simp [read_arrow]

open Dsl in
@[dcc_judge, inline]
abbrev arrow.matcher.{u} {τ_c : Type u} [DecidableEq τ_c] (t : GenericExpr τ_c) : Option ((α β : GenericExpr τ_c) × (m : Level) × PULift.{1, 0} (t = (DCC? (α : Sort m) → β))) :=
  match heq₀ : t with
  | DCC? ((Π (Id Sort m) (Λ _a _b (` _c β))) α) =>
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

open Dsl in
@[dcc_judge] abbrev snd.f_β.type.{u} {τ_c : Type u} (δ _β : GenericExpr τ_c) (o : Level) : GenericExpr τ_c :=
  (DCC? ((Π (Id Sort o) _β) δ))

@[dcc_judge] abbrev id.type.{u} {τ_c : Type u} (α : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? (α : Sort m) → α

/-
β : ∀ (x : α), Sort n
Fst(β) : ∀ (s : Coup(β)), α
-/
open Dsl in
@[dcc_judge] abbrev fstc.type.{u} {τ_c : Type u} (α β : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  DCC? ((Σ β) : Sort (max m n)) → α

/-
β : ∀ (x : α), Sort n
Snd(β) : ∀ (s : Coup(β)), (β ∘ Fst(β)) s
-/
open Dsl in
@[dcc_judge] abbrev sndc.type.{u} {τ_c : Type u} (β : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort (max m n)) (`Sort (max m n) (∘ β (Fst β)))) (Σ β))

/-
f_β : δ → α → Sort n
Fst(f_β) : ∀ (env : δ) (s : Σ(f_β) env), α
-/

open Dsl in
@[dcc_judge] abbrev fst.type.{u} {τ_c : Type u} (α f_β δ : GenericExpr τ_c) (n o : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort o) (`Sort o (∘ (Π (Id Sort n) (Λ Sort n (Id Sort n) (` (Σ (Id Sort n)) α))) (Σ α f_β)))) δ)

/-
Λ(β, x) y z → x ⟦β⟧(y, z)

β receives x

x : ∀ (s : coup.type α β m), γ s
-/
open Dsl in
@[dcc_judge] abbrev curr.type.{u} {τ_c : Type u} (α β γ : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort m) (`Sort m (Π β (Λ α β γ)))) α) -- weaken α, keep x

open Dsl in
@[dcc_judge] abbrev curr.x.type.{u} {τ_c : Type u} (B' C : GenericExpr τ_c) (u v : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort (max u v)) (`(Sort max u v) C)) (Σ B'))

open Dsl in
@[dcc_judge] abbrev curr'.type.{u} {τ_c : Type u} (α β γ : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort m) (`Sort m (Π (!<> β) (!Λ α β γ)))) (! α)) -- weaken α, keep x

open Dsl in
@[dcc_judge] abbrev curr'.x.type.{u} {τ_c : Type u} (B' C : GenericExpr τ_c) (u v : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort (max u v)) (`(Sort max u v) C)) (! (Σ B')))

/-
*(f) &(x) = (f x)
-/

/-
β : α → Sort n
-/
open Dsl in
@[dcc_judge] abbrev curr.β.type.{u} {τ_c : Type u} (f_α x_α : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  (DCC? ((Π f_α (: Sort m) → Sort n) x_α))

/-
Nondependent quotation.

x : α
`(β, x) : β → α
-/
@[dcc_judge] abbrev quot.type.{u} {τ_c : Type u} (α β : GenericExpr τ_c) (n : Level) : GenericExpr τ_c :=
  DCC? (β : Sort n) → α

open Dsl in
@[dcc_judge] abbrev comp.type.{u} {τ_c : Type u} (A C g : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort m) (`Sort m (∘ C g))) A)

@[dcc_judge, inline]
abbrev comp.g.type.{u} {τ : Type u} := Arrow (τ := τ)

open Dsl in
@[dcc_judge] abbrev comp.f.type.{u} {τ_c : Type u} (B C : GenericExpr τ_c) (n : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort n) (`(Sort n) C)) B)

open Dsl in
@[dcc_judge] abbrev eql.type.{u} {τ_c : Type u} (f_α δ : GenericExpr τ_c) (o : Level) : GenericExpr τ_c :=
  (DCC? ((Π (Id Sort o)
      (`Sort o (Π (!<> f_α) (Λ (! δ) (!<> f_α) (`(Σ (!<> f_α)) Sort 0))))) (! δ)))

open Dsl in
@[dcc_judge] abbrev refl.type.{u} {τ_c : Type u} (f_α δ : GenericExpr τ_c) (o : Level) : GenericExpr τ_c :=
  (DCC? ((Π (Id Sort o) (`Sort o (Π (!<> f_α) (Eql f_α)))) (! δ)))

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
@[dcc_judge] abbrev Pi.type.{u} {τ_c : Type u} (α : GenericExpr τ_c) (o m n : Level) : GenericExpr τ_c :=
  DCC? (α : Sort o) → Sort (max m n)

/-abbrev Pi.C.type (f_α α : Expr) (m o : Level) :=
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

open Dsl in
@[dcc_judge] abbrev Eval.type.{u} {τ_c : Type u} (α β γ : GenericExpr τ_c) (m n : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort (max m n)) (`Sort (max m n) (Eval α β γ))) (Σ β))

open Dsl in
@[dcc_judge] abbrev Eval.x.type.{u} {τ_c : Type u} (A' B' C : GenericExpr τ_c) (u : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort u) (`Sort u (Π B' C))) A')

open Dsl in
@[dcc_judge] abbrev Pair.f.type.{u} {τ_c : Type u} (A B : GenericExpr τ_c) (u : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort u) (`(Sort u) B)) A)

open Dsl in
@[dcc_judge] abbrev Pair.g.type.{u} {τ_c : Type u} (A B C : GenericExpr τ_c) (u : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort u) (`(Sort u) (Π B C))) A)

/-
⟨f, g⟩ x = (f x, g x (f x))

f : ∀ (x : α), β x
g : ∀ (x : α) (y : β x), γ x y
⟨f, g⟩ : ∀ (x : α), Σ(Λ(α, β, γ)) x
-/
open Dsl in
@[dcc_judge] abbrev Pair.type.{u} {τ_c : Type u} (A B C : GenericExpr τ_c) (u : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort u) (`Sort u (∘ (Σ B C) (* A)))) (! A))

end GenericExpr
