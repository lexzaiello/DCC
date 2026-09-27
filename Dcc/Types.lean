import Dcc.Ast
import Dcc.Attrs

namespace GenericExpr

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

/-
(Π(Id(Sort 3),
                     `(Sort 3,
                       Π(!<Snd(`(⊤, Sort 2))>,
                         !Λ(Coup(`(⊤, Sort 2)), Snd(`(⊤, Sort 2)), `(!(Coup(Snd(`(⊤, Sort 2)))), Sort 3)))))
                     !(Coup(`(⊤, Sort 2))))
-/

open Dsl in
@[dcc_judge] abbrev Top.type.{u} {τ_c : Type u} : GenericExpr τ_c :=
  DCC? Sort 0

open Dsl in
@[dcc_judge] abbrev Tintro.type.{u} {τ_c : Type u} : GenericExpr τ_c :=
  DCC? ⊤

open Dsl in
@[dcc_judge] abbrev Bot.type.{u} {τ_c : Type u} : GenericExpr τ_c :=
  DCC? Sort 0

/-
TODO: x needs to depend on (env : δ)
-/
open Dsl in
@[dcc_judge] abbrev fst.f_β.type.{u} {τ_c : Type u} (α δ : GenericExpr τ_c) (m n o : Level) : GenericExpr τ_c :=
  (DCC? (δ : Sort o) → ((α : Sort m) → Sort n))

open Dsl in
open Dsl in
@[dcc_judge] abbrev snd.f_β.type.{u} {τ_c : Type u} (δ _β : GenericExpr τ_c) (o : Level) : GenericExpr τ_c :=
  (DCC? ((Π (Id Sort o) _β) δ))

open Dsl in
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
open Dsl in
@[dcc_judge] abbrev quot.type.{u} {τ_c : Type u} (α β : GenericExpr τ_c) (n : Level) : GenericExpr τ_c :=
  DCC? (β : Sort n) → α

open Dsl in
@[dcc_judge] abbrev comp.type.{u} {τ_c : Type u} (A C g : GenericExpr τ_c) (m : Level) : GenericExpr τ_c :=
  DCC? ((Π (Id Sort m) (`Sort m (∘ C g))) A)

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
open Dsl in
@[dcc_judge] abbrev Pi.type.{u} {τ_c : Type u} (α : GenericExpr τ_c) (o m n : Level) : GenericExpr τ_c :=
  DCC? (α : Sort o) → Sort (max m n)

/-abbrev Pi.C.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(m, α, f_α), Sort o))))) α))-/

open Dsl in
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
open Dsl in
@[dcc_judge] abbrev Sigma.type.{u} {τ_c : Type u} (δ : GenericExpr τ_c) (m n o : Level) : GenericExpr τ_c :=
  DCC? (δ : Sort o) → Sort max m n

open Dsl in
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
