import Dcc.CC.Ast
import Dcc.CC.Judge2

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1) ∘ Id(Sort 1)).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC Fst(`(Sort 1, `(Sort 1, Sort 1)), Sort 0)).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Σ(`(Sort 1, `(Sort 1, Sort 1))) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fstc(3, Sort 2, Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Sndc(3, Sort 2, Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ((Id(Sort 1) ∘ Id(Sort 1)) (Sort 0))).infer

def test_pair : Option Expr := do
  match ← (DCC Id(Sort 1)).infer with
  | ⟨DCC (Π(_f_α, Λ(_a, _b, β)) _x), _⟩ =>
    let e := DCC (⟦2, Sort 1, β, β⟧⟨Id(Sort 1), Id(Sort 1)⟩ (Sort 0))
    Sigma.fst <$> e.infer
  | _ => .none

#eval Std.format test_pair

--#eval (DCC (Π(Id(Sort 2), `(Sort 2, `(Sort 1, Sort 1))) Sort 1)).infer

def test_app : Option Expr := do
  match ← (DCC Id(Sort 1)).infer with
  | ⟨t@(DCC (Π(_f_α, Λ(_a, _b, β)) _x)), _⟩ =>
    let e := DCC (App(Sort 1, β) ⟦`(t, Sort 1)⟧(Id(Sort 1), Sort 0))
    Sigma.fst <$> e.infer
  | _ => .none

#eval Std.format <$> test_app

/-
New app type:

needs to work with environment.

Coup(n, Π(f_α, f_β) env, `(Π(f_α, f_β) env, (f_α env)))

App(f_α, f_β, env) : Π(Id(Sort n),
  (f_β env) ∘ Snd'(Π(f_α, f_β) env, (f_α env))
  ) Coup(n, Π(f_α, f_β) env, `(Π(f_α, f_β) env, (f_α env)))
-/

/-
Uncurry:

uncurry(f) (x, y) = f x y

f : Π(Id(Sort m),

f x : 

uncurry := ⟦`(Sort m, Π(β, Λ(α, β, γ))), β ∘ Snd'(Sort m, α)⟧⟨f ∘ Fstc(α, β), Sndc(α, β)⟩

uncurry := App() ∘
  ⟦`(Sort m, Π(β, Λ(α, β, γ))), β ∘ Snd'(Sort m, α)⟧⟨f ∘ Fstc(α, β), Sndc(α, β)⟩
-/

def uncurry (α β γ f : Expr) (m : Level) : Expr :=
  sorry
