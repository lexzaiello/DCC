import Dcc.CC.Ast
import Dcc.CC.Judge2

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1) ∘ Id(Sort 1)).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fst(`(Sort 1, `(Sort 1, Sort 1))) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Σ(`(Sort 1, `(Sort 1, Sort 1))) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fstc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Sndc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ((Id(Sort 1) ∘ Id(Sort 1)) (Sort 0))).infer

def test_pair : Option Expr := do
  match ← (DCC Id(Sort 1)).infer with
  | ⟨DCC (Π(_f_α, Λ(_a, _b, β)) _x), _⟩ =>
    let e := DCC (⟦2, Sort 1, β, β⟧⟨Id(Sort 1), Id(Sort 1)⟩ (Sort 0))
    Sigma.fst <$> e.infer
  | _ => .none

#eval Std.format test_pair

#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1))).infer

#eval (Std.format ∘ Sigma.fst) <$> (DCC (Λ(Sort 2, Id(Sort 2), Fstc(Id(Sort 2))) (Sort 1) (Sort 0))).infer

def test_id_nested : Option Expr := do
  let ⟨t, _⟩ ← (DCC Id(Sort 1)).infer
  Sigma.fst <$> (DCC (Id(t) Id(Sort 1) (Sort 0))).infer

#eval test_id_nested

/-
App(f_α, f_β, f_γ) env x (y, z) = x y z

f_β env x = Sort 1

App(Id(Sort 1)
-/
def test_app : Option Expr := do
  let ⟨env, _⟩ ← (DCC Id(Sort 1)).infer
  match ← env.infer with
  | ⟨δ@(DCC Sort m), _⟩ =>
    let f_α := DCC Id(Sort m)
    let f_β := DCC Λ(Sort m, f_α, `(Coup(f_α), Sort 1))
    -- f_γ env Id(Sort 1) (Sort 0) = (Sort 1)
    let f_γ := DCC Λ(δ, f_α, Λ(Coup(f_α), `(Coup(f_α), Sort 1), `(Coup(`(Coup(f_α), Sort 1)), Sort 1)))
    Sigma.fst <$> (DCC (App(f_α, f_β, f_γ) env)).infer
  | _ => .none

#eval Std.format <$> test_app

/-
I should have gotten f_α and f_β corrrectly.
The main challenge is the structure of the Σ itself.
-/
