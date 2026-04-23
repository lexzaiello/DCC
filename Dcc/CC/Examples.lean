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

App(Id(Sort 1)
-/
def test_app : Option Expr := do
  match ← (DCC `(Sort 1, Id(Sort 1))).infer, ← (DCC Id(Sort 1)).infer with
  | ⟨DCC (Π(_f_α, Λ(_a, _b, β)) _x), _⟩, ⟨DCC (Π(_f_α₂, Λ(_a₂, _b₂, β₂)) _x₂), _⟩ =>
    let my_pair := DCC (⟦2, Sort 1, β, β₂⟧⟨`(Sort 1, Id(Sort 1)), Id(Sort 1)⟩ Sort 0)
    dbg_trace (Std.format ∘ Sigma.fst) <$> my_pair.infer
    Sigma.fst <$> (DCC ((App(_f_α₂, Λ(_a₂, _b₂, β₂)) _x₂))).infer
    --dbg_trace my_app.infer.isSome
    -- (my_pair (Sort 0))
    --.none
  | _, _ => .none

#eval Std.format <$> test_app

/-
I should have gotten f_α and f_β corrrectly.
The main challenge is the structure of the Σ itself.
-/
