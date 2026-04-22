import Dcc.CC.Ast
import Dcc.CC.Judge2

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1) ∘ Id(Sort 1)).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fst(`(Sort 1, `(Sort 1, Sort 1))) (Sort 0))).infer
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

#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1))).infer

#eval (Std.format ∘ Sigma.fst) <$> (DCC Λ(Sort 1, Id(Sort 1), Fstc(2, Sort 1, Id(Sort 1)))).infer

/-
App is most naturally used with rendered pairs.

⟨f, g⟩ x produces a sigma-typed term, but its type is more the shape that App expects
and can introspect into with f_α and f_β
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
