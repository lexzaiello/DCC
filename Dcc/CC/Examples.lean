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

#eval (Std.format ∘ Sigma.fst) <$> (DCC (App(Sort 1, `(Σ(Id(Sort 2)), Sort 1))
  ⟦`((Π(Id(Sort 2), `(Sort 2, `(Sort 1, Sort 1))) Sort 1), Sort 1)⟧(
    Id(Sort 1),
    Sort 0))).infer

/-
Uncurry:

uncurry(f) (x, y) = f x y

f : Π(Id(Sort m),

uncurry := ⟨f ∘ Fst(β), Snd(β)⟩

uncurry := ⟦β ∘ Fst(Π(β, γ))⟧⟨⟦Π(β, γ)⟧⟨Fst(β), f ∘ Fst(β)⟩, Snd(β)⟩
-/
