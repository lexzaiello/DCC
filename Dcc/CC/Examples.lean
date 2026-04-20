import Dcc.CC.Ast
import Dcc.CC.Judge2

#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ⟦Id(Sort 2)⟧(Sort 1, Sort 0)).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fst(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Snd(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC Σ(Id(Sort 1))).infer
#eval (Std.format ∘ Sigma.fst) <$> (id.type (DCC Sort 1) 2).infer
#eval Std.format (id.type (DCC Sort 1) 2)
#eval (Std.format ∘ Sigma.fst) <$> (DCC `(Sort 2, `(Sort 1, Sort 1))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (`(Sort 1, `(Sort 1, Sort 0)) (Sort 0) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ((Id(Sort 1) ∘ Id(Sort 1)) (Sort 0))).infer

def test_pair : Option Expr :=
  let f := DCC Id(Sort 2)
  let g := DCC Id(Sort 2) ∘ Id(Sort 2)
  -- γ receives (f x)
  /-
    Id(Sort 2) ∘ Id(Sort 2) :
    (some ((Π(3, 3) Sort 2) (Λ(Id(Sort 3),`(Sort 3, ((Σ(4, 3) Sort 3) Id(Sort 3)), Sort 2)) Sort 2)
      ∘ Id(Sort 2) ∘ Snd(Sort 3, Id(Sort 3))))
  -/
  let γ := DCC (Λ(Id(Sort 3), `(Σ(Id(Sort 3)), Sort 2)) Sort 2)
  let e := DCC (⟦γ⟧⟨f, g⟩ (Sort 1))
  Sigma.fst <$> e.infer

#eval test_pair

#eval (Std.format ∘ Sigma.fst) <$> (DCC App(Sort 1, `(Σ(Id(Sort 2)), Sort 1))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (App(Sort 1, `(Σ(Id(Sort 2)), Sort 1))  ⟦`((Π(Id(Sort 2), Λ(Id(Sort 2), `(Σ(Id(Sort 2)), Sort 1))) Sort 1), Sort 1)⟧(Id(Sort 1), Sort 0))).infer

/-
expected:
Σ(`((Π(Id(Sort 2), `(Σ(Id(Sort 1)), Sort 1)) Sort 1), Sort 1)))

actual:
Σ(`((Π(Id(Sort 2), Λ(Id(Sort 2), `(Σ(Id(Sort 2)), Sort 1))) Sort 1), Sort 1))

expected':
Σ(`((Π(Id(Sort 2), Λ(Id(Sort 2), `(Σ(Id(Sort 1)), Sort 1))) Sort 1), Sort 1))
-/

/-
α → α
Π(Id(Sort m), `(Sort m, `(α, α))) α
(some (Π(Id(Sort 3), `(Sort 3, `(Sort 2, (Π(Id(Sort 2), `(Sort 2, `(Sort 1, Sort 2))) Sort 1)))) Sort 2))

`(Sort m, `(α, α))
: (some (Π(Id(Sort 3), `(Sort 3, `(Sort 2, (Π(Id(Sort 2), `(Sort 2, `(Sort 1, Sort 2))) Sort 1)))) Sort 2))


-/
