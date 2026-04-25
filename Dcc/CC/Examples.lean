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
    let e := DCC (⟦2, Sort 1, β, β⟧⟨Id(Sort 1), Id(Sort 1)⟩)
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
  Sigma.fst <$> (DCC (App'(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1)))
    (Sort 1)
    ⟦`((Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1), Sort 1)⟧(Id(Sort 1), Sort 0))).infer

/-
(Σ(`(⊤, `((Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1), (Id(Sort 2) Sort 1)))) ∗)
(Σ(`(⊤, `((Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1), Sort 1))) ∗)
-/

/-
(Σ(`(⊤, `((Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1), (Id(Sort 2) Sort 1)))) ∗)

Coup(`((Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1), (Id(Sort 2) Sort 1)))

(Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1)
(Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1)
-/

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1)).infer

/-
(Π(Id(Sort 2), `(Sort 2, (Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1)) Sort 1))) Sort 1)
^ this has a partially applied curr

we should not be applying env to f_β OR f_α.

expected

what is actual Id type?
-/

#eval Std.format <$> test_app

/-
(Σ(`(⊤, `(Π(Id(Sort 2), `(Sort 2, (Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1)) Sort 1))), Sort 1))) ∗)

expected

fn type:
Π(Id(Sort 2), `(Sort 2, (Λ(Sort 2, Id(Sort 2), `((Coup(Id(Sort 2))) ∗), Sort 1)) Sort 1)))

Id(Sort 1)
-/

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1)).infer

/-
I should have gotten f_α and f_β corrrectly.
The main challenge is the structure of the Σ itself.
-/
