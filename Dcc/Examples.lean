import Dcc.Ast
import Dcc.Judge
import Dcc.Types

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1) ∘ Id(Sort 1)).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fst(`(Sort 1, `(Sort 1, Sort 1))) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Σ(`(Sort 1, `(Sort 1, Sort 1))) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fstc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Sndc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ((Id(Sort 1) ∘ Id(Sort 1)) (Sort 0))).infer

def mk_test_pair : Expr :=
  DCC (⟨Id(Sort 1), Id(Sort 1)⟩ (Sort 0))

def test_pair : Option Expr := Sigma.fst <$> mk_test_pair.infer

def mk_test_pair₂ : Expr :=
  DCC (⟨`(Sort 1, Id(Sort 1)), Id(Sort 1)⟩ (Sort 0))

#eval (Expr.reduce_all mk_test_pair₂)

#eval Expr.reduce_all <$> test_pair

#eval Std.format test_pair

def test_pair_comp : Option Expr := do
  let e := DCC (⟨Id(Sort 1), Id(Sort 1)⟩)
  Sigma.fst <$> e.infer

#eval test_pair_comp

/-
Want to change pair type so that it aligns with the environment pattern.
Not necessary, since f and g are points.

why does β need to receive a couple? something with duplication I recall.
-/

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
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1))).infer
def test_app : Option Expr := do
  Sigma.fst <$> (DCC (App(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Coup(`(Sort 1, Sort 1)))))
  (Sort 0)
  (⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Id(Coup(`(Sort 1, Sort 1))))⟩ (Sort 0))
  )
    ).infer

/-
This should eta reduce
(Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `(Coup(Σ(`(⊤, `(Sort 1, Sort 1)))), Sort 1)) ∗)


-/

#eval (Std.format ∘ Sigma.fst) <$> (DCC Λ(Sort 1, `(Sort 1, Sort 1),
           (Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `(Coup(Σ(`(⊤, `(Sort 1, Sort 1)))), Sort 1)) ∗))).infer

#eval (Std.format ∘ Sigma.fst) <$> (DCC (⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Id(Coup(`(Sort 1, Sort 1))))⟩ (Sort 0))).infer

/-

-/

#eval (Std.format ∘ Sigma.fst) <$> (DCC Λ(Sort 1, `(Sort 1, Sort 1),
           (Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `(Coup(Σ(`(⊤, `(Sort 1, Sort 1)))), Sort 1)) ∗))).infer

#eval Sigma.fst <$> (DCC Λ(Sort 1, `(Sort 1, Sort 1),
         (Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `((Σ(`(⊤, Σ(`(⊤, `(Sort 1, Sort 1))))) ∗), Sort 1)) ∗))).infer

-- (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)

#eval ((· == (DCC (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)))∘ Expr.reduce_all ∘ Sigma.fst) <$> (DCC Id(Sort 1)).infer

#eval Sigma.fst <$> (DCC Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))).infer

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

-- f_α := `(Sort 1, Sort 1)
/-
f_β := Λ(Sort 1, `(Sort 1, Sort 1),
         (Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `((Σ(`(⊤, Σ(`(⊤, `(Sort 1, Sort 1))))) ∗), Sort 1)) ∗))
-/

/-
We need the pair type to align with App as much as possible, or change pair to be more flexible.

It's specifically f_β that it chokes on. we might need to change it from Π.f_β
-/

#eval (DCC (Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `((Σ(`(⊤, Σ(`(⊤, `(Sort 1, Sort 1))))) ∗), Sort 2)) ∗)).reduce_all
#eval Sigma.fst <$> (DCC Λ(Sort 1, `(Sort 1, Sort 1),
         (Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `((Σ(`(⊤, Σ(`(⊤, `(Sort 1, Sort 1))))) ∗), Sort 1)) ∗))).infer
#eval Sigma.fst <$> (DCC (⟨Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1))), Id(Sort 1)⟩ (Sort 0))).infer

#eval Sigma.fst <$> (DCC Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1)))).infer

#eval (DCC (Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `((Σ(`(⊤, Σ(`(⊤, `(Sort 1, Sort 1))))) ∗), Sort 1)) ∗)).reduce_all

#eval Sigma.fst <$> (DCC Λ(Sort 1, `(Sort 1, Sort 1),
         (Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `((Σ(`(⊤, Σ(`(⊤, `(Sort 1, Sort 1))))) ∗), Sort 1)) ∗))).infer

#eval (DCC (Fst(`(⊤, Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))))) ∗)).reduce_all
#eval (DCC Id(Sort 2) ∘ (Fst(`(⊤, Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))))) ∗)).reduce_all

#eval (Std.format ∘ Sigma.fst) <$> (DCC (⟨`(Sort 1, Id(Sort 1)), Id(Sort 1)⟩ (Sort 0))).infer

#eval (DCC (Σ(Λ(Sort 1, `(Sort 1, (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)),
     `(Sort 1, (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)) ∘
       Fstc(`(Sort 1, (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)))))
   Sort 0)).reduce_all

#eval (DCC (Σ(Λ(Sort 1, `(Sort 1, (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)),
     `(Sort 1, (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)) ∘
       Fstc(`(Sort 1, (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)))))
   Sort 0)).reduce_all

#eval (DCC (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)).reduce_all

#eval (Std.format ∘ Sigma.fst) <$> (DCC (⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1)))⟩ (Sort 0))).infer
#eval Std.format <$> test_app

#eval (Std.format ∘ Sigma.fst) <$> (DCC ⟦`((Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1), Sort 1)⟧(Id(Sort 1), Sort 0)).infer

#eval (Std.format ∘ Sigma.fst) <$> (DCC ⟦`((Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))) Sort 1), Sort 1)⟧(Id(Sort 1), Sort 0)).infer

/-
Maybe my example is wrong? We should try it with the couple example from before.
-/

#eval Sigma.fst <$> (DCC (⟨Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1))), Id(Sort 1)⟩ Sort 0)).infer

#eval (DCC (Σ(Λ(Sort 2, Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))),
       Id(Sort 2) ∘ (Fst(`(⊤, Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1))))) ∗))) (Sort 1))).reduce_all

/-
(Σ(`(⊤, `(Π(Id(Sort 2), `(Sort 2, (Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1)) Sort 1))), Sort 1))) ∗)

expected

fn type:
Π(Id(Sort 2), `(Sort 2, (Λ(Sort 2, Id(Sort 2), `((Coup(Id(Sort 2))) ∗), Sort 1)) Sort 1)))

Id(Sort 1)
-/

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1)).infer

#eval (Std.format ∘ Sigma.fst) <$> (DCC (⟨Id(Sort 1), Id(Sort 1)⟩)).infer
