import Dcc.Ast
import Dcc.Judge3
import Dcc.Types

/-
Can quot be derived?

`(β, x) = Λ(α, Λ(
-/

open Dsl

#eval (Std.format ∘ (·.fst)) <$> (DCC (∘ (Id Sort 1) (Id Sort 1))).infer
#eval (Std.format ∘ (·.fst)) <$> (DCC ((Id Sort 1) (Sort 0))).infer
#eval (DCC (`(Sort 1) Sort 1)).infer'
#eval (DCC (Λ (Sort 1) (` (Sort 1) Sort 1) (`(Σ (`(Sort 1) Sort 1)) Sort 1))).infer'
#eval (DCC (Id (Σ (Id Sort 2)))).infer'
#eval (DCC (Λ (Sort 2) (Id Sort 2) (Id (Σ (Id Sort 2))))).infer'
#eval (DCC (`(Sort 1) Sort 1)).infer'
#eval (DCC (Λ (Sort 1) (`(Sort 1) Sort 1) (`(Σ (`(Sort 1) Sort 1)) Sort 1))).infer'
#eval (DCC ((Σ (`(Sort 1) Sort 1) (Λ (Sort 1) (`(Sort 1) Sort 1) (`(Σ (`(Sort 1) Sort 1)) Sort 2))) (Sort 0))).infer
#eval (Std.format ∘ (·.fst)) <$> (DCC ((Fst (Id Sort 2)) (,(Id Sort 2) (Sort 1) (Sort 0)))).infer
#eval (Std.format ∘ (·.fst)) <$> (DCC ((Snd (Id Sort 2)) (,(Id Sort 2) (Sort 1) (Sort 0)))).infer
#eval (Std.format ∘ (·.fst)) <$> (DCC ((∘ (Id Sort 1) (Id Sort 1)) (Sort 0))).infer

/-
Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1))
Shuoldn't this reduce?

It does.
It does very nicely.

Pretty sure this is just because we need the top-level env rule.
-/


#eval Expr.infer' (DCC (Id Sort 1))
#eval Expr.infer' (DCC (Λ (Sort 1) (`(Sort 1) Sort 1) (Fst (`(Sort 1) Sort 1))))

-- B := `Sort 1 Sort
-- A := Sort 1
#eval (DCC (`Sort 1 (`(Sort 1) Sort 1))).infer'
#eval (DCC (Λ (Sort 1) (` (Sort 1) Sort 1) (Fst (` (Sort 1) Sort 1)))).infer'
#eval (DCC (Id Sort 1)).infer'
#eval (DCC (Λ (Sort 1) (` (Sort 1) Sort 1) (Fst (` (Sort 1) Sort 1)))).infer'

open Dsl in
#eval (DCC (∘ (Id (Sort 1)) (Id (Sort 1)))).infer'
open Dsl in
def mk_test_pair : Expr :=
  DCC ((⟨,⟩(Λ (Sort 1) (`(Sort 1) (Sort 1)) (`(Σ (`(Sort 1) (Sort 1))) (Sort 1))) (Id Sort 1) (Λ Sort 1 (`(Sort 1) Sort 1) (Fst (`(Sort 1) Sort 1)))) (& Sort 0))

def test_pair : Except (TypeError mk_test_pair) Expr := (·.fst) <$> mk_test_pair.infer
#eval GenericExpr.red_aff (DCC (((`(Sort 2) (∘ (Σ (`(Sort 1) (`(Sort 1) (Sort 1)))) (* (Sort 1)))) (! (Sort 1))) (& (Sort 0))))
--#eval GenericExpr.canonicalize
#eval test_pair

/-
Want to change pair type so that it aligns with the environment pattern.
Not necessary, since f and g are points.

why does β need to receive a couple? something with duplication I recall.
-/

#eval (Std.format ∘ (·.fst)) <$> (DCC (Id(Sort 1))).infer

def test_id_nested : Option Expr := do
  let ⟨t, _⟩ ← (DCC (Id Sort 1)).infer.toOption
  (·.fst) <$> (DCC ((Id t) (Id Sort 1) (Sort 0))).infer.toOption

#eval test_id_nested

/-
(some (Coup(`(Sort 1,
       (Σ(Λ(Sort 1, `(Sort 1, Sort 1),
            Π(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Coup(`(Sort 1, Sort 1))))) ∘
              Fst(`(Sort 1, Sort 1))))
          Sort 0)))))

this is exactly as expected, except the environment is discarded? Why?
I think this is due to the pair type.

this could actually be due to η-reduction...
-/

/-
Expected:

Coup(Σ(Λ(Sort 1, `(Sort 1, Sort 1),
            Π(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Coup(`(Sort 1, Sort 1))))) ∘
              Fst(`(Sort 1, Sort 1)))))
-/

/-

-/

--#eval (Std.format ∘ (·.fst)) <$> (DCC (⟨Id(Sort 1), ⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Id(Coup(`(Sort 1, Sort 1))))⟩⟩ (Sort 0))).infer

/-
This should eta reduce
(Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `(Coup(Σ(`(⊤, `(Sort 1, Sort 1)))), Sort 1)) ∗)


-/

/-

-/

-- (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)

#eval (DCC (Id Sort 1)).infer'
#eval ((· == (DCC ((Π (Id Sort 2) (`(Sort 2) (`(Sort 1) Sort 1))) Sort 1)))∘ (·.fst)) <$> (DCC (Id Sort 1)).infer

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

#eval (Std.format ∘ (·.fst)) <$> (DCC (Id Sort 1)).infer

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

#eval (·.fst) <$> (DCC (Λ (Sort 1) (`(Sort 1) Sort 1) (Fst (`(Sort 1) Sort 1)))).infer

#eval (DCC ((Π (Id Sort 2) (Λ (Sort 2) (Id Sort 2) (`(Σ (Id Sort 2)) Sort 1))) Sort 1)).reduce_all


/-
Maybe my example is wrong? We should try it with the couple example from before.
-/

/-
(Σ(`(⊤, `(Π(Id(Sort 2), `(Sort 2, (Λ(Sort 2, Id(Sort 2), `((Σ(`(⊤, Id(Sort 2))) ∗), Sort 1)) Sort 1))), Sort 1))) ∗)

expected

fn type:
Π(Id(Sort 2), `(Sort 2, (Λ(Sort 2, Id(Sort 2), `((Coup(Id(Sort 2))) ∗), Sort 1)) Sort 1)))

Id(Sort 1)
-/

#eval (Std.format ∘ (·.fst)) <$> (DCC (Id Sort 1)).infer
#eval (DCC (Id Sort 1)).infer'

#eval (DCC (Id Sort 2)).infer'
#eval (DCC (refl (Id Sort 2))).infer'
#eval (DCC ((refl (Id Sort 2)) (& Sort 1) (& Sort 0))).infer'
#eval (DCC (refl(Id(Sort 2)))).infer'

--#eval (DCC Id(Sort 0)).infer'

/-

-/

