import Dcc.Ast
import Dcc.Judge
import Dcc.Types

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1) ∘' Id(Sort 1)).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1) (Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fst(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1)) )(Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Σ(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1)) )(Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fstc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Sndc(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ((Id(Sort 1) ∘' Id(Sort 1)) (Sort 0))).infer

def mk_test_pair : Expr :=
  DCC (⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1)))⟩ (Sort 0))

def test_pair : Option Expr := Sigma.fst <$> mk_test_pair.infer

#eval Expr.reduce_all <$> test_pair

#eval Std.format test_pair

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
(some (Coup(`(Sort 1,
       (Σ(Λ(Sort 1, `(Sort 1, Sort 1),
            Π(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Coup(`(Sort 1, Sort 1))))) ∘
              Fstc(`(Sort 1, Sort 1))))
          Sort 0)))))

this is exactly as expected, except the environment is discarded? Why?
I think this is due to the pair type.

this could actually be due to η-reduction...
-/

/-
Expected:

Coup(Σ(Λ(Sort 1, `(Sort 1, Sort 1),
            Π(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Coup(`(Sort 1, Sort 1))))) ∘
              Fstc(`(Sort 1, Sort 1)))))
-/

/-

-/

--#eval (Std.format ∘ Sigma.fst) <$> (DCC (⟨Id(Sort 1), ⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Id(Coup(`(Sort 1, Sort 1))))⟩⟩ (Sort 0))).infer

/-
This should eta reduce
(Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `(Coup(Σ(`(⊤, `(Sort 1, Sort 1)))), Sort 1)) ∗)


-/

/-

-/

-- (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)

#eval ((· == (DCC (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)))∘ Expr.reduce_all ∘ Sigma.fst) <$> (DCC Id(Sort 1)).infer

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

#eval Sigma.fst <$> (DCC Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1)))).infer

#eval (DCC (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)).reduce_all


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

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1)).infer

/-
Old way (env is here to calculate types of x and f given f_α and f_β):
App(f_α, f_β) (env, (x, f)) := x f

Background: Fstc is just a macro for my Fst combinator. Fst explicitly takes the environment in Σ(...) env. Couples don't depend on an environment, snd just depends on fst. Pairs, for example, are of a sigma type similarly to couples, except couples don't have relevant environment information, but pairs do, so Fst(f_β) env is for any Σ, whereas Fstc(β) = Fst(`(⊤, β)) ∗. ⊤ is unit type, ∗ is unit constructor, and β is the snd element type dependent on the first element. Same thing for Sndc.

Remember, new pair rule (required for snd to actually depend on fst):
⟨f, g⟩ x = (f x, g x (f x)⟩

Derivation:

App(f_α, f_β) ⟦...some env handling stuff⟧(env, ⟦...⟧(x, f)) = x f
= (Sndc(...) ∘ ⟨Fstc(...), Sndc(...)⟩ ∘ Sndc(...)) (env, (x, f))
= (Sndc(...) ∘ ⟨Fstc(...), Sndc(...)⟩) (x, f)
= Sndc(...) (x, Sndc(...) (x, f) x)
= Sndc(...) (x, f x)
= (f x)
-/
