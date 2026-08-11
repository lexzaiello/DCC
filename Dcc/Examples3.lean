import Dcc.Ast
import Dcc.Judge3
import Dcc.Types

/-
Can quot be derived?

`(β, x) = Λ(α, Λ(
-/

#eval (Std.format ∘ Sigma.fst) <$> (DCC Id(Sort 1) ∘' Id(Sort 1)).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1) (Sort 0))).infer
#eval (DCC `(Sort 1, Sort 1)).infer'
#eval (DCC Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1))).infer'
#eval (DCC Id(Coup(Id(Sort 2)))).infer'
#eval (DCC (Π(Id(Sort 1), `(Sort 1, Π(Id(Sort 1), Λ(Sort 1, Id(Sort 1), Id(Sort 2))))) Sort 1)).reduce_all
#eval (DCC Λ(Sort 2, Id(Sort 2), Id(Coup(Id(Sort 2))))).infer'
#eval (DCC `(Sort 1, Sort 1)).infer'
#eval (DCC Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1))).infer'
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Σ(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 2)))(Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Fst(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC (Snd(Id(Sort 2)) ⟦Id(Sort 2)⟧(Sort 1, Sort 0))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ((Id(Sort 1) ∘' Id(Sort 1)) (Sort 0))).infer

/-
Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1))
Shuoldn't this reduce?

It does.
It does very nicely.

Pretty sure this is just because we need the top-level env rule.
-/


#eval Expr.infer' (DCC Id(Sort 1))
#eval (DCC (Π(Id(Sort 2), `(Sort 2, Π(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1)))))
   Sort 1)).red_eta'
#eval Expr.infer' (DCC Λ(Sort 1, `(Sort 1, Sort 1), Fst(`(Sort 1, Sort 1))))

#eval (DCC Λ(Sort 1, `(Sort 1, Sort 1), Fst(`(Sort 1, Sort 1)))).infer'
#eval (DCC (`(Sort 2, Π(`(Sort 1, Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1)))) (Sort 1))).reduce_all
#eval (DCC Id(Sort 1)).infer'

#eval (DCC Λ(Sort 1, `(Sort 1, Sort 1), `(Coup(`(Sort 1, Sort 1)), Sort 1))).reduce_all

#eval (DCC Id(Sort 1)).infer'
#eval (DCC (`(Sort 2, `(Sort 1, Sort 1)) Sort 1)).reduce_all
#eval (DCC Λ(Sort 1, `(Sort 1, Sort 1), Fst(`(Sort 1, Sort 1)))).infer'


def mk_test_pair : Expr :=
  DCC (⟦`(Sort 1, `(Sort 1, Sort 1))⟧⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Fst(`(Sort 1, Sort 1)))⟩
    &(Sort 0))

def test_pair : Except (TypeError mk_test_pair) Expr := Sigma.fst <$> mk_test_pair.infer

#eval Expr.reduce_all <$> test_pair
#eval Expr.reduce_all mk_test_pair

#eval Std.format test_pair

/-
Want to change pair type so that it aligns with the environment pattern.
Not necessary, since f and g are points.

why does β need to receive a couple? something with duplication I recall.
-/

#eval (Std.format ∘ Sigma.fst) <$> (DCC (Id(Sort 1))).infer

#eval (Std.format ∘ Sigma.fst) <$> (DCC (Λ(Sort 2, Id(Sort 2), Fst(Id(Sort 2))) (Sort 1) (Sort 0))).infer

def test_id_nested : Option Expr := do
  let ⟨t, _⟩ ← (DCC Id(Sort 1)).infer.toOption
  Sigma.fst <$> (DCC (Id(t) Id(Sort 1) (Sort 0))).infer.toOption

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

--#eval (Std.format ∘ Sigma.fst) <$> (DCC (⟨Id(Sort 1), ⟨Id(Sort 1), Λ(Sort 1, `(Sort 1, Sort 1), Id(Coup(`(Sort 1, Sort 1))))⟩⟩ (Sort 0))).infer

/-
This should eta reduce
(Λ(⊤, Σ(`(⊤, `(Sort 1, Sort 1))), `(Coup(Σ(`(⊤, `(Sort 1, Sort 1)))), Sort 1)) ∗)


-/

/-

-/

-- (Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), `(Coup(Id(Sort 2)), Sort 1))) Sort 1)

#eval (DCC Id(Sort 1)).infer'
#eval ((· == (DCC (Π(Id(Sort 2), `(Sort 2, `(Sort 1, Sort 1))) Sort 1)))∘ Sigma.fst) <$> (DCC Id(Sort 1)).infer

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

#eval Sigma.fst <$> (DCC Λ(Sort 1, `(Sort 1, Sort 1), Fst(`(Sort 1, Sort 1)))).infer

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
#eval (DCC Id(Sort 1)).infer'

#eval (DCC ((Sort 1 : Sort 2) → ((Sort 3 : Sort 4) → Sort 5))).reduce_all

#eval (DCC Id(Sort 2)).infer'
#eval (DCC refl(Id(Sort 2))).infer'
#eval (DCC (refl(Id(Sort 2)) &(Sort 1) &(Sort 0))).infer'
#eval (DCC (refl(Id(Sort 2)))).infer'

--#eval (DCC Id(Sort 0)).infer'

/-

-/

#eval (DCC (refl(`(Sort 0, (Sort 0 : Sort 1) → Sort 0)) &(⊤) &(Id(Sort 0)))).infer'
#eval (DCC (Id(Id(Sort 0) = Id(Sort 0) ∘' Id(Sort 0))
  (refl(`(Sort 0, (Sort 0 : Sort 1) → Sort 0)) &(⊤) &(Id(Sort 0))))).infer'

#eval (DCC (Id(Id(Sort 0) = Id(Sort 0) ∘' Id(Sort 0) ∘' Id(Sort 0))
  (refl(Id(Sort 1))
    &((Π(Id(Sort 1)
      , `(Sort 1, `(Sort 0, Sort 0))) Sort 0))
    &(Id(Sort 0))))).infer.isOk

/-

-/
#eval (DCC (Π(Id(Sort 1), `(Sort 1, `(Sort 0, Sort 0))) Sort 0)).infer'

def pair.{u} {τ_c : Type u} (u v : Level) (A B C : @GenericExpr τ_c) : @GenericExpr τ_c :=
  let τ₁    := DCC? A
  let τ₂    := DCC? `(A, B)
  let τ₃    := DCC? Coup(`(A, B))
  let τ_fn₀ := DCC? ((B : Sort v) → C)
  let τ_fn  := DCC? (A : Sort u) → τ_fn₀
  let τ₄    := DCC? `(Coup(`(A, B)), τ_fn)
  let M     := DCC? Snd(`(A, τ_fn₀)) ∘' ⟦`(Coup(τ₄), `(A, τ_fn₀))⟧⟨Fst(τ₂) ∘' Fst(τ₄), Snd(τ₄)⟩


  ---M
  DCC? Snd(τ₄)

  /-DCC? Λ(τ₁, τ₂,
          Λ(τ₃, τ₄, Snd(`(B, C)) ∘' ⟦`(B, C)⟧⟨Fst(τ₂) ∘' Fst(τ₄), M⟩))-/

  /-DCC? Λ(τ₁, τ₂,
          Λ(τ₃, τ₄, Eval(τ_fn₀, `(τ_fn₀, B), Id(τ_fn₀)) ∘' ⟦`(τ_fn₀, B)⟧⟨M, Snd(τ₂) ∘' Fst(τ₄)⟩))-/

#eval (pair 1 0 (DCC Sort 0) (DCC ⊤) (DCC ⊤)).infer'
#eval (DCC ⟦`((Sort 0 : Sort 1) → (⊤ : Sort 0) → ⊤,
                         Sort 0)⟧⟨Snd(`(Coup(`(Sort 0, ⊤)), (Sort 0 : Sort 1) → (⊤ : Sort 0) → ⊤)),
                                                   (Fst(`(Sort 0, ⊤)) ∘'
                                                      Fst(`(Coup(`(Sort 0, ⊤)), (Sort 0 : Sort 1) → (⊤ : Sort 0) → ⊤)))⟩).infer'

/-
Example of church isomorphism:

pair vs boolean selector:

pair := λ x y f => f x y
fst := λ p => p (λ a b => a)
snd := λ p => p (λ a b => a)

let τ₁ := A
let τ₂ := `(A, B)
let τ₃ := Coup(`(A, B))
let τ_fn₀ := ((B : Sort v) → C)
let τ_fn := (A : Sort u) → τ_fn₀
let τ₄ := `(Coup(`(A, B)), τ_fn)

? := Snd(τ₄)

M := Eval(τ_fn, `(τ_fn, B), Id(τ_fn)) ∘' ⟦`(τ_fn, B)⟧⟨Snd(τ₄), Fst(τ₂) ∘' Fst(τ₄)⟩

pair := Λ(τ₁, τ₂,
          Λ(τ₃, τ₄, Eval(τ_fn₀, B, Id(τ_fn₀)) ∘' ⟦`(τ_fn₀, B)⟧⟨M, Snd(τ₂) ∘' Fst(τ₄)⟩))

true := λ x y => x
false := λ x y => y

pair₂ := λ x y b => b x y
fst₂  := λ p => p true
snd₂  := λ p => false
-/
