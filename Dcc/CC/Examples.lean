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

/-
α → α
Π(Id(Sort m), `(Sort m, `(α, α))) α
(some (Π(Id(Sort 3), `(Sort 3, `(Sort 2, (Π(Id(Sort 2), `(Sort 2, `(Sort 1, Sort 2))) Sort 1)))) Sort 2))

`(Sort m, `(α, α))
: (some (Π(Id(Sort 3), `(Sort 3, `(Sort 2, (Π(Id(Sort 2), `(Sort 2, `(Sort 1, Sort 2))) Sort 1)))) Sort 2))


-/
