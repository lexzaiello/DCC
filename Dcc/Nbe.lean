import Dcc.Ast
import Dcc.Types
import Dcc.Nbe.RunEvalApply
import Dcc.Nbe.RunQuote

namespace Semantic

open Semantic

end Semantic

namespace Expr

open Semantic

inductive Nbe : Expr → Expr → Type
  | mk : Eval [] e v → v.Quote 0 e' → Nbe e e'

def nbe (e : Expr) : Option ((e' : Expr) × Nbe e e') := do
  let ⟨e₁, h₁⟩ ← e.evaluate []
  dbg_trace repr e₁
  let ⟨_, h₂⟩ ← e₁.quote 0
  return ⟨_, .mk h₁ h₂⟩

def nbe! (e : Expr) : Expr :=
  match e.nbe with
  | .some ⟨e', _⟩ => e'
  | _ => e

#eval Sigma.fst <$> nbe (DCC Id(Sort 1) ∘' Id(Sort 1))
#eval Sigma.fst <$> nbe (DCC `(Sort 1, Sort 1))
#eval Sigma.fst <$> nbe (DCC Id(Sort 1))
#eval Sigma.fst <$> evaluate [] (DCC Eql(Id(Sort 2)))
#eval Sigma.fst <$> nbe (DCC Eql(Id(Sort 2)))
#eval Sigma.fst <$> nbe (DCC (Π(Id(Sort 3), `(Sort 3, Π(!<Id(Sort 2)>, Eql(Id(Sort 2))))) !(Sort 2)))

end Expr
