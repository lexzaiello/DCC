import Dcc.Ast
import Dcc.Nbe.RunEvalApply
import Dcc.Nbe.RunQuote

namespace Expr

open Semantic

inductive Nbe : Expr → Expr → Type
  | mk : Eval [] e v → v.Quote 0 e' → Nbe e e'

def nbe (e : Expr) : Option ((e' : Expr) × Nbe e e') := do
  let ⟨e₁, h₁⟩ ← e.evaluate []
  let ⟨_, h₂⟩ ← e₁.quote 0
  return ⟨_, .mk h₁ h₂⟩

def nbe! (e : Expr) : Expr :=
  match e.nbe with
  | .some ⟨e', _⟩ => e'
  | _ => e

end Expr
