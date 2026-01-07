import Cm.Ast

inductive Error where
  | mismatch_arg (t_expected : Expr)
    (t_actual : Expr)
    (at_app : Expr)
    (pos : Option ℕ) : Error
  | not_type (e : Expr) : Error
  | short_context (Γ : Expr) : Error
  | stuck (e : Expr) : Error
  | combine : Error
    → Error
    → Error

def Error.toString : Error → String
  | .mismatch_arg expected actual in_e pos =>
    s!"argument type mismatch.
expected {expected},
but found {actual}
in {in_e}
at tape position {pos}"
  | .not_type e => s!"expected a type, but found {e}"
  | .short_context Γ => s!"expected a longer context, but found {Γ}"
  | .stuck e => s!"evaluation is stuck at {e}"
  | .combine e₁ e₂ => s!"{e₁.toString}
{e₂.toString}"

instance : ToString Error where
  toString := Error.toString
