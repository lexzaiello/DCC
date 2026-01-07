import Cm.Ast
import Cm.Eval2
import Cm.Error

def infer : Expr → Except Error Expr
  | ⟪₂ map ⟫
  | ⟪₂ assert ⟫
  | ⟪₂ next ⟫
  | ⟪₂ fst ⟫
  | ⟪₂ snd ⟫
  | ⟪₂ both ⟫
  | ⟪₂ exec ⟫
  | ⟪₂ read ⟫
  | ⟪₂ apply ⟫
  | ⟪₂ quote ⟫
  | ⟪₂ push_on ⟫
  | ⟪₂ nil ⟫
  | ⟪₂ Data ⟫ => pure ⟪₂ Data ⟫
  | ⟪₂ S ⟫ => pure s_type
  | ⟪₂ I ⟫ => pure i_type
  | ⟪₂ K ⟫ => pure k_type
  | ⟪₂ K' ⟫ => pure k'_type
  | ⟪₂ quoted :_e ⟫ => pure ⟪₂ Data ⟫
  | ⟪₂ :: ⟫ =>
    pure ⟪₂ :: Data (:: Data (:: Data nil)) ⟫
  | ⟪₂ :f :arg ⟫ => do
    let t_f ← infer f
    let t_arg ← infer arg

    match ← do_step ⟪₂ :: exec (:: :t_f (:: :arg nil)) ⟫ with
    | ⟪₂ :: :t_in :xs ⟫ =>
      if t_in == t_arg then
        pure xs
      else
        Except.error <| .mismatch_arg t_in t_arg ⟪₂ :f :arg ⟫ .none
    | t => Except.error <| .not_type t
  | ⟪₂ , ⟫ => Except.error <| .stuck ⟪₂ , ⟫
