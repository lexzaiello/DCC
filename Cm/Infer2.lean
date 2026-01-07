import Cm.Ast
import Cm.Eval2
import Cm.Error

def reduce_unquote : Expr → Expr
  | ⟪₂ quoted :e ⟫ => (do_step e).toOption.getD e
  | e => e

/-
Our read didn't run in time.
-/

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

    let quoted_arg := match t_arg with
      | ⟪₂ Data ⟫ => arg
      | _ => ⟪₂ quoted :arg ⟫

    match ← do_step ⟪₂ :: exec (:: :t_f (:: :quoted_arg nil)) ⟫ with
    | ⟪₂ :: :t_in (:: :xs nil) ⟫
    | ⟪₂ :: :t_in :xs ⟫ =>
      if reduce_unquote t_in == t_arg then
        pure xs
      else
        Except.error <| .mismatch_arg t_in t_arg ⟪₂ :f :arg ⟫ .none
    | t => Except.error <| .not_type t
  | ⟪₂ , ⟫ => Except.error <| .stuck ⟪₂ , ⟫

#eval infer ⟪₂ :: Data (:: Data Data) ⟫
#eval infer ⟪₂ I Data Data ⟫
#eval infer ⟪₂ K Data (I Data) Data Data ⟫

#eval infer ⟪₂ S Data (I Data) ⟫

#eval exec_op ⟪₂ ((:: ((:: exec) ((:: ((:: assert) read)) ((:: read) nil)))) apply) ⟫ ⟪₂ :: Data nil ⟫
