import Dcc.Ast2

inductive Expr.RedTm : Expr → Expr → Prop
  | k        : RedTm (SK (K.{[m, n]} α β x y)) x
  | k'       : RedTm (SK (K'.{[m, n]} α β x y)) x
  | s        : RedTm (SK (S.{[m, n, o]} α β γ x y z)) (SK ((x z) (y z)))
  | congrFun : RedTm f f' → RedTm (SK (f x)) (SK (f' x))
  | congrArg : RedTm x x' → RedTm (SK (f x)) (SK (f x'))

def Expr.step_tm? : Expr → Option Expr
  | (SK (K.{[_m, _n]} _α _β x _y)) => .some x
  | (SK (K'.{[_m, _n]} _α _β x _y)) => .some x
  | (SK (S.{[_m, _n, _o]} _α _β _γ x y z)) => .some (SK ((x z) (y z)))
  | SK ((f x)) => match f.step_tm?, x.step_tm? with
    | .some f', _ => .some (SK (f' x))
    | _, .some x' => .some (SK (f x'))
    | _, _ => .none
  | _ => .none

theorem step_tm?_sound : Expr.step_tm? e = .some e' → Expr.RedTm e e' := by
  intro h
  unfold Expr.step_tm? at h
  split at h
  · simp_all only [Option.some.injEq]
    exact .k
  · simp_all only [Option.some.injEq]
    exact .k'
  · simp_all only [Option.some.injEq]
    exact h.symm ▸ .s
  · rename_i x f x' _ _  ih
    split at h
    · simp_all only [imp_false, Option.some.injEq]
      rename_i h_f_step
      exact h.symm ▸ .congrFun (step_tm?_sound h_f_step)
    · simp_all only [imp_false, Option.some.injEq]
      rename_i h_x_step _
      exact h.symm ▸ .congrArg (step_tm?_sound h_x_step)
    · contradiction
  · contradiction
