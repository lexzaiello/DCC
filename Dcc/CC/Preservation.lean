import Dcc.CC.Ast
import Dcc.CC.Step2
import Dcc.CC.Judge
import Mathlib.Tactic

namespace Expr

namespace Judge

theorem preserves (h_t : Judge x T) (h_red : Red x x') : Judge x' T := by
  induction h_t generalizing x' with
  | sort | quot | app_e | curr | snd | fst | pair | comp | id =>
    cases h_red
  | coup =>
    cases h_red
    · rename_i h_t_α h_t_β ih₁ ih₂ _ hr
      exact Judge.coup (ih₁ hr) (.conv (by assumption) (.congrArg hr))
    · rename_i h_t_α h_t_β ih₁ ih₂ _ hr
      refine Judge.coup h_t_α (ih₂ hr)
  | app h_t_f h_t_x ih₁ ih₂ =>
    cases h_red with
    | congrArg h_r_x =>
      have h := ih₂ h_r_x
      apply Judge.conv' (Judge.app (by assumption) h)
      exact .congrArg (Red.sigr (by assumption))
    | id =>
      cases h_t_f with
      | id =>
        sorry
      | conv h =>
        cases h with
        | id =>
          rename_i h
          cases h with
          | congrFun =>
            rename_i h
            cases h with
            | congrFun =>
              exact Judge.conv' (by assumption) .quot
            | congrArg =>
              exact Judge.conv' (.conv' (by assumption) (by assumption)) .quot
          | congrArg =>
            rename_i h
            cases h
        | conv =>
          
          sorry
    | app =>
      sorry
  | conv h_t_x h_r_A ih => exact Judge.conv (ih h_red) h_r_A
  | conv' h_t_x h_r_A ih => exact Judge.conv' (ih h_red) h_r_A

end Judge

end Expr
