import Dcc.Ast
import Dcc.Eval
import Dcc.Judge
import Dcc.Tactic

open tactic in theorem invert_k : Judge α ⸨K.{[m, n]} α β x y⸩ → Judge (Srt m) α ∧ Judge ((~> n.succ) α, (Srt n)) β ∧ Judge α x ∧ Judge ⸨β x⸩ y := by
  intro h
  repeat cases_spine
  constructor
  · cases_conv *
    reduce_equations
    simp_all
  constructor
  · apply Judge.conv
    · assumption
    cases_conv *
    rename_i ih₁ ih₂
    have h := ParRed.reduce_sound ((ParRed.reduce_complete ih₁).trans (ParRed.reduce_complete ih₂).symm)
    cases h
    rename_i h _
    have hβ := ParRed.reduce_sound (ParRed.reduce_complete h).symm
    refine ⟨_, hβ, ?_⟩
    smart_reduce show reduction
    smart_reduce close decide
  sorry

theorem preservation : Judge t e → ParRed e e' → Judge t e' := by
  intro ht₁ hr
  induction ht₁ generalizing e'
  · cases hr
    exact .K
  · cases hr
    exact .K'
  · cases hr
    exact .S
  · cases hr
    exact .Srt
  · cases hr
    exact .Pi
  

