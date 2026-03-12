import Dcc.Syn.Gen
import Dcc.Syn.InferPi
import Dcc.Syn.JudgePi

open Expr

theorem S_well_typed (h₁ : Judge (Srt m) α) (h₂ : Judge ((~> n.succ) α, (Srt n)) β)
  (h₃ : Judge ((Π' o.succ) α
      , (Π' o.succ) β
      , ⸨next ⸨assert (Srt o)⸩⸩) γ)
  (h₄ : Judge ((Π' o) α, (Π' o) β, γ) x)
  (h₅ : Judge ((Π' n) α, β) y)
  (h₆ : Judge α z) : Judge ⸨γ z ⸨y z⸩⸩ ⸨(S m n o) α β γ x y z⸩ := by
  decide_infer

theorem K_well_typed (h₁ : Judge (Srt m) α) (h₂ : Judge ((~> n.succ) α, (Srt n)) β)
  (h₃ : Judge α x) (h₄ : Judge ⸨β x⸩ y) : Judge α ⸨(K m n) α β x y⸩ := by
  decide_infer

theorem I_well_typed (h₁ : Judge (Srt m) α) (h₂ : Judge α x) : Judge α ⸨(I m) α x⸩ := by
  decide_infer

theorem K'_well_typed (h₁ : Judge (Srt m) α) (h₂ : Judge (Srt n) β)
  (h₃ : Judge α x) (h₄ : Judge β y) : Judge α ⸨(K' m n) α β x y⸩ := by
  decide_infer

theorem Red.preservation (h_step : ParRed x x') (h_t : Judge α x) : Judge α x' := by
  induction h_t
  cases h_step
  decide_infer
  
  sorry
