import Dcc.Ast2

  -- Decreasing measure
-- function arity decreases with each argument
inductive Expr.TySize : Expr → ℕ → Prop
  | fst  : Expr.TySize (SK fst) 1
  | snd  : Expr.TySize (SK snd) 1
  | comp : Expr.TySize f m
    → Expr.TySize g n
    → Expr.TySize (SK f ∘ g) (m + n).succ
  | coup  : Expr.TySize (SK (a, b)) 0
  | pair  : Expr.TySize a m
    → Expr.TySize b n
    → Expr.TySize (SK ⟨a, b⟩) (m + n).succ
  | curr  : Expr.TySize x m
    → Expr.TySize (SK Λ(x)) m.succ
  | nil   : Expr.TySize (SK nil) 0
  | comb  : Expr.TySize (.comb c) 0
  | hole  : Expr.TySize (SK __ ∶ t) 0
  | srt   : Expr.TySize (SK Sort m) 0
  | app   : Expr.TySize f n
    → Expr.TySize x m
    → Expr.TySize (SK (f x)) (n + m)

inductive Expr.RedTy : Expr → Expr → Prop
  | comp      : Expr.RedTy (SK ((x ∘ y) z)) (SK (x (y z)))
  | fst       : Expr.RedTy (SK (fst (x, y))) x
  | snd       : Expr.RedTy (SK (snd (x, y))) y
  | curr      : Expr.RedTy (SK ((Λ(x) y z))) (SK (x (y, z)))
  | pair      : Expr.RedTy (SK (⟨f, g⟩ (a, b))) (SK ((f a), (g b)))
  | congrFun  : Expr.RedTy f f'
    → Expr.RedTy (SK (f x)) (SK (f' x))

theorem Expr.all_size : ∃ n, Expr.TySize e n := by
  induction e
  · exact ⟨0, .hole⟩
  · exact ⟨0, .srt⟩
  · exact ⟨0, .comb⟩
  case app f x ih₁ ih₂ =>
    have ⟨n, hn⟩ := ih₁
    have ⟨m, hm⟩ := ih₂
    exact ⟨n + m, .app hn hm⟩
  case comp f g ih₁ ih₂ =>
    have ⟨m, h₁⟩ := ih₁
    have ⟨n, h₂⟩ := ih₂
    exact ⟨(m + n).succ, .comp h₁ h₂⟩
  · exact ⟨0, .nil⟩
  · exact ⟨1, .fst⟩
  · exact ⟨1, .snd⟩
  case curr f ih =>
    have ⟨m, h₁⟩ := ih
    exact ⟨m.succ, .curr h₁⟩
  · exact ⟨0, .coup⟩
  case pair f g ih₁ ih₂ =>
    have ⟨m, h₁⟩ := ih₁
    have ⟨n, h₂⟩ := ih₂
    exact ⟨(m + n).succ, .pair h₁ h₂⟩

