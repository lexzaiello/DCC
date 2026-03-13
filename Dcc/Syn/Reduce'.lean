import Dcc.Syn.JudgePi

open Expr in def reduce' (e : Expr) : ((e' : Expr) × (PLift <| ParRed e e')) :=
  match e with
  | Expr.app (.app (.I _m) _α) x =>
    let ⟨x', h⟩ := reduce' x
    ⟨x', ⟨.I h.down⟩⟩
  | ⸨(.K _m _n) _α _β x _y⸩ =>
    let ⟨x', h⟩ := reduce' x
    ⟨x', ⟨.K h.down⟩⟩
  | ⸨(.K' _m _n) _α _β x _y⸩ =>
    let ⟨x', h⟩ := reduce' x
    ⟨x', ⟨.K' h.down⟩⟩
  | ⸨(.S _m _n _o) _α _β _γ x y z⸩ =>
    let ⟨x', h₁⟩ := reduce' x
    let ⟨y', h₂⟩ := reduce' y
    let ⟨z', h₃⟩ := reduce' z
    ⟨((x'.app z').app (y'.app z')), ⟨.S h₁.down h₂.down h₃.down⟩⟩
  | ⸨(.Pi m α β) x⸩ =>
    let ⟨α', h₁⟩ := reduce' α
    let ⟨β', h₂⟩ := reduce' β
    let ⟨x', h₃⟩ := reduce' x
    ⟨Expr.Pi m (α'.app x') (β'.app x'), ⟨.Pi h₁.down h₂.down h₃.down⟩⟩
  | (.Pi m α β) =>
    let ⟨α', h₁⟩ := reduce' α
    let ⟨β', h₂⟩ := reduce' β
    ⟨Expr.Pi m α' β', ⟨.Pival h₁.down h₂.down⟩⟩
  | ⸨.next f _x⸩ =>
    let ⟨f', h₁⟩ := reduce' f
    ⟨f', ⟨.next h₁.down⟩⟩
  | ⸨.read e⸩ =>
    let ⟨e', h₁⟩ := reduce' e
    ⟨e', ⟨.read h₁.down⟩⟩
  | ⸨.assert f _x⸩ =>
    let ⟨f', h₁⟩ := reduce' f
    ⟨f', ⟨.assert h₁.down⟩⟩
  | ⸨.app' π f g x⸩ =>
    let ⟨f', h₁⟩ := reduce' f
    let ⟨g', h₂⟩ := reduce' g
    let ⟨x', h₃⟩ := reduce' x
    ⟨(Expr.app π (f'.app x')).app (g'.app x'), ⟨.app' h₁.down h₂.down h₃.down⟩⟩
  | ⸨f x⸩ =>
    let ⟨f', h₁⟩ := reduce' f
    let ⟨x', h₂⟩ := reduce' x

    ⟨f'.app x', ⟨.app h₁.down h₂.down⟩⟩
  | .K' m n => ⟨.K' m n, ⟨.refl_K'⟩⟩
  | .K m n => ⟨.K m n, ⟨.refl_K⟩⟩
  | .S m n o => ⟨S m n o, ⟨.refl_S⟩⟩
  | .I m => ⟨I m, ⟨.refl_I⟩⟩
  | .Srt m => ⟨Srt m, ⟨.refl_Srt⟩⟩
  | .next => ⟨.next, ⟨.refl_next⟩⟩
  | .read => ⟨.read, ⟨.refl_read⟩⟩
  | .assert => ⟨.assert, ⟨.refl_assert⟩⟩
  | .app'   => ⟨.app', ⟨.refl_app'⟩⟩
  | .hole   => ⟨.hole, ⟨.refl_hole⟩⟩

theorem reduce'.sound : reduce' A = ⟨B, hpr⟩ → ParRed A B := fun _ => hpr.down

theorem ParRed.triangle : ParRed A B → ParRed B (reduce' A).fst := fun h => by
  induction h
  repeat (apply reduce'.sound; rfl)
  repeat (unfold reduce'; simp; assumption)
  · unfold reduce'; simp
    apply ParRed.app
    repeat (apply ParRed.app; repeat assumption)
  · unfold reduce'; simp
    apply ParRed.Pival
    repeat (apply ParRed.app; repeat assumption)
  · unfold reduce'; simp
    apply ParRed.Pival
    repeat assumption
  · unfold reduce'; simp
    assumption
  · unfold reduce'; simp
    assumption
  · unfold reduce'; simp
    assumption
  · unfold reduce'; simp
    apply ParRed.app
    apply ParRed.app
    exact ParRed.refl
    repeat (apply ParRed.app; repeat assumption)
  case app f f' x x' h_f' h_x' h_red_f h_red_x =>
    unfold reduce' at h_red_f
    split at h_red_f
    repeat (simp_all; unfold reduce'; simp; apply ParRed.app; repeat assumption)
    simp_all
    unfold reduce'
    simp
    cases h_f'
    apply ParRed.Pi
    
    /-cases h_f'
    · unfold reduce'
      simp
      apply ParRed.app
      apply reduce'.sound
      rfl
      assumption
    · apply ParRed.app
      apply reduce'.sound
      rfl
      assumption
    · apply ParRed.app
      apply reduce'.sound
      rfl
      assumption
    · apply ParRed.app
      apply reduce'.sound
      rfl
      assumption
    · apply ParRed.app
      apply reduce'.sound
      rfl
      assumption
    · apply ParRed.app
      apply reduce'.sound
      rfl
      assumption
    · apply ParRed.app
      apply reduce'.sound
      rfl
      assumption
    · unfold reduce'
      simp
      apply ParRed.read
      assumption
    repeat (unfold reduce'; simp; apply ParRed.app; assumption; assumption)
    unfold reduce'
    simp
    unfold reduce' at h_red_f
    cases h_red_f
    apply ParRed.Pi
    repeat assumption
    repeat (unfold reduce'; simp; apply ParRed.app; repeat assumption)
    case app f f' x x' h_f h_x =>
      unfold reduce' at h_red_f
      simp at h_red_f
      unfold reduce'
      simp
     
      sorry-/
