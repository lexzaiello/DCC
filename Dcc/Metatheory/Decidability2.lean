import Dcc.Judge2

namespace GenericExpr

theorem Judge₂.complete.pair.{u_1} {τ_c : Type u_1} [inst : DecidableEq τ_c] [inst_1 : BEq τ_c]
  {f : GenericExpr τ_c} {m : Level} {f_β x_α β g f_α₂ f_β₂ α γ γ' β₂ γ₂ τ : GenericExpr τ_c}
  (h_t_f : f.Judge₂ (((GenericExpr.sort m).id.pi f_β).app x_α)) (h_r_β : (f_β.app x_α).Reduces₂ β)
  (h_t_g : g.Judge₂ ((f_α₂.pi f_β₂).app α)) (h_r_γ : γ.Reduces₂ γ') (h_r_f_β : (f_β₂.app α).Reduces₂ (β₂.pi γ₂))
  (h_r_γ₂ : γ₂.Reduces₂ γ') (h_r_β₂ : β₂.Reduces₂ β) (h_r_α₂ : (f_α₂.app α).Reduces₂ x_α)
  (h_r_τ : (pair.type x_α β γ' m).Reduces₂ τ)
  (ih₁ : f.infer₂ = Except.ok ⟨((GenericExpr.sort m).id.pi f_β).app x_α, h_t_f⟩)
  (ih₂ : g.infer₂ = Except.ok ⟨(f_α₂.pi f_β₂).app α, h_t_g⟩) :
  (γ.pair f g).infer₂ = Except.ok ⟨τ, h_t_f.pair h_r_β h_t_g h_r_γ h_r_f_β h_r_γ₂ h_r_β₂ h_r_α₂ h_r_τ⟩ := by
  dsimp only [infer₂]
  rw [ih₁, ih₂]
  dcc_aesop!

set_option maxHeartbeats 1000000000000 in
theorem Judge₂.complete {e : GenericExpr τ_c} [DecidableEq τ_c] [BEq τ_c] (h : Judge₂ e t) : infer₂ e = .ok ⟨t, h⟩ := by
  induction h
  case pi h_t_f_α h_arr h_t_f_β hr₁ h_t_pi_f_β hr₂ ih₁ ih₂ =>
    dsimp only [infer₂]
    rw [ih₁, ih₂]
    dsimp only
    rw [h_arr.read_complete]
    dsimp only
    cases hr₁.complete
    rw [h_t_pi_f_β.complete]
    dsimp
    cases hr₂.complete
    grind
  case pair h_t_f h_r_β h_t_g h_r_γ h_r_f_β h_r_γ₂ h_r_β₂ h_r_α₂ h_r_τ ih₁ ih₂ =>
    apply Judge₂.complete.pair <;> assumption
  case app h_t_f h_r_α h_t_x h_deq hr ih₁ ih₂ =>
    dsimp only [infer₂]
    rw [ih₁, ih₂]
    dsimp only
    dcc_aesop!
  case eval ih₁ ih₂ ih₃ =>
    dsimp only [infer₂]
    rw [ih₁, ih₂, ih₃]
    dsimp only
    dcc_aesop!
  case unbox hr ih =>
    dsimp only [infer₂]
    rw [ih]
    dsimp only
    cases hr.complete
    grind
  case _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ =>
    dsimp only [infer₂]
    try (first
      | grind
      | dcc_aesop!)

def decide_judge {τ_c : Type u} [BEq τ_c] [DecidableEq τ_c]
  {e τ : GenericExpr τ_c} : (Judge₂ e τ) ⊕ (Judge₂ e τ → PLift False) :=
  match heq₀ : e.infer₂ with
  | .ok ⟨τ₂, h⟩ =>
    if heq : τ₂ = τ then
      .inl (heq ▸ h)
    else
      .inr (fun h => by
        have h := h.complete
        simp_all)
  | .error _ => .inr (fun h => by
    have h := h.complete
    simp_all)

/-instance {e : GenericExpr τ_c} [DecidableEq τ_c] [BEq τ_c] : Decidable (Judge₂ e t) :=
  match heq : infer₂ e with
  | .ok ⟨τ, ⟨h⟩⟩ =>
    if heq₂ : τ = t then
      .isTrue (heq₂ ▸ h)
    else
      .isFalse (fun h => by
        have hn := h.complete
        grind)
  | .error _e => .isFalse (fun h => by
    have hn := h.complete
    grind)-/

end GenericExpr
