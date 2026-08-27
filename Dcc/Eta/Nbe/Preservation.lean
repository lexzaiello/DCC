import Dcc.Eta.Nbe.Hole

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

@[aesop norm (rule_sets := [DccSize]), grind]
def const_size {τ : Type u} (e : GenericExpr τ) : ℕ :=
  match e with
  | DCC[.] ∗ => 1
  | DCC[.] ⊤ => 2
  | DCC[.] ⊥ => 2
  | DCC[.] x = y => (x.const_size + y.const_size) + 1
  | DCC[.] Eql(α)  => α.const_size + 5
  | DCC[.] refl(α) => α.const_size + 5
  | DCC[.] Sort m => m
  | DCC[.] Σ(α, β) => α.const_size + β.const_size + 3
  | DCC[.] `(β, x) => β.const_size + x.const_size + 3
  | DCC[.] ⟦β⟧(x, y) => β.const_size + x.const_size + y.const_size + 1
  | DCC[.] Coup(β) => β.const_size + 1
  | DCC[.] Id(α)      => 1 + α.const_size
  | DCC[.] Fst(α)    => 3 + α.const_size
  | DCC[.] Snd(α)    => 3 + α.const_size
  | DCC[.] Π(α, β) => α.const_size + β.const_size + 2
  | DCC[.] (f ∘' g) => f.const_size + f.const_size + g.const_size + 3
  | DCC[.] (f ∘ g)  => f.const_size + f.const_size + g.const_size + 3
  | DCC[.] (f ∘∘ g)  => f.const_size + f.const_size + g.const_size + 3
  | DCC[.] ⟦β⟧⟨a, b⟩   => β.const_size + a.const_size + a.const_size + b.const_size + 3
  | DCC[.] Λ(α, β, x) => α.const_size + β.const_size + x.const_size + 3
  | DCC[.] !Λ(α, β, x) => α.const_size + (5 * β.const_size) + x.const_size + 5
  | DCC[.] Eval(α, β, x) => α.const_size + β.const_size + x.const_size + 2
  | DCC[.] !(x)   => x.const_size + 1
  | DCC[.] *<α>   => α.const_size + 1
  | DCC[.] &(x)   => 5 * x.const_size + 1
  | DCC[.] !<x>   => x.const_size + x.const_size + x.const_size + 3
  | DCC[.] $<x>   => 5 * x.const_size + 3
  | DCC[.] (f x) => f.const_size + x.const_size
  | .const _ => 1

@[grind ., grind →]
theorem RedAff.decreasing_const (h : RedAff A B) : const_size B < const_size A := by
  induction h <;> grind

@[grind ., grind →, grind! .]
theorem RedAff.congr_decreasing_const (h : RedAff (DCC? (f x)) (DCC? (f y))) : const_size y < const_size x := by
  cases h <;> grind

namespace RedAffNorm

def decreasing?_const (h : RedAffNorm A B) : const_size B.raw ≤ const_size A := by
  match h with
  | ⟨hr, hn⟩ =>
    match hr.cases_head with
    | .inl h =>
      cases h
      dcc_simp
    | .inr ⟨_, h₁, h₂⟩ =>
      have ha := h₁.decreasing_const
      have h_dec := h₁.decreasing
      have hb := decreasing?_const (mk h₂ hn)
      dcc_simp_all
      grind
termination_by size A

def elim_const_size (hrt : RedAffNorm A B) (h_size : const_size B.raw > const_size A := by grind) : False := by
  have h := hrt.decreasing?_const
  grind

end RedAffNorm

end GenericExpr

namespace NormExpr

namespace Hole

theorem box_bigger (e_h : Hole α level hole) : hole.raw.const_size < hole.raw.box.const_size := by
  induction e_h <;> grind

end Hole

open GenericExpr

def Domain.no_mem_hole_app {f : @NormExpr τ_c RedAff}
  (h_dom : Domain f α) (e_h : Hole α.to_eta level ⟨hole, hn_hole⟩)
  (hrt   : RedAff (DCC? (f.to_eta.raw hole)) (DCC? (g hole)))
  (hn    : IsNorm RedAff g) : ¬ g.hole_mem_tm := by
  have h_dom₀ := h_dom.to_eta
  cases h_dom with
  | refl₁ | eql₁ =>
    dcc_simp at e_h
    cases e_h with
    | pure hn => exact (hn .bang).elim
    | bang =>
      dcc_simp at hrt
      have h := hrt.elim_norm (fun ⟨_, h⟩ => match h with
        | .congrFun h => by
          have h' := RedAff.reflect_eta h to_eta_no_hole
          dcc_simp at h'
          expose_names
          exact hn_1 ⟨_, h'⟩
        | .congrArg h => hn_hole ⟨_, h⟩)
      cases h
  | id =>
    dcc_simp at hrt
    expose_names
    have heq' : α.expr_to_eta.id = g := by
      cases hrt with
      | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    exact (heq' ▸ hrt).size_absurd.elim
  | eql₂ =>
    cases e_h with
    | pure hn => exact (hn .bang).elim
    | bang =>
      expose_names
      dcc_simp at hrt
      have heq : (g.app hole.box) = hole.eq hole := by
        cases hrt with
        | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h =>
          exact (hn_hole ⟨_, h⟩).elim
      cases heq
  | refl₂ =>
    cases e_h with
    | pure hn => exact (hn .bang).elim
    | bang =>
      expose_names
      have heq : (g.app hole.box) = ((mk (f_α.refl.app env.box) hn_1).to_eta.raw.app hole.box) := by
        cases hrt with
        | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h =>
          exact (hn_hole ⟨_, h⟩).elim
      exact (heq ▸ hrt).size_absurd.elim
  | unmap =>
    expose_names
    cases e_h with
    | pure hn => exact (hn .bang).elim
    | bang =>
      expose_names
      dcc_simp at hrt
      have heq : (g.app hole.box) = (expr_to_eta f).app hole := by
        match hrt with
        | .congrFun h => exact (hn_map.to_eta ⟨_, h⟩).elim
        | .congrArg (.box₀ h) => exact (hn_hole_1 ⟨_, h⟩).elim
      cases heq
  | fstc =>
    expose_names
    cases e_h with
    | pure hn => exact (hn .coup).elim
    | coup =>
      expose_names
      dcc_simp at hrt
      have heq : hole₁ = (g.app (hole₁.mkc hole₁ hole₂)) := by
        cases hrt with
        | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h => exact (hn_hole ⟨_, h⟩).elim
      cases heq
  | sndc =>
    expose_names
    cases e_h with
    | pure hn => exact (hn .coup).elim
    | coup =>
      expose_names
      dcc_simp at hrt
      have heq : hole₂ = (g.app (hole₁.mkc hole₁ hole₂)) := by
        cases hrt with
        | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h => exact (hn_hole ⟨_, h⟩).elim
      cases heq
  | curr₁ =>
    expose_names
    dcc_simp at hrt
    have heq : (g.app hole) = ((mk (α.curr β x) hn_1).to_eta.raw.app hole) := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    rw [heq] at hrt
    exact (hrt.size_absurd (h_size_eq := by dcc_simp)).elim
  | curr₁' =>
    expose_names
    dcc_simp at hrt
    have heq : (g.app hole) = ((mk (α.curr' β x) hn_1).to_eta.raw.app hole) := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    rw [heq] at hrt
    exact (hrt.size_absurd (by dcc_simp)).elim
  | curr₂ =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? (x.expr_to_eta ⟦β.expr_to_eta⟧(y.expr_to_eta, hole))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | curr₂' =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? (x.expr_to_eta &(⟦β.expr_to_eta⟧(y.expr_to_eta, hole)))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | map =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? !((f.expr_to_eta hole))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_map.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | fmap =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? &((f.expr_to_eta hole))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | pair =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? ⟦β.expr_to_eta⟧((M.expr_to_eta hole), ((N.expr_to_eta hole) (M.expr_to_eta hole)))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | eval =>
    expose_names
    dcc_simp at hrt
    cases e_h with
    | pure hn => exact (hn .coup).elim
    | coup =>
      expose_names
      have heq : (DCC? (x.expr_to_eta hole₁ hole₂)) = g.app (hole₁.mkc hole₁ hole₂) := by
        cases hrt with
        | congrFun h =>
          exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h => exact (hn_hole ⟨_, h⟩).elim
      cases heq
  | quot =>
    expose_names
    dcc_simp at hrt
    have hn_mem := to_eta_no_hole (e := x)
    generalize heq_x : x.expr_to_eta = x'
    rw [heq_x] at hrt
    have heq : x' = g.app hole := by
      cases hrt with
      | quot => rfl
      | congrFun h => exact (hn_1.to_eta ⟨_, heq_x.symm ▸ h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    rw [heq_x] at hn_mem
    have h_mem : (g.app hole).contains_hole := by
      have ha := e_h.contains_hole
      grind
    grind
  | comp' | comp₂ | comp =>
    expose_names
    have heq : (f.expr_to_eta.app (g_1.expr_to_eta.app hole)) = g.app hole := by
      cases hrt with
      | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | pi =>
    expose_names
    have heq : ((mk (f_α.pi f_β) hn_1).to_eta.raw.app hole) = g.app hole := by
      cases hrt with
      | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    exact hrt.size_absurd.elim

def Domain.app_hole_preserve_dom
  {f     : @NormExpr τ_c RedAff}
  (h_dom : Domain f α) (e_h : Hole α.to_eta level ⟨hole, hn_hole⟩)
  (hrt   : RedAff (DCC? (f.to_eta.raw hole)) (DCC? (g hole)))
  (hn    : IsNorm RedAff g) : Domain ⟨g, hn⟩ α.to_eta := by
  have h_dom₀ := h_dom.to_eta
  cases h_dom with
  | refl₁ | eql₁ =>
    dcc_simp at e_h
    cases e_h with
    | pure hn => exact (hn .bang).elim
    | bang =>
      dcc_simp at hrt
      have h := hrt.elim_norm (fun ⟨_, h⟩ => match h with
        | .congrFun h => by
          have h' := RedAff.reflect_eta h to_eta_no_hole
          dcc_simp at h'
          expose_names
          exact hn_1 ⟨_, h'⟩
        | .congrArg h => hn_hole ⟨_, h⟩)
      cases h
  | id =>
    dcc_simp at hrt
    expose_names
    have heq' : α.expr_to_eta.id = g := by
      cases hrt with
      | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    exact (heq' ▸ hrt).size_absurd.elim
  | eql₂ =>
    cases e_h with
    | pure hn => exact (hn .bang).elim
    | bang =>
      expose_names
      dcc_simp at hrt
      have heq : (g.app hole.box) = hole.eq hole := by
        cases hrt with
        | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h =>
          exact (hn_hole ⟨_, h⟩).elim
      cases heq
  | refl₂ =>
    cases e_h with
    | pure hn => exact (hn .bang).elim
    | bang =>
      expose_names
      have heq : (g.app hole.box) = ((mk (f_α.refl.app env.box) hn_1).to_eta.raw.app hole.box) := by
        cases hrt with
        | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h =>
          exact (hn_hole ⟨_, h⟩).elim
      exact (heq ▸ hrt).size_absurd.elim
  | unmap =>
    expose_names
    cases e_h with
    | pure hn => exact (hn .bang).elim
    | bang =>
      expose_names
      dcc_simp at hrt
      have heq : (g.app hole.box) = (expr_to_eta f).app hole := by
        match hrt with
        | .congrFun h => exact (hn_map.to_eta ⟨_, h⟩).elim
        | .congrArg (.box₀ h) => exact (hn_hole_1 ⟨_, h⟩).elim
      cases heq
  | fstc =>
    expose_names
    cases e_h with
    | pure hn => exact (hn .coup).elim
    | coup =>
      expose_names
      dcc_simp at hrt
      have heq : hole₁ = (g.app (hole₁.mkc hole₁ hole₂)) := by
        cases hrt with
        | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h => exact (hn_hole ⟨_, h⟩).elim
      cases heq
  | sndc =>
    expose_names
    cases e_h with
    | pure hn => exact (hn .coup).elim
    | coup =>
      expose_names
      dcc_simp at hrt
      have heq : hole₂ = (g.app (hole₁.mkc hole₁ hole₂)) := by
        cases hrt with
        | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h => exact (hn_hole ⟨_, h⟩).elim
      cases heq
  | curr₁ =>
    expose_names
    dcc_simp at hrt
    have heq : (g.app hole) = ((mk (α.curr β x) hn_1).to_eta.raw.app hole) := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    rw [heq] at hrt
    exact (hrt.size_absurd (h_size_eq := by dcc_simp)).elim
  | curr₁' =>
    expose_names
    dcc_simp at hrt
    have heq : (g.app hole) = ((mk (α.curr' β x) hn_1).to_eta.raw.app hole) := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    rw [heq] at hrt
    exact (hrt.size_absurd (by dcc_simp)).elim
  | curr₂ =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? (x.expr_to_eta ⟦β.expr_to_eta⟧(y.expr_to_eta, hole))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | curr₂' =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? (x.expr_to_eta &(⟦β.expr_to_eta⟧(y.expr_to_eta, hole)))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | map =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? !((f.expr_to_eta hole))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_map.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | fmap =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? &((f.expr_to_eta hole))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | pair =>
    expose_names
    dcc_simp at hrt
    have heq : (DCC? ⟦β.expr_to_eta⟧((M.expr_to_eta hole), ((N.expr_to_eta hole) (M.expr_to_eta hole)))) = g.app hole := by
      cases hrt with
      | congrFun h =>
        exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | eval =>
    expose_names
    dcc_simp at hrt
    cases e_h with
    | pure hn => exact (hn .coup).elim
    | coup =>
      expose_names
      have heq : (DCC? (x.expr_to_eta hole₁ hole₂)) = g.app (hole₁.mkc hole₁ hole₂) := by
        cases hrt with
        | congrFun h =>
          exact (hn_1.to_eta ⟨_, h⟩).elim
        | congrArg h => exact (hn_hole ⟨_, h⟩).elim
      cases heq
  | quot =>
    expose_names
    dcc_simp at hrt
    have hn_mem := to_eta_no_hole (e := x)
    generalize heq_x : x.expr_to_eta = x'
    rw [heq_x] at hrt
    have heq : x' = g.app hole := by
      cases hrt with
      | quot => rfl
      | congrFun h => exact (hn_1.to_eta ⟨_, heq_x.symm ▸ h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    rw [heq_x] at hn_mem
    have h_mem : (g.app hole).contains_hole := by
      have ha := e_h.contains_hole
      grind
    grind
  | comp' | comp₂ | comp =>
    expose_names
    have heq : (f.expr_to_eta.app (g_1.expr_to_eta.app hole)) = g.app hole := by
      cases hrt with
      | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    cases heq
  | pi =>
    expose_names
    have heq : ((mk (f_α.pi f_β) hn_1).to_eta.raw.app hole) = g.app hole := by
      cases hrt with
      | congrFun h => exact (hn_1.to_eta ⟨_, h⟩).elim
      | congrArg h => exact (hn_hole ⟨_, h⟩).elim
    exact hrt.size_absurd.elim

end NormExpr
