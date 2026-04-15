import Dcc.CC.Ast
import Dcc.CC.Step2
import Dcc.CC.Judge

namespace Expr

def Reduces.reduce_self (h : Reduces τ τ') : Reduces τ τ'.reduce :=
  match h with
  | ⟨h_red, h_norm⟩ =>
    reduce_reduces (by
      rw [← h_red.complete h_norm]
      exact _root_.Expr.reduce_self)

namespace IsArrow

def reduce (h : IsArrow τ α β m n) : Reduces τ (DCC (Π(m, n) α.reduce `(Sort n, Σ(Sort m, Id(Sort m)), β))) :=
  match h with
  | ⟨h_red, h_norm⟩ =>
    have h := h_norm.congrFun.congrArg.complete_reduce
    ⟨.trans h_red (RedAffReflTrans.congrFun (.congrArg (reduce_sound rfl))), h.symm ▸ h_norm⟩

end IsArrow

theorem reduce_curr : reduce (DCC (Λ(α, x) y z)) = (DCC (x ⟦α, Id(α)⟧(y, z))).reduce := by
  conv =>
    left
    unfold reduce
    simp [step?]

theorem reduce_congr : reduce (DCC (f x)) = reduce (f.reduce.app x.reduce) :=
  have h : RedAffReflTrans (DCC (f x)) (f.reduce.app x.reduce).reduce :=
    Relation.ReflTransGen.trans (.trans
      (RedAffReflTrans.congrFun (reduce_sound rfl))
      (RedAffReflTrans.congrArg (reduce_sound rfl)))
      (reduce_sound rfl)
  h.complete (reduce_norm rfl)

theorem reduce_congrFun : reduce (DCC (f x)) = reduce (f.reduce.app x) :=
  have h : RedAffReflTrans (DCC (f x)) (DCC (f.reduce x)).reduce :=
    .trans (RedAffReflTrans.congrFun (reduce_sound rfl))
      (reduce_sound rfl)
  h.complete (reduce_norm rfl)

theorem reduce_congrArg : reduce (DCC (f x)) = reduce (f.app x.reduce) :=
  have h : RedAffReflTrans (DCC (f x)) (DCC (f x.reduce)).reduce :=
    .trans (RedAffReflTrans.congrArg (reduce_sound rfl))
      (reduce_sound rfl)
  h.complete (reduce_norm rfl)

theorem reduce_curr_congr : reduce (DCC (Λ(α, x) y z)) = (DCC (x.reduce ⟦α, Id(α)⟧(y, z))).reduce :=
  have h : RedAffReflTrans _ _ :=
    Relation.ReflTransGen.trans
      (.trans
        (.single (RedAff.curr (α := α) (x := x) (y := y) (z := z)))
        (RedAffReflTrans.congrFun (reduce_sound rfl))) (reduce_sound rfl)
  have h_norm : ((x.reduce.app (((α.mk α.id).app y).app z)).reduce).IsNormAff := reduce_norm rfl
  h.complete h_norm

namespace JudgeConv

def invert_app : JudgeConv (DCC (f x)) t → (α β : Expr) × (m n : Level)
  × JudgeConv x α
  × JudgeConv f (DCC (Π(m, n) α β))
  × (Reduces (DCC (β ⟦Sort m, Id(Sort m)⟧(α, x))) t) := fun ⟨h_t, h_red⟩ =>
  match h_t with
  | .app (α := α) (β := β) (m := m) (n := n) h_t_f h_red_pi h_t_x h_red_α =>
    ⟨α, β, m, n, ⟨h_t_x, h_red_α⟩, ⟨h_t_f, h_red_pi⟩, h_red⟩

def preservation_flip : JudgeConv (DCC (Flip(x) y z)) t → JudgeConv (DCC (x z y)) t :=
  fun h@⟨h_t, h_red⟩ => by
  cases h_t with
  | app h_t_xy t_xy_red h_t_z t_z_red =>
    cases h_t_xy with
    | app h_t_flip_x t_flip_x_red h_t_y red_t_y =>
      cases h_t_flip_x with
      | flip h_t_x arrow₁_t_x arrow₂_t_x =>
        cases reduce_arrow t_flip_x_red.complete
        have h := reduce_congr_quot ▸ t_xy_red.complete
        rename_i α₁ _ _ _ _ _ _ α _ _ _ _ _
        have heq : α.reduce = α₁ := by
          simp_all
          cases h
          rfl
        simp_all
        cases h
        have h := arrow₂_t_x.reduce
        refine ⟨.app (.app h_t_x arrow₁_t_x.reduce h_t_z (by rw [heq]; exact t_z_red)) (by
          rw [heq]
          apply reduce_reduces
          rw [reduce_congr_quot]
          exact h.complete) h_t_y red_t_y, reduce_reduces ?_⟩
        rw [reduce_congr_quot]
        exact reduce_congr_quot ▸ h_red.complete

def preservation_comp' : JudgeConv (DCC ((f ∘' g) x)) t
  → JudgeConv (DCC (f (g x))) t := fun h@⟨h_t, h_red⟩ =>
  let ⟨α, β, m, n, ⟨h_t_x, h_red_t_x⟩, ⟨h_t_f, h_red_f⟩, h_red⟩ := h.invert_app
  match h_t_f with
  | .comp' h_t_g ⟨h_red_t_g, h_norm_arr⟩ h_t_f h_red_t_f => by
    have h := reduce_congr_pi ▸ h_red_f.complete
    conv at h =>
      left
      right
      simp [reduce]
      rfl
    cases h
    have h := h_red.complete
    rw [RedAff.reduce_same .comp', reduce_congrArg, RedAff.reduce_same .comp'] at h
    conv at h =>
      left
      right
      right
      rw [reduce_congrArg, RedAff.reduce_same .snd']
      rfl
    rw [RedAff.reduce_same .curr'] at h
    cases h
    have h := h_red_t_g.complete h_norm_arr
    have h₂ := (reduce_congr_arrow rfl) ▸ h ▸ reduce_self ▸ h_red_t_g.complete h_norm_arr
    unfold arrow at h₂
    have h_red_t_f' := h_red_t_f.complete
    have h_red_t_f'₂ := reduce_congr_pi ▸ h_red_t_f' ▸ reduce_self ▸ h_red_t_f.complete
    refine ⟨.app h_t_f h_red_t_f (.app h_t_g (reduce_reduces h) h_t_x (reduce_reduces ?_)) (reduce_reduces ?_), reduce_reduces ?_⟩
    · rw [h_red_t_x.complete]
      simp_all
    · rw [RedAff.reduce_same .quot]
      have h := h_norm_arr.congrArg
      simp_all
    · conv =>
        left
        rw [reduce_congrArg]
        right
        right
        rw [reduce_congrArg]
        right
        right
        rw [reduce_congrArg]
        rfl
      symm
      trans
      rw [reduce_congrArg]
      rfl

end JudgeConv

end Expr
