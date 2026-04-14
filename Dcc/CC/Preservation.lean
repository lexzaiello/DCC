import Dcc.CC.Ast
import Dcc.CC.Step2
import Dcc.CC.Judge

namespace Expr

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
