import Dcc.CC.Ast
import Dcc.CC.Step2
import Dcc.CC.Judge
import Mathlib.Tactic

namespace Expr

namespace Judge

/-
⊢ ((Expr.sort m).quot ((Expr.sort m).sigma (Expr.sort m).id) α).Judge
    (arrow ((Expr.sort m).sigma (Expr.sort m).id) (Expr.sort m) (Nat.succ m) (Nat.succ m))
-/

syntax "reduce" ident                    : tactic
syntax "convr" term                      : tactic
syntax "convl" term                      : tactic
syntax "cases_conv" "[" term,* "]"       : tactic
syntax "cases_conv'" "[" term,* "]"      : tactic
syntax "cases_red"  "[" term,* "]"       : tactic
syntax "reduce_here"                     : term

macro_rules
  | `(term| reduce_here) => `((Expr.reduce _).snd.down)
  | `(tactic| cases_red [$h:term]) =>
    `(tactic| (
      have ha := ($h).complete (by assumption)
      simp [reduce, step?] at ha
      (try simp_all)
    ))
  | `(tactic| cases_red [$h:term, $xs:term,*]) =>
    `(tactic| cases_red [$h:term]; cases_red [$xs:term,*])
  | `(tactic| cases_conv [$h:term]) =>
    `(tactic|(
      obtain ⟨_, a, b, h⟩ : (∃ C, RedAffReflTrans _ C ∧ RedAffReflTrans _ C ∧ C.IsNormAff) := $h
      cases_red [a, b])
    )
  | `(tactic| cases_conv' [$h:term]) =>
    `(tactic|(
      obtain ⟨a, b, h⟩ : (RedAffReflTrans _ _ ∧ RedAffReflTrans _ _ ∧ IsNormAff _) := $h
      cases_red [a, b])
    )
  | `(tactic| cases_conv [$x:term, $xs:term,*]) =>
    `(tactic| cases_conv [$x:term]; cases_conv [$xs:term,*])
  | `(tactic| cases_conv' [$x:term, $xs:term,*]) =>
    `(tactic| cases_conv' [$x:term]; cases_conv' [$xs:term,*])
  | `(tactic| convr $e:term) =>
    `(tactic|
      exact ⟨_, (reduce _).snd.down, by
        simp [reduce, step?]
        split
        exact .trans (.single (($e).step?.get (by simp_all)).snd.down) (by simp_all; exact (reduce _).snd.down)
        exact .refl, reduce_norm rfl⟩)

macro_rules
  | `(tactic| convl $e:term) =>
    `(tactic|
      exact ⟨_, by
        simp [reduce, step?]
        split
        exact .trans (.single (($e).step?.get (by simp_all)).snd.down) (by simp_all; exact (reduce _).snd.down)
        exact .refl, (reduce _).snd.down, reduce_norm rfl⟩)

theorem id_well_typed (h_t_α : Judge α (DCC (Sort m))) (h_t_x : Judge x α) : Judge (DCC (Id(α) x)) α :=
  .conv (.app (.id h_t_α) h_t_x) (by convr α)

theorem app_invert {e t f x : Expr} (h_t : Judge e t) (heq : e = (DCC (f x))) : ∃ m n α β,
  Judge f (DCC (Π(m, n) α β))
    ∧ Judge x α
    ∧ (∃ C, RedAffReflTrans (DCC (β ⟦Id(Sort m)⟧(α, x))) C ∧ RedAffReflTrans t C ∧ IsNormAff C) := by
  induction heq₂ : h_t with
  | app h_t_f h_t_x _ _ =>
    simp at heq
    have ⟨h₁, h₂⟩ := heq
    rw [← h₁, ← h₂]
    exact ⟨_, _, _, _, h_t_f, h_t_x, _, (reduce _).snd.down, (reduce _).snd.down, reduce_norm rfl⟩
  | conv _h_t_x h_conv ih =>
    simp_all
    have ⟨C, h₃, h₄, h_norm⟩ := h_conv
    have ⟨m, n, α, β, h_t_f, h_t_x, D, h₁, h₂, h_norm⟩ := ih (by rw [← heq]; assumption)
    have ⟨D, h₅, h₆⟩ := h₃.conf h₂
    refine ⟨m, n, α, β, h_t_f, h_t_x, ?_⟩
    exact ⟨_, .trans (.trans h₁ h₆) D.reduce.snd.down, .trans (.trans h₄ h₅) D.reduce.snd.down, reduce_norm rfl⟩
  | _ => contradiction

--theorem preserves_arrow (h_t_e : Judge 

theorem preserves_id (h_t_α : Judge α (DCC (Sort m))) (h_t : Judge (DCC (Id(α) x)) α) : Judge x α := by
  have ⟨m, n, α₁, β, h_t_f, h₁, h_t_x, h_conv⟩ := app_invert h_t rfl
  cases h_t_f with
  | id => exact h₁
  | conv =>
    rename_i h_conv
    cases_conv [h_conv]
    rename_i h _ _ _
    cases_conv' [h_conv]
    
    sorry

/-theorem preserves_id (h_t_α : Judge α (DCC (Sort m))) (h_t : Judge (DCC (Id(α) x)) α) : Judge x α := by
  cases h_t with
  | app h₁ h₂ =>
    cases h_t_α with
    | conv _h h_red =>
      cases _h with
      | app h_t_β₁ h_t_id =>
        cases h_t_β₁ with
        | id =>
          cases_conv [h_red]
          rename_i h _ _ _ _
          cases h_t_id with
          | coup h_t_id h_t_α₁ h_t_x' =>
            rename_i ha
            simp [coup.type, step?] at ha
            cases h_t_id with
            | id h_t_sort =>
              cases h_t_sort with
              | sort =>
                rename_i han _
                cases han
                contradiction
              | conv =>
                rename_i han _ _ _ _
                cases han
                contradiction
            | conv =>
              rename_i han _ _ _ _ _ _ _
              cases han
              contradiction
          | conv =>
            rename_i han _ _ _
            cases han
            rename_i h h_t_coup _ _ _ _
            
            sorry-/

/-theorem preserves (h_t : Judge x T) (h_red : Red x x') : Judge x' T := by
  induction h_t generalizing x' with
  | sort | quot | app_e | curr | snd | fst | pair | comp | id =>
    cases h_red
  | app h_t_f h_t_x ih₁ ih₂ =>
    cases h_red with
    | id =>
      
      have ⟨m, n, α, β, h_t_f, h_t_x, C, h₁, h₂⟩ := (Judge.app h_t_f h_t_x).app_invert rfl
      have ⟨hc₁, h_norm⟩ := h₂
      cases h_t_f
      · cases h_t_f
        rename_i α _ _ _ _
        · exact Judge.conv (by assumption) (by convl α)
        · have h := h₁.complete h_norm
          simp [reduce, step?] at h
          rename_i _α _ _ _ _
          have hb := hc₁.complete h_norm
          refine Judge.conv (by assumption) ?_
          refine ⟨C, ?_, ?_, h_norm⟩
          · rw [← h]
            split
            · simp_all
              rename_i h _
              exact .trans (.single h) (reduce _).snd.down
            · simp_all; exact .refl
          · rw [← hb]
            exact (Expr.reduce _).snd.down
      rename_i h _
      cases h
      · rename_i h _
        cases h
        
        sorry
  | coup => sorry
  | conv => sorry-/

end Judge

end Expr
