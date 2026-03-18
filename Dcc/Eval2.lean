import Dcc.Ast2
import Init.Data.Option.Lemmas
import Mathlib.Logic.Relation
import Mathlib.Tactic

-- Decreasing measure
-- function arity decreases with each argument
inductive Expr.TySize : Expr → ℕ → Prop
  | next : Expr.TySize (SK K*) 1
  | comp : Expr.TySize (SK B) 1
  | flip : Expr.TySize (SK C) 1
  | read : Expr.TySize (SK I) 1
  | pi   : Expr.TySize (SK Π α, β) 0
  | comb : Expr.TySize (.comb c) 0
  | hole : Expr.TySize (SK __ ∶ t) 0
  | srt  : Expr.TySize (SK Sort m) 0
  | app  : Expr.TySize f n
    → Expr.TySize x m
    → Expr.TySize (SK (f x)) (n + m)

-- single-ish step reduction
-- no refl constructor, since this is meant to fire at the top level with Π.
-- Π argument types should always reduce for the argument.
inductive Expr.RedTy : Expr → Expr → Prop
  | next      : RedTy (SK (K* A b)) A
  | comp      : RedTy (SK (B f g x)) (SK (f (g x)))
  | flip      : RedTy (SK (C x y z)) (SK (x z y))
  | read      : RedTy (SK (I x)) x
  | app       : Expr.RedTy f f'
    → Expr.RedTy x x'
    → Expr.RedTy (SK (f x)) (SK (f' x'))

theorem Expr.all_size : ∃ n, Expr.TySize e n := by
  induction e
  · exact ⟨0, .hole⟩
  · rename_i c
    cases c
    · exact ⟨1, .next⟩
    · exact ⟨1, .read⟩
    · exact ⟨1, .comp⟩
    · exact ⟨1, .flip⟩
  · exact ⟨0, .pi⟩
  · exact ⟨0, .srt⟩
  · exact ⟨0, .comb⟩
  case app f x ih₁ ih₂ =>
    have ⟨n, hn⟩ := ih₁
    have ⟨m, hm⟩ := ih₂
    exact ⟨n + m, .app hn hm⟩

theorem Expr.TySize.unique (h₁ : Expr.TySize e n) (h₂ : e.TySize m) : m = n := by
  induction h₁ generalizing m
  repeat (cases h₂; rfl)
  case app f n x m _ _ ih₁ ih₂ =>
    cases h₂
    rename_i hnf hnx
    have ha := ih₁ hnf
    have hb := ih₂ hnx
    grind only


def Expr.ty_size : Expr → ℕ
  | (SK K*) => 1
  | (SK B) => 1
  | (SK C) => 1
  | (SK I) => 1
  | (SK Π _α, _β) => 0
  | .comb _c => 0
  | SK __ ∶ _t => 0
  | SK Sort _m => 0
  | SK (f x) =>
    let n := f.ty_size
    let m := x.ty_size
    (n + m)

theorem Expr.TySize.sound : Expr.ty_size e = n → Expr.TySize e n := by
  intro h
  unfold Expr.ty_size at h
  rw [← h]
  split at h
  · exact .next
  · exact .comp
  · exact .flip
  · exact .read
  · exact .pi
  · exact .comb
  · exact .hole
  · exact .srt
  simp at h
  apply Expr.TySize.app
  repeat (apply Expr.TySize.sound; rfl)

theorem Expr.TySize.complete : Expr.TySize e n → Expr.ty_size e = n := by
  intro h
  induction h
  repeat rfl
  case app f n x m hf hx ih₁ ih₂ =>
    rw [← ih₁, ← ih₂]
    rfl

theorem Expr.RedTy.decreasing (h_red : Expr.RedTy e e') (h_size : e.TySize n) : ∃ m, e'.TySize m ∧ m < n := by
  induction h_red generalizing n
  · cases h_size
    rename_i h _
    cases h
    rename_i h _
    cases h
    exact ⟨_, (by assumption), by grind only⟩
  · cases h_size
    rename_i h _
    cases h
    rename_i h _
    cases h
    rename_i h _
    cases h
    exact ⟨_, .app (by assumption) (.app (by assumption) (by assumption)), by grind only⟩
  · cases h_size
    rename_i h _
    cases h
    rename_i h _
    cases h
    rename_i h _
    cases h
    exact ⟨_, .app (.app (by assumption) (by assumption)) (by assumption), by grind only⟩
  · cases h_size
    rename_i h _
    cases h
    exact ⟨_, by assumption, by grind only⟩
  case app f f' x hrf ih =>
    cases h_size
    have ha := hrf (by assumption)
    have hb := ih (by assumption)
    have ⟨f', h₁, h₂⟩ := ha
    have ⟨f'', h₃, h₄⟩ := hb
    exact ⟨_, .app (by assumption) (by assumption), by grind only⟩

def Expr.RedTyTrans := Relation.TransGen Expr.RedTy

-- retry with hyp n₂ instead if hard
theorem Expr.RedTyTrans.decreasing (h_red : Expr.RedTyTrans a b) (hn : a.TySize n) : ∃ m, b.TySize m ∧ m < n := by
  induction h_red
  · rename_i hr
    exact hr.decreasing hn
  · rename_i b c htrans hr ih
    have ⟨m, hbm₁, hbm₂⟩ := ih
    have ⟨mc, hcm₁, hcm₂⟩ := hr.decreasing hbm₁
    exact ⟨mc, hcm₁, by grind only⟩

theorem Expr.RedTy.decreasing' (h_red : Expr.RedTy e e') : e'.ty_size < e.ty_size := by
  let h_size := e.ty_size
  have ⟨m, h, hp⟩ := Expr.RedTy.decreasing h_red (Expr.TySize.sound (e := e) (n := h_size) rfl)
  have h := h.complete
  exact h.symm ▸ hp

instance : WellFoundedRelation Expr := ⟨fun x y => x.ty_size < y.ty_size, (measure (fun e => Expr.ty_size e)).wf⟩

instance Expr.instSizeOf : SizeOf Expr := ⟨Expr.ty_size⟩

def Expr.RedTyReflTrans := Relation.ReflTransGen Expr.RedTy

def Expr.IsNorm (e : Expr) : Prop := ∀ e', ¬ Expr.RedTy e e'

def Expr.step? (e : Expr) : Option Expr :=
  match e with
  | (SK (K* A _b)) => .some A
  | (SK (B f g x)) => .some (SK (f (g x)))
  | (SK (C x y z)) => .some (SK (x z y))
  | (SK (I x)) => .some x
  | (SK (f x)) => match f.step?, x.step? with
    | .some f', .some x' =>
      .some (SK (f' x'))
    | _a, _b => .none
  | _e => .none

def Expr.step?_sound : Expr.step? e = .some e' → Expr.RedTy e e' := by
  induction e generalizing e'
  intro h
  · contradiction
  · rename_i c
    intro h
    unfold Expr.step? at h
    contradiction
  · rename_i α β ih₁ ih₂
    intro h
    unfold Expr.step? at h
    contradiction
  · intro h
    unfold Expr.step? at h
    contradiction
  · intro h
    unfold Expr.step? at h
    contradiction
  · rename_i f x ih₁ ih₂
    intro h
    unfold Expr.step? at h
    split at h
    · rename_i heq
      simp_all only [app.injEq, Option.some.injEq, and_self]
      exact .next
    · rename_i heq
      simp_all only [app.injEq, Option.some.injEq]
      rw [← h]
      exact .comp
    · rename_i heq
      simp_all only [app.injEq, Option.some.injEq]
      rw [← h]
      exact .flip
    · rename_i heq
      simp_all only [app.injEq, Option.some.injEq]
      rw [← h]
      exact .read
    · rename_i heq
      split at h
      · simp_all only [imp_false, app.injEq, Option.some.injEq, forall_eq']
        rw [← h]
        apply RedTy.app
        repeat assumption
      · contradiction
    contradiction

def Expr.reduce (e : Expr) : Expr :=
  match heq : step? e with
  | .some e' =>
    have _h_size : e'.ty_size < e.ty_size := (Expr.step?_sound heq).decreasing'
    e'.reduce
  | .none => e
termination_by e

theorem reduce_sound : Expr.reduce e = e' → Expr.RedTyReflTrans e e' := by
  intro h
  unfold Expr.reduce at h
  split at h
  · rename_i e'' heq
    have _h_size : e''.ty_size < e.ty_size := (Expr.step?_sound heq).decreasing'
    exact .trans (.single (Expr.step?_sound heq)) (reduce_sound h)
  · rename_i heq
    exact h.symm ▸ .refl

theorem app_step_size_decrease : Expr.RedTy f f' → Expr.RedTy x x' → (SK (f' x')).ty_size < (SK (f x)).ty_size := by
  intro ha hb
  have h : f'.ty_size < f.ty_size := ha.decreasing'
  have h : x'.ty_size < x.ty_size := hb.decreasing'
  induction ha generalizing x'
  · unfold Expr.ty_size; grind
  · unfold Expr.ty_size; grind
  · unfold Expr.ty_size; grind
  · unfold Expr.ty_size; grind
  case app f₂ f₃ x₂ x₃ hf hx ih₁ ih₂ h' =>
    have h := hb.decreasing'
    have ha := hf.decreasing'
    have hc := hx.decreasing'
    have haa := ih₁ (by assumption) (by assumption) (by assumption)
    have hbb := ih₂ (by assumption) (by assumption) (by assumption)
    unfold Expr.ty_size
    simp
    grind

theorem Expr.step?_complete : Expr.RedTy a b → Expr.step? a = .some b := by
  intro h
  induction h
  repeat (unfold Expr.step?; rfl)
  case app f f' x x' hf hx ih₁ ih₂ =>
    
    sorry

theorem reduce_same : Expr.RedTy a b → Expr.RedTy a c → Expr.reduce b = Expr.reduce c := by
  intro ha hb
  unfold Expr.reduce
  split
  · rename_i d heq
    simp_all
    have hc := Expr.step?_sound heq
    have hsize₁ := ha.decreasing'
    have hsize₂ := hb.decreasing'
    have hsize₃ := hc.decreasing'
    
    exact reduce_same hc (by sorry)
    sorry

theorem reduce_complete : Expr.RedTyTrans e e' → Expr.reduce e = e' := by
  intro h
  unfold Expr.reduce
  split
  · rename_i e₂ heq
    induction h
    · rename_i e₃ h
      have h_sound := Expr.step?_sound heq
      have hsize₁ := h.decreasing'
      have hsize₂ := h_sound.decreasing'
      exact reduce_complete (by sorry)
    sorry
  sorry
