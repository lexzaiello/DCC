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
  | pi   : Expr.TySize α n → Expr.TySize (SK Π α, β) n
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
  | pi        : Expr.RedTy (SK (α x)) α'
    -- ^ this is fine since all argument binders should have at least one I ready to fire
    → Expr.RedTy (SK ((Π α, β) x)) (SK (Π α', (β x)))

theorem Expr.all_size : ∃ n, Expr.TySize e n := by
  induction e
  · exact ⟨0, .hole⟩
  · rename_i c
    cases c
    · exact ⟨1, .next⟩
    · exact ⟨1, .read⟩
    · exact ⟨1, .comp⟩
    · exact ⟨1, .flip⟩
  case Pi α β ih₁ ih₂ =>
    have ⟨n, h⟩ := ih₁
    exact ⟨n, .pi h⟩
  · exact ⟨0, .srt⟩
  · exact ⟨0, .comb⟩
  case app f x ih₁ ih₂ =>
    have ⟨n, hn⟩ := ih₁
    have ⟨m, hm⟩ := ih₂
    exact ⟨n + m, .app hn hm⟩

theorem Expr.TySize.unique (h₁ : Expr.TySize e n) (h₂ : e.TySize m) : m = n := by
  induction h₁ generalizing m
  repeat (cases h₂; rfl)
  case pi α n β _ ih =>
    cases h₂
    rename_i hsizeα
    exact ih hsizeα
  repeat (cases h₂; rfl)
  case app f n x m _ _ ih₁ ih₂ =>
    cases h₂
    rename_i hnf hnx
    have ha := ih₁ hnf
    have hb := ih₂ hnx
    grind only

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
  case pi α x α' β hr ih =>
    cases h_size
    · rename_i n m hsizeα hsizex
      cases hsizeα
      rename_i hsizeα
      have h := ih (.app (by assumption) (by assumption))
      have ⟨n', h₁, h₂⟩ := h
      exact ⟨_, .pi (by assumption), by grind only⟩

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

def Expr.ty_size : Expr → ℕ
  | (SK K*) => 1
  | (SK B) => 1
  | (SK C) => 1
  | (SK I) => 1
  | (SK Π α, _β) => α.ty_size
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
  · have h' := Expr.TySize.sound h
    rw [← h] at h'
    apply TySize.pi
    exact h'
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
  case pi α n β hα ih =>
    exact ih.symm ▸ rfl
  repeat rfl
  case app f n x m hf hx ih₁ ih₂ =>
    rw [← ih₁, ← ih₂]
    rfl

theorem Expr.RedTy.decreasing' (h_red : Expr.RedTy e e') : e'.ty_size < e.ty_size := by
  let h_size := e.ty_size
  have ⟨m, h, hp⟩ := Expr.RedTy.decreasing h_red (Expr.TySize.sound (e := e) (n := h_size) rfl)
  have h := h.complete
  exact h.symm ▸ hp

instance : WellFoundedRelation Expr := ⟨fun x y => x.ty_size < y.ty_size, (measure (fun e => Expr.ty_size e)).wf⟩

def Expr.RedTyReflTrans := Relation.ReflTransGen Expr.RedTy

def Expr.IsNorm (e : Expr) : Prop := ∀ e', ¬ Expr.RedTy e e'

def Expr.step? (e : Expr) : Option Expr :=
  match e with
  | (SK (K* A _b)) => .some A
  | (SK (B f g x)) => .some (SK (f (g x)))
  | (SK (C x y z)) => .some (SK (x z y))
  | (SK (I x)) => .some x
  | (SK ((Π α, β) x)) => match (SK (α x)).step? with
    | .some α' => .some (SK (Π α', (β x)))
    | .none => .none
  | (SK (f x)) => match f.step?, x.step? with
    | .some f', .some x' =>
      .some (SK (f' x'))
    | _a, _b => .none
  | _e => .none

def Expr.step?_sound : Expr.step? e = .some e' → Expr.RedTy e e' := by
  intro h
  unfold step? at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact .next
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact .comp
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact .flip
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact .read
  · split at h
    · rename_i heq
      simp_all only [Option.some.injEq]
      rw [← h]
      exact .pi (Expr.step?_sound heq)
    contradiction
  · split at h
    · simp only [Option.some.injEq] at h
      rename_i heq₁ heq₂
      rw [← h]
      exact .app (Expr.step?_sound heq₁) (Expr.step?_sound heq₂)
    · contradiction
  · contradiction

def Expr.reduce (h_size : Expr.TySize e n) : ((e' : Expr) × (PLift (e.RedTyTrans e'))) := by
  
  sorry
