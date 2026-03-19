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
  | congrFun  : Expr.RedTy f f'
    → Expr.RedTy (SK (f x)) (SK (f' x))

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
  case congrFun f f' x hrf ih =>
    cases h_size
    have h := ih (by assumption)
    have ⟨m, hf, h₁⟩ := h
    rename_i n_x _ _
    refine ⟨m + n_x, ?_, ?_⟩
    apply TySize.app
    repeat assumption
    grind

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

theorem Expr.RedTyTrans.decreasing' (h_red : Expr.RedTyTrans e e') : e'.ty_size < e.ty_size := by
  let h_size := e.ty_size
  have ⟨m, h, hp⟩ := Expr.RedTyTrans.decreasing h_red (Expr.TySize.sound (e := e) (n := h_size) rfl)
  have h := h.complete
  exact h.symm ▸ hp

instance : WellFoundedRelation Expr := ⟨fun x y => x.ty_size < y.ty_size, (measure (fun e => Expr.ty_size e)).wf⟩

def Expr.RedTyReflTrans := Relation.ReflTransGen Expr.RedTy

def Expr.IsNorm (e : Expr) : Prop := ¬ ∃ e', RedTy e e'

def Expr.step? (e : Expr) : Option Expr :=
  match e with
  | (SK (K* A _b)) => .some A
  | (SK (B f g x)) => .some (SK (f (g x)))
  | (SK (C x y z)) => .some (SK (x z y))
  | (SK (I x)) => .some x
  | (SK (f x)) => match f.step? with
    | .some f' =>
      .some (SK (f' x))
    | _ => .none
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
      cases heq
      have h := RedTy.congrFun (x := x) (ih₁ (by assumption))
      simp_all
      contradiction
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
termination_by e.ty_size

theorem app_step_size_decrease : Expr.RedTy f f' → Expr.RedTy x x' → (SK (f' x')).ty_size < (SK (f x)).ty_size := by
  intro ha hb
  have h : f'.ty_size < f.ty_size := ha.decreasing'
  have h : x'.ty_size < x.ty_size := hb.decreasing'
  induction ha generalizing x'
  · unfold Expr.ty_size; grind
  · unfold Expr.ty_size; grind
  · unfold Expr.ty_size; grind
  · unfold Expr.ty_size; grind
  case congrFun f'' f''' x' hrf ih₁ ih₂ =>
    unfold Expr.ty_size
    simp_all only [gt_iff_lt]
    grind

theorem step?_decreasing : Expr.step? e = .some e' → e'.ty_size < e.ty_size := fun h =>
  (Expr.step?_sound h).decreasing'

def Expr.RedTy.step?_complete : Expr.RedTy e e' → Expr.step? e = .some e' := fun h => by
  induction e generalizing e'
  · cases h
  · cases h
  · cases h
  · cases h
  · cases h
  case app f x ih₁ ih₂ =>
    cases h
    repeat rfl
    · unfold Expr.step?
      have h := ih₁ (by assumption)
      split
      repeat (simp_all; cases h)
      split
      simp_all
      rename_i h
      exfalso
      exact h (by assumption) (by simp_all)
      have h := ih₁ (by assumption)
      simp_all

theorem Expr.RedTy.unique : Expr.RedTy a b → Expr.RedTy a c → b = c := by
  intro hr₁ hr₂
  have heq₁ := hr₁.step?_complete
  have heq₂ := hr₂.step?_complete
  simp_all

theorem Expr.IsNorm.reduce_rfl : Expr.IsNorm e → e.reduce = e := by
  intro h
  unfold Expr.reduce
  split
  · rename_i heq
    have h := Expr.step?_sound heq
    rename_i h_norm e''
    exfalso
    exact h_norm ⟨_, h⟩
  rfl

theorem Expr.RedTy.reduce_same : Expr.RedTy a b → reduce a = reduce b := by
  intro ha
  conv =>
    left
    unfold reduce
    rfl
  split
  · rename_i e' heq
    simp [ha.unique (Expr.step?_sound heq)]
  · have h := ha.step?_complete
    simp_all

theorem Expr.RedTyTrans.reduce_same : Expr.RedTyTrans a b → Expr.RedTyTrans a c → reduce b = reduce c := by
  intro h₁ h₂
  induction h₁ generalizing c
  · induction h₂ generalizing b
    · rename_i b₁ hr₁ b₂ hr₂
      have ha := hr₁.reduce_same
      have hb := hr₂.reduce_same
      simp_all
    · rename_i b₁ hrr₁ b₂ c htrans hb₂ ih
      rw [ih]
      exact hb₂.reduce_same
      exact b₂
  · rename_i b₁ c₁ htrans hr₂ ih
    have h := ih h₂
    rw [← h]
    have h := hr₂.reduce_same
    simp_all

theorem Expr.RedTyTrans.complete : Expr.RedTyTrans a b → Expr.reduce a = Expr.reduce b := by
  intro h
  induction h
  · exact Expr.RedTy.reduce_same (by assumption)
  · rename_i h _
    have h := h.reduce_same
    simp_all

theorem Expr.RedTyTrans.complete' : Expr.RedTyTrans a b → IsNorm b → Expr.reduce a = b := by
  intro ha hnorm
  induction ha
  · rename_i _ hr
    simp [hr.reduce_same]
    unfold Expr.reduce
    split
    · exfalso
      exact hnorm ⟨_, Expr.step?_sound (by assumption)⟩
    · rfl
  · rename_i b₂ c htrans hrb ih
    have h := hrb.step?_complete
    change Expr.RedTyTrans a b₂ at htrans
    rw [htrans.complete]
    unfold Expr.reduce
    split
    · simp_all
      unfold Expr.reduce
      split
      · simp
        exfalso
        exact hnorm ⟨_, Expr.step?_sound (by assumption)⟩
      · rfl
    simp_all

def Expr.RedTy.SN (e : Expr) : Acc (fun b a => Expr.RedTy a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing'
  exact Expr.RedTy.SN e')
termination_by e

def Expr.RedTyTrans.SN (e : Expr) : Acc (fun b a => Expr.RedTyTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing'
  exact Expr.RedTyTrans.SN e')
termination_by e.ty_size

#eval Std.format <| (SK (arg 2 I (Sort 1) (Sort 2) (Sort 3))).reduce

/-
Count the size of a Π α, β expression
by finding the size of its leaves (not nested Π. apps, for example,
or just tycombs).
-/
inductive Expr.PiSize : Expr → ℕ → Prop
  | tycomb : Expr.TySize (.tycomb c) n → Expr.PiSize (.tycomb c) n
  | comb   : Expr.PiSize (.comb c) 0
  | hole   : Expr.PiSize (SK __ ∶ t) 0
  | srt    : Expr.PiSize (SK Sort m) 0
  | app    : Expr.TySize (.app f x) n → Expr.PiSize (.app f x) n
  | pi     : Expr.PiSize α m → Expr.PiSize β n →  Expr.PiSize (SK Π α, β) (m + n)

def Expr.pi_size (e : Expr) : ℕ :=
  match e with
  | (SK Π α, β) =>
    let m := α.pi_size
    let n := β.pi_size
    (m + n)
  | e => e.ty_size

theorem Expr.PiSize.sound (h : Expr.pi_size e = n) : Expr.PiSize e n := by
  unfold Expr.pi_size at h
  rw [← h]
  split at h
  · rename_i e α β
    have size₁ := Expr.PiSize.sound (e := α) rfl
    have size₂ := Expr.PiSize.sound (e := β) rfl
    exact Expr.PiSize.pi size₁ size₂
  · rename_i _ hsize
    cases e
    · exact .hole
    · rename_i c
      cases c
      repeat (apply PiSize.tycomb; exact TySize.sound rfl)
    · rename_i e₁ α β
      exfalso
      exact hsize α β rfl
    · exact .srt
    · exact .comb
    · rename_i e' f x
      apply PiSize.app; exact TySize.sound rfl

/-
α leaves must always reduce.
-/
inductive Expr.RedPi : Expr → Expr → Prop
  | step_ty  : Expr.RedTy e e' → Expr.RedPi e e'
  | step_dom : Expr.RedPi (SK (α x)) α'
    → Expr.RedPi (SK (β x)) β'
    → Expr.RedPi (SK ((Π α, β) x)) (SK Π α', β')
  | zero_app : Expr.TySize f 0 -- this is to handle raw SK in Π. does not increase size.
    → Expr.RedPi (SK (f x)) (SK (f x))

def Expr.step_pi? (e : Expr) : Option Expr :=
  match e with
  | SK ((Π α, β) x) =>
    -- full congruence is fine, since raw combs do nothing
    -- and all arg macros expand to at least one I, which will reduce
    match (SK (α x)).step_pi?, (SK (β x)).step_pi? with
    | .some α', .some β' =>
      .some (SK (Π α', β'))
    | _, _ => .none
  | SK (f x) =>
    if _h : f.ty_size = 0 then
      .some (SK (f x))
    else
      (SK (f x)).step?
  | _ => .none


