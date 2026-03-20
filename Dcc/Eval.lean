import Dcc.Ast
import Init.Data.Option.Lemmas
import Mathlib.Logic.Relation
import Mathlib.Tactic

-- Decreasing measure
-- function arity decreases with each argument
inductive Expr.TySize : Expr → ℕ → Prop
  | next  : Expr.TySize (SK K*) 1
  | comp  : Expr.TySize (SK B) 1
  | flip  : Expr.TySize (SK C) 1
  | read  : Expr.TySize (SK I) 1
  | pi    : Expr.TySize (SK Π α, β) 0
  | comb  : Expr.TySize (.comb c) 0
  | hole  : Expr.TySize (SK __ ∶ t) 0
  | srt   : Expr.TySize (SK Sort m) 0
  | app   : Expr.TySize f n
    → Expr.TySize x m
    → Expr.TySize (SK (f x)) (n + m)

-- single-ish step reduction
-- no refl constructor, since this is meant to fire at the top level with Π.
-- congruence is only to the left (call-by-name reduction), to enable determinism,
-- and since argument types formed in a Π binder should always reduce fully
inductive Expr.RedTy : Expr → Expr → Prop
  | next      : RedTy (SK (K* A b)) A
  | comp      : RedTy (SK (B f g x)) (SK (f (g x)))
  | flip      : RedTy (SK (C x y z)) (SK (x z y))
  | read      : RedTy (SK (I x)) x
  | congrFun  : Expr.RedTy f f'
    → Expr.RedTy (SK (f x)) (SK (f' x))

-- All expressions have a size (including combinator terms)
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

-- Sizes are unique for an expression `e`
theorem Expr.TySize.unique (h₁ : Expr.TySize e n) (h₂ : e.TySize m) : m = n := by
  induction h₁ generalizing m
  repeat (cases h₂; rfl)
  case app f n x m _ _ ih₁ ih₂ =>
    cases h₂
    rename_i hnf hnx
    have ha := ih₁ hnf
    have hb := ih₂ hnx
    grind only

-- Compute the size of an expression
def Expr.ty_size : Expr → ℕ
  | (SK K*) | (SK B) | (SK C) | (SK I) => 1
  | (SK Π _α, _β) | .comb _c | SK __ ∶ _t | SK Sort _m => 0
  | SK (f x) =>
    let n := f.ty_size
    let m := x.ty_size
    (n + m)

-- ty_size corresponds to TySize
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

-- TySize corresponds to ty_size
theorem Expr.TySize.complete : Expr.TySize e n → Expr.ty_size e = n := by
  intro h
  induction h
  repeat rfl
  case app f n x m hf hx ih₁ ih₂ =>
    rw [← ih₁, ← ih₂]
    rfl

-- For every single-step reduction, there is a TySize for e' that is smaller than e's size.
theorem Expr.RedTy.decreasing (h_red : Expr.RedTy e e') (h_size : e.TySize n) : ∃ m, e'.TySize m ∧ m < n := by
  induction h_red generalizing n
  · cases h_size
    iterate 2 (rename_i h _; cases h)
    exact ⟨_, (by assumption), by grind only⟩
  · cases h_size
    iterate 3 (rename_i h _; cases h)
    exact ⟨_, .app (by assumption) (.app (by assumption) (by assumption)), by grind only⟩
  · cases h_size
    iterate 3 (rename_i h _; cases h)
    exact ⟨_, .app (.app (by assumption) (by assumption)) (by assumption), by grind only⟩
  · cases h_size
    rename_i h _; cases h
    exact ⟨_, by assumption, by grind only⟩
  case congrFun f f' x hrf ih =>
    cases h_size
    rename_i n_x _ _
    have h := ih (by assumption)
    have ⟨m, hf, h₁⟩ := h
    exact ⟨m + n_x, .app (by assumption) (by assumption), by grind⟩

-- The transitive closure of single-step reduction
def Expr.RedTyTrans := Relation.TransGen Expr.RedTy

-- Same as Expr.RedTy.decreasing, but for transitive closure
theorem Expr.RedTyTrans.decreasing (h_red : Expr.RedTyTrans a b) (hn : a.TySize n) : ∃ m, b.TySize m ∧ m < n := by
  induction h_red
  · rename_i hr
    exact hr.decreasing hn
  · rename_i b c htrans hr ih
    have ⟨m, hbm₁, hbm₂⟩ := ih
    have ⟨mc, hcm₁, hcm₂⟩ := hr.decreasing hbm₁
    exact ⟨mc, hcm₁, by grind only⟩

-- The "smaller" size of e' in single-step reduction IS its unique size.
theorem Expr.RedTy.decreasing' (h_red : Expr.RedTy e e') : e'.ty_size < e.ty_size := by
  have ⟨m, h, hp⟩ := Expr.RedTy.decreasing h_red (Expr.TySize.sound (e := e) (n := e.ty_size) rfl)
  exact h.complete.symm ▸ hp

-- Same as above, but for transitive closure
theorem Expr.RedTyTrans.decreasing' (h_red : Expr.RedTyTrans e e') : e'.ty_size < e.ty_size := by
  have ⟨m, h, hp⟩ := Expr.RedTyTrans.decreasing h_red (Expr.TySize.sound (e := e) (n := e.ty_size) rfl)
  exact h.complete.symm ▸ hp

-- This is used by Lean for `termination_by e.ty_size`.
instance : WellFoundedRelation Expr := ⟨fun x y => x.ty_size < y.ty_size, (measure (fun e => Expr.ty_size e)).wf⟩

-- Reflexive transitive closure. `reduce` function requires this to prove soundness, since beta reduction requires reflexivity for normal forms.
def Expr.RedTyReflTrans := Relation.ReflTransGen Expr.RedTy

-- Normal forms have no next single-step reduction.
def Expr.IsNorm (e : Expr) : Prop := ¬ ∃ e', RedTy e e'

-- Single-step reduction. If no reduction is possible, return .none
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

-- Every result of step? corresponds to a constructor of our single-step reduction predicate
-- This is essentially the workhorse of all other proofs.
def Expr.step?_sound : Expr.step? e = .some e' → Expr.RedTy e e' := by
  induction e generalizing e'
  intro h
  · contradiction
  iterate 4 (intro h; unfold Expr.step? at h; contradiction)
  · rename_i f x ih₁ ih₂
    intro h; unfold Expr.step? at h
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

-- Full beta-reduction. We use our decreasing measure to recurse.
-- termination_by e is also possible. It infers ty_size due to our WellfoundedRelation
-- instance.
def Expr.reduce (e : Expr) : Expr :=
  match heq : step? e with
  | .some e' =>
    -- This hypothesis allows the recursion. Easy to prove.
    have _h_size : e'.ty_size < e.ty_size := (Expr.step?_sound heq).decreasing'
    e'.reduce
  | .none => e
termination_by e.ty_size

-- Every reduction corresponds to a constructor of reflexive transitive closure of single-step reduction
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

-- Congruence implies that the size of the entire expression decreases.
theorem app_step_size_decrease : Expr.RedTy f f' → Expr.RedTy x x' → (SK (f' x')).ty_size < (SK (f x)).ty_size := by
  intro ha hb
  have h : f'.ty_size < f.ty_size := ha.decreasing'
  have h : x'.ty_size < x.ty_size := hb.decreasing'
  induction ha generalizing x'
  repeat (unfold Expr.ty_size; grind)

-- Same as RedTy.decreasing', but for our computable function
theorem step?_decreasing : Expr.step? e = .some e' → e'.ty_size < e.ty_size := fun h =>
  (Expr.step?_sound h).decreasing'

-- Completeness of our single-step reduction function
def Expr.RedTy.step?_complete : Expr.RedTy e e' → Expr.step? e = .some e' := fun h => by
  induction e generalizing e'
  iterate 5 cases h
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

-- Uniqueness of single-step reductions (determinism of single-step reductions)
theorem Expr.RedTy.unique : Expr.RedTy a b → Expr.RedTy a c → b = c := by
  intro hr₁ hr₂
  have heq₁ := hr₁.step?_complete
  have heq₂ := hr₂.step?_complete
  simp_all

-- Normal forms reduce to themselves
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

-- Single-step reduct of a reduces to the reduction of a
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

-- Church-rosser for our reduction function. Implies church-rosser for the predicate version, since we have soundness.
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

-- Completeness of full reduction function with respect to the transitive closure of single-step reduction.
-- Note that there are two forms of this theorem. This one just says that the reduct
-- reduces to the same thing as a.
theorem Expr.RedTyTrans.complete : Expr.RedTyTrans a b → Expr.reduce a = Expr.reduce b := by
  intro h
  induction h
  · exact Expr.RedTy.reduce_same (by assumption)
  · rename_i h _
    have h := h.reduce_same
    simp_all

-- This proof shows that if the reduct under transitive closure of b is a normal form,
-- then reduce produces the same result.
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

theorem reduce_norm : Expr.reduce e = e' → Expr.IsNorm e' := by
  intro h ⟨e'', hr⟩
  unfold Expr.reduce at h
  split at h
  · rename_i e'' h_step
    have h_dec : e''.ty_size < e.ty_size:= (Expr.step?_sound h_step).decreasing'
    exact reduce_norm h (⟨_, hr⟩)
  · rename_i hstep
    have h := hr.step?_complete
    simp_all only [reduceCtorEq]

termination_by e.ty_size

-- Strong normalization of single-step reduction using our decreasing measure.
def Expr.RedTy.SN (e : Expr) : Acc (fun b a => Expr.RedTy a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing'
  exact Expr.RedTy.SN e')
termination_by e.ty_size

-- Strong normalization of transitive closure of single-step reduction using our decreasing measure.
def Expr.RedTyTrans.SN (e : Expr) : Acc (fun b a => Expr.RedTyTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing'
  exact Expr.RedTyTrans.SN e')
termination_by e.ty_size

inductive Expr.RedTm : Expr → Expr → Prop
  | k        : RedTm (SK (K.{[m, n]} α β x y)) x
  | k'       : RedTm (SK (K'.{[m, n]} α β x y)) x
  | s        : RedTm (SK (S.{[m, n, o]} α β γ x y z)) (SK ((x z) (y z)))
  | congrFun : RedTm f f' → RedTm (SK (f x)) (SK (f' x))
  | congrArg : RedTm x x' → RedTm (SK (f x)) (SK (f x'))

def Expr.red_ty : Expr → Option Expr
  | (SK (K.{[_m, _n]} _α _β x _y)) => .some x
  | (SK (K'.{[_m, _n]} _α _β x _y)) => .some x
  | (SK (S.{[_m, _n, _o]} _α _β _γ x y z)) => .some (SK ((x z) (y z)))
  | SK ((f x)) => match f.red_ty, x.red_ty with
    | .some f', _ => .some (SK (f' x))
    | _, .some x' => .some (SK (f x'))
    | _, _ => .none
  | _ => .none
