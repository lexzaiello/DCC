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
    → Expr.RedTy (SK (f x)) (SK (f' x))
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

instance : WellFoundedRelation Expr := ⟨fun x y => x.ty_size < y.ty_size, (measure (fun e => Expr.ty_size e)).wf⟩

def Expr.RedTyReflTrans := Relation.ReflTransGen Expr.RedTy

def Expr.IsNorm (e : Expr) : Prop := ∀ e', ¬ Expr.RedTy e e'

theorem local_confluence : Expr.RedTy a b → Expr.RedTy a c → ∃ d, b.RedTyReflTrans d ∧ c.RedTyReflTrans d := by
  sorry

theorem Expr.RedTy.is_norm_unique (h₁ : Expr.RedTy e e₁) (h₂ : Expr.RedTy e e₂) (h_norm₁ : e₁.IsNorm) (h_norm₂ : e₂.IsNorm) : e₁ = e₂ := by
  
  sorry

theorem Expr.RedTy.no_step_self : ¬ Expr.RedTy e e := by
  intro h
  induction e
  repeat contradiction
  case app f x ih₁ ih₂ =>
    cases h
    rename_i h
    exfalso
    exact ih₁ h

theorem Expr.RedTyTrans.is_norm_unique (h₁ : Expr.RedTyTrans e e₁) (h₂ : Expr.RedTyTrans e e₂) (h_norm : e.IsNorm) : e₁ = e₂ := by
  induction h₁ generalizing e₂
  rename_i b _
  · have h := h_norm b
    contradiction
  · rename_i b c hrb hredb ih
    induction hrb generalizing e₁
    · rename_i b _
      have h := h_norm b
      contradiction
    · rename_i b' c' hrb' hredc' ih₂
      have h₁ := ih hrb'
      have h₂ := ih h₂
      have h : c'.RedTy c' := by
        simp_all only
      exfalso
      exact h.no_step_self

theorem Expr.RedTyReflTrans.weak_norm : ∃ e', (RedTyReflTrans e e' ∧ e'.IsNorm) := by
  induction e
  · exact ⟨_, .refl, fun e h => by cases h⟩
  · exact ⟨_, .refl, fun e h => by cases h⟩
  · exact ⟨_, .refl, fun e h => by cases h⟩
  · exact ⟨_, .refl, fun e h => by cases h⟩
  · exact ⟨_, .refl, fun e h => by cases h⟩
  case app f x ih₁ ih₂ =>
    have ⟨f', hrf, h_norm_f⟩ := ih₁
    have ⟨x', hrx, h_norm_x⟩ := ih₂
    induction hrf generalizing x x'
    induction hrx generalizing f f'
    
    sorry

--theorem Expr.RedTyTrans.norm (h_size : 

def Expr.reduce (h_size : Expr.TySize e n) : ((e' : Expr) × (PLift (e.RedTyTrans e'))) := by
  
  sorry

/-
inductive Expr.RedexTy : Expr → Prop
  | comp : RedexTy (SK (B f g x))
  | flip : RedexTy (SK (C x y z))
  | next : RedexTy (SK (K* x y))
  | read : RedexTy (SK (I x))

def Expr.ty_is_redex (e : Expr) : Option (PLift e.RedexTy) :=
  match e with
  | SK (B _f _g _x) => .some ⟨.comp⟩
  | SK (C _x _y _z) => .some ⟨.flip⟩
  | SK (K* _x _y) => .some ⟨.next⟩
  | SK (I _x) => .some ⟨.read⟩
  | _e => .none

theorem Expr.RedexTy.sound (h : (Expr.ty_is_redex e).isSome) : e.RedexTy := ((e.ty_is_redex).get h).down

theorem Expr.RedexTy.complete (h : Expr.RedexTy e) : e.ty_is_redex = .some ⟨h⟩ := by
  induction h
  repeat rfl

instance Expr.RedexTy.instDecidable : Decidable (Expr.RedexTy e) :=
  if h : e.ty_is_redex.isSome then
    .isTrue (e.ty_is_redex.get h).down
  else
    .isFalse (fun h => by simp only [h.complete, Option.isSome_some, not_true_eq_false] at *)

inductive Expr.RedTyComb : Expr → Expr → Prop
  | next      : RedTyComb (SK (K* A b)) A
  | comp      : RedTyComb (SK (B f g x)) (SK (f (g x)))
  | flip      : RedTyComb (SK (C x y z)) (SK (x z y))
  | read      : RedTyComb (SK (I x)) x
  | cong      : ¬ (SK (f x)).RedexTy → f.RedTyComb f' → (SK (f x)).RedTyComb (SK (f' x))

def Expr.red_ty_comb? (e : Expr) : (Option <| (e' : Expr) × PLift (e.RedTyComb e')) :=
  if heq₂ : e.RedexTy then
    match heq : e with
    | SK (K* A _b) => .some ⟨A, ⟨.next⟩⟩
    | SK (I A) => .some ⟨A, ⟨.read⟩⟩
    | SK (C x y z) => .some ⟨SK (x z y), ⟨.flip⟩⟩
    | SK (B f g x) => .some ⟨SK (f (g x)), ⟨.comp⟩⟩
  else
    match heq : e with
    | SK (f x) =>
      match f.red_ty_comb? with
      | .some ⟨f', h⟩ =>
        .some ⟨SK (f' x), ⟨.cong (fun h => by
          have h' := h.complete
          simp_all only [not_true_eq_false]) (by exact h.down)⟩⟩
      | _a => .none
    | _a => .none

@[simp] def Expr.ty_size_of : Expr → ℕ
  | SK K* => 2
  | SK B
  | SK C => 3
  | SK I => 1
  | SK (f x) => f.ty_size_of + x.ty_size_of
  | _ => 0

theorem Expr.RedTyComb.sound (h : (Expr.red_ty_comb? e).isSome) : Expr.RedTyComb e ((Expr.red_ty_comb? e).get h).fst := (e.red_ty_comb?.get h).snd.down

theorem Expr.RedTyComb.complete (h : RedTyComb e e') : (Expr.red_ty_comb? e) = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  repeat rfl
  case cong f x f' h_nredex h_red ih =>
    dsimp only [red_ty_comb?]
    simp only [h_nredex, ↓reduceDIte, ih]

inductive Expr.RedexTm : Expr → Prop where
  | k    : RedexTm (SK (K.{[_m, _n]} _α _β _x _y))
  | k'   : RedexTm (SK (K'.{[_m, _n]} _α _β _x _y))
  | s    : RedexTm (SK (S.{[_m, _n, _o]} _α _β _γ _x _y _z))

inductive Expr.RedTm : Expr → Expr → Prop
  | k         : Expr.RedTm x x' → Expr.RedTm (SK (K.{[m, n]} α β x y)) x'
  | k'        : Expr.RedTm x x' → Expr.RedTm (SK (K'.{[m, n]} α β x y)) x'
  | s         : Expr.RedTm x x' → Expr.RedTm y y' → Expr.RedTm z z'
    → Expr.RedTm (SK (S.{[m, n, o]} α β γ x y z)) (SK (((x' z') (y' z'))))
  | app       : (¬ (SK (f x)).RedexTm) → Expr.RedTm f f'
    → Expr.RedTm x x' → Expr.RedTm (SK (f x)) (SK (f' x'))
  | refl_comb : Expr.RedTm (.comb c) (.comb c)
  | refl_ty   : Expr.RedTm (.tycomb c) (.tycomb c)
  | refl_srt  : Expr.RedTm (SK Sort m) (SK Sort m)

/-
{1} I (Srt 0) (Srt 1) = Srt 1
-/

def RedTrans := Relation.TransGen Expr.RedTyComb

def Expr.reduce_ty_n (n : ℕ) (e : Expr) : Option ((e' : Expr) × (PLift (RedTrans e e'))) :=
  match n with
  | .zero => .none
  | .succ .zero => do
    let ⟨e', h⟩ ← e.red_ty_comb?
    .some ⟨e', ⟨match h with | ⟨h⟩ => .single h⟩⟩
  | .succ n => do
    let ⟨inner, h₁⟩ ← e.reduce_ty_n n
    let ⟨inner', h₂⟩ ← inner.red_ty_comb?
    .some ⟨inner', ⟨match h₁, h₂ with
      | ⟨h₁⟩, ⟨h₂⟩ => h₁.tail h₂⟩⟩

theorem all_ty_red_decreasing : Expr.RedTyComb e e' → Expr.ty_size_of e' < Expr.ty_size_of e := by
  intro hr
  induction hr
  repeat (simp [Expr.ty_size_of]; grind only)
  · simp only [Expr.ty_size_of, lt_add_iff_pos_left, zero_lt_one]
  case cong f x f' hr hredf ih =>
    simp only [Expr.ty_size_of, add_lt_add_iff_right, ih]

theorem all_ty_red_decreasing' : PLift (Expr.RedTyComb e e') → Expr.ty_size_of e' < Expr.ty_size_of e := fun h =>
  match h with
  | .up h => all_ty_red_decreasing h

def Expr.TyRedTrans := Relation.TransGen Expr.RedTyComb

def Expr.reduce_ty (e : Expr) : Option ((e' : Expr) × (PLift (Expr.TyRedTrans e e'))) := do
  let _size := e.ty_size_of
  let ⟨e', h⟩ ← e.red_ty_comb?
  if _h : 0 < e.ty_size_of then
    have _h_size : e'.ty_size_of < e.ty_size_of := all_ty_red_decreasing' h
    let ⟨e'', r⟩ ← e'.reduce_ty
    .some ⟨e'', ⟨.trans (.single h.down) r.down⟩⟩
  else .some ⟨e', ⟨.single h.down⟩⟩

def Expr.reduce_ty_sound : Expr.reduce_ty e = ⟨e', hr⟩ → Expr.TyRedReflTrans e e' := fun _ => hr

/-def Expr.reduce_complete (h : Expr.CRedTrans e e')
  (h_pos : e.ty_size_of > 0) : Expr.reduce e h_pos = .some ⟨e', h⟩ := by
  induction h
  · unfold Expr.reduce
    simp only [gt_iff_lt]
    rename_i hr
    have h := hr.down
    cases h
    dsimp [Expr.red_ty_comb?]

    sorry
  sorry-/

inductive RedPiArg (arg : Expr) : Expr → Expr → Prop
  | srt : RedPiArg arg (SK Sort m) (SK Sort m)
  | pi  : RedPiArg arg α α' → RedPiArg arg β β'
    → RedPiArg arg (SK Π α, β) (SK Π α', β')
  | red : (SK (f arg)).TyRedReflTrans e' → RedPiArg arg f e'

def Expr.reduce_pi_arg (in_pi arg : Expr) : (e' : Expr) × (PLift (RedPiArg arg in_pi e')) :=
  match in_pi with
  | SK Sort m => ⟨SK Sort m, ⟨.srt⟩⟩
  | SK Π α, β =>
    let ⟨α', ⟨h₁⟩⟩ := α.reduce_pi_arg arg
    let ⟨β', ⟨h₂⟩⟩ := β.reduce_pi_arg arg
    ⟨(SK Π α', β'), ⟨.pi h₁ h₂⟩⟩
  | SK e =>
    let ⟨e', h⟩ := Expr.reduce_ty (SK (e arg))
    ⟨e', ⟨.red h⟩⟩

def Expr.RedPiArg.sound (_h : Expr.reduce_pi_arg in_pi arg = ⟨e', ⟨hp⟩⟩) : RedPiArg arg in_pi e' := hp

def arg (n : ℕ) : Expr :=
  match n with
  | 0 => SK I
  | 1 => SK K*
  | .succ n => SK (B K* #(arg n))

-/
