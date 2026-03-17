import Dcc.Ast2
import Init.Data.Option.Lemmas
import Mathlib.Logic.Relation
import Mathlib.Tactic

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

inductive Expr.TyRedReflTrans : Expr → Expr → Type where
  | single : PLift (e.RedTyComb e') → Expr.TyRedReflTrans e e'
  | trans  : (PLift (a.RedTyComb b)) → Expr.TyRedReflTrans b c → Expr.TyRedReflTrans a c
  | refl   : Expr.TyRedReflTrans e e

def Expr.reduce_ty (e : Expr) : ((e' : Expr) × (Expr.TyRedReflTrans e e')) :=
  let _size := e.ty_size_of
  let r := e.red_ty_comb?
  match r with
  | .some ⟨e', h⟩ =>
    if _h : 0 < e.ty_size_of then
      have _h_size : e'.ty_size_of < e.ty_size_of := all_ty_red_decreasing' h
      let ⟨e'', r⟩ := e'.reduce_ty
      ⟨e'', .trans h r⟩
    else ⟨e', .single h⟩
  | _ => ⟨e, .refl⟩

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

