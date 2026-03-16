import Dcc.Ast2

inductive Expr.RedexTy : Expr → Prop
  | comp : RedexTy ⸨B f g x⸩
  | flip : RedexTy ⸨C x y z⸩
  | next : RedexTy ⸨K* x y⸩
  | read : RedexTy ⸨I x⸩

def Expr.ty_is_redex (e : Expr) : Option (PLift e.RedexTy) :=
  match e with
  | ⸨B _f _g _x⸩ => .some ⟨.comp⟩
  | ⸨C _x _y _z⸩ => .some ⟨.flip⟩
  | ⸨K* _x _y⸩ => .some ⟨.next⟩
  | ⸨I _x⸩ => .some ⟨.read⟩
  | _ => .none

theorem Expr.RedexTy.sound (h : (Expr.ty_is_redex e).isSome) : e.RedexTy := ((e.ty_is_redex).get h).down

theorem Expr.RedexTy.complete (h : Expr.RedexTy e) : e.ty_is_redex = .some ⟨h⟩ := by
  induction h
  repeat rfl

instance Expr.RedexTy.instDecidable : Decidable (Expr.RedexTy e) :=
  if h : e.ty_is_redex.isSome then
    .isTrue (e.ty_is_redex.get h).down
  else
    .isFalse (fun h => by simp [h.complete] at *)

inductive Expr.RedTyComb : Expr → Expr → Prop
  | next     : RedTyComb A A'  → RedTyComb ⸨K* A b⸩ A'
  | comp     : RedTyComb f f'  → RedTyComb g g' → RedTyComb x x' → RedTyComb ⸨B f g x⸩ ⸨f' ⸨g' x'⸩⸩
  | flip     : RedTyComb x x'  → RedTyComb y y' → RedTyComb z z' → RedTyComb ⸨C x y z⸩ ⸨x' z' y'⸩
  | read     : RedTyComb x x'  → RedTyComb ⸨I x⸩ x'
  | app      : ¬ ⸨f x⸩.RedexTy → RedTyComb f f' → RedTyComb x x' → RedTyComb ⸨f x⸩ ⸨f' x'⸩
  | refl_c   : RedTyComb (.comb c) (.comb c)
  | refl_ty  : RedTyComb (.tycomb c) (.tycomb c)
  | refl_srt : RedTyComb (Srt m) (Srt m)

def Expr.red_ty_comb (e : Expr) : Option ((e' : Expr) × (PLift (e.RedTyComb e'))) :=
  if _h : e.ty_is_redex.isSome then
    match e with
    | ⸨K* A _b⸩ => do
      let ⟨A', ⟨p⟩⟩ ← A.red_ty_comb
      .some ⟨A', ⟨.next p⟩⟩
    | ⸨I A⸩ => do
      let ⟨A', ⟨p⟩⟩ ← A.red_ty_comb
      .some ⟨A', ⟨.read p⟩⟩
    | ⸨C x y z⸩ => do
      let ⟨x', ⟨p₁⟩⟩ ← x.red_ty_comb
      let ⟨y', ⟨p₂⟩⟩ ← y.red_ty_comb
      let ⟨z', ⟨p₃⟩⟩ ← z.red_ty_comb
      .some ⟨⸨x' z' y'⸩, ⟨.flip p₁ p₂ p₃⟩⟩
    | ⸨B f g x⸩ => do
      let ⟨f', ⟨p₁⟩⟩ ← f.red_ty_comb
      let ⟨g', ⟨p₂⟩⟩ ← g.red_ty_comb
      let ⟨x', ⟨p₃⟩⟩ ← x.red_ty_comb
      .some ⟨⸨f' ⸨g' x'⸩⸩, ⟨.comp p₁ p₂ p₃⟩⟩
  else match heq : e with
    | ⸨f x⸩ => do
      let ⟨f', ⟨p₁⟩⟩ ← f.red_ty_comb
      let ⟨x', ⟨p₂⟩⟩ ← x.red_ty_comb
      have h : ¬ ⸨f x⸩.RedexTy := fun h => by
        have h := h.complete
        simp_all
      .some ⟨⸨f' x'⸩, ⟨.app h p₁ p₂⟩⟩
    | .comb c => .some ⟨.comb c, ⟨.refl_c⟩⟩
    | .tycomb c => .some ⟨.tycomb c, ⟨.refl_ty⟩⟩
    | (Srt m) => .some ⟨Srt m, ⟨.refl_srt⟩⟩
    | _ => .none

theorem Expr.RedTyComb.sound (h : (Expr.red_ty_comb e).isSome) : Expr.RedTyComb e ((Expr.red_ty_comb e).get h).fst := ((e.red_ty_comb).get h).snd.down

theorem Expr.RedTyComb.complete (h : RedTyComb e e') : (Expr.red_ty_comb e) = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  · rename_i ih
    unfold Expr.red_ty_comb
    unfold Expr.ty_is_redex
    simp [ih]
  · rename_i ih₁ ih₂ ih₃
    unfold Expr.red_ty_comb
    unfold Expr.ty_is_redex
    simp [ih₁, ih₂, ih₃]
  · rename_i ih₁ ih₂ ih₃
    unfold Expr.red_ty_comb
    unfold Expr.ty_is_redex
    simp [ih₁, ih₂, ih₃]
  · rename_i ih
    unfold Expr.red_ty_comb
    unfold Expr.ty_is_redex
    simp [ih]
  case app f x f' x' h_red hr₁ hr₂ ih₁ ih₂ =>
    have h : ¬ ⸨f x⸩.ty_is_redex.isSome := fun h => by
      have h := Expr.RedexTy.sound h
      simp_all
    unfold Expr.red_ty_comb
    simp_all
  repeat (unfold Expr.red_ty_comb; simp; intro h; contradiction)

inductive Expr.RedexTm : Expr → Prop where
  | k    : RedexTm ⸨K.{[_m, _n]} _α _β _x _y⸩
  | k'   : RedexTm ⸨K'.{[_m, _n]} _α _β _x _y⸩
  | s    : RedexTm ⸨S.{[_m, _n, _o]} _α _β _γ _x _y _z⸩

inductive RedTm : Expr → Expr → Prop
  | k         : RedTm x x' → RedTm ⸨K.{[m, n]} α β x y⸩ x'
  | k'        : RedTm x x' → RedTm ⸨K'.{[m, n]} α β x y⸩ x'
  | s         : RedTm x x' → RedTm y y' → RedTm z z'
    → RedTm ⸨S.{[m, n, o]} α β γ x y z⸩ ⸨⸨x' z'⸩ ⸨y' z'⸩⸩
  | app       : (¬ ⸨f x⸩.RedexTm) → RedTm f f'
    → RedTm x x' → RedTm ⸨f x⸩ ⸨f' x'⸩
  | refl_comb : RedTm (.comb c) (.comb c)
  | refl_ty   : RedTm (.tycomb c) (.tycomb c)
  | refl_srt  : RedTm (Srt m) (Srt m)
