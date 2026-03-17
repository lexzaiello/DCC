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
  | _e => .none

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
  | next      : RedTyComb ⸨K* A b⸩ A
  | comp      : RedTyComb ⸨B f g x⸩ ⸨f ⸨g x⸩⸩
  | flip      : RedTyComb ⸨C x y z⸩ ⸨x z y⸩
  | read      : RedTyComb ⸨I x⸩ x

def Expr.red_ty_comb (e : Expr) : (Option <| (e' : Expr) × PLift (e.RedTyComb e')) :=
  match e with
  | ⸨K* A _b⸩ => .some ⟨A, ⟨.next⟩⟩
  | ⸨I A⸩ => .some ⟨A, ⟨.read⟩⟩
  | ⸨C x y z⸩ => .some ⟨⸨x z y⸩, ⟨.flip⟩⟩
  | ⸨B f g x⸩ => .some ⟨⸨f ⸨g x⸩⸩, ⟨.comp⟩⟩
  | _ => .none

theorem Expr.RedTyComb.sound (_h : (Expr.red_ty_comb e).isSome) : Expr.RedTyComb e (e.red_ty_comb.get h).fst := (e.red_ty_comb.get h).snd.down

theorem Expr.RedTyComb.complete (h : RedTyComb e e') : (Expr.red_ty_comb e) = .some ⟨e', ⟨h⟩⟩ := by
  induction h
  repeat rfl

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
