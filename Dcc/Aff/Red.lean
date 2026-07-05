import Dcc.Attrs
import Dcc.Ast
import Dcc.Relation
import Dcc.Aff.Size

namespace GenericExpr

/-
Preservation proof:
- can make these more type-directed
-/

inductive RedAff.{u} {τ : Type u} : GenericExpr τ → GenericExpr τ → Prop
  | pil      : RedAff f_α f_α' → RedAff (DCC[τ] Π(f_α, f_β)) (DCC[τ] Π(f_α', f_β))
  | pir      : RedAff f_β f_β' → RedAff (DCC[τ] Π(f_α, f_β)) (DCC[τ] Π(f_α, f_β'))
  | eql      : RedAff (DCC[τ] (Eql(f_α) env &(x))) (DCC[τ] x = x)
  | eql'     : RedAff x x' → RedAff (DCC[τ] (x = y)) (DCC[τ] (x' = y))
  | eqr'     : RedAff y y' → RedAff (DCC[τ] (x = y)) (DCC[τ] (x = y'))
  | bang     : RedAff x x' → RedAff (DCC[τ] !(x)) (DCC[τ] !(x'))
  | map      : RedAff (DCC[τ] (!<f> &(x))) (DCC[τ] !((f x)))
  | fmap     : RedAff (DCC[τ] ($<f> &(x))) (DCC[τ] &((f x)))
  | unbox    : RedAff (DCC[τ] (*(α) &(x))) x
  | unmap    : RedAff (DCC[τ] (*<f> &(x))) (DCC[τ] (f x))
  | pair     : RedAff (DCC[τ] (⟦β⟧⟨M, N⟩ &(x))) (DCC[τ] ⟦β⟧((M x), (N x (M x))))
  | evalc    : RedAff (DCC[τ] (Eval(_α, _β, x) ⟦__β⟧(y, z))) (DCC[τ] (x y z))
  | quot     : RedAff (DCC[τ] (`(β, x) y)) x
  | id       : RedAff (DCC[τ] (Id(α) x)) x
  | fstc     : RedAff (DCC[τ] (Fstc(_α) ⟦β⟧(a, b))) a
  | sndc     : RedAff (DCC[τ] (Sndc(_α) ⟦β⟧(a, b))) b
  | comp'    : RedAff (DCC[τ] ((x ∘' y) z)) (DCC[τ] (x (y z)))
  | comp     : RedAff (DCC[τ] ((x ∘ y) z)) (DCC[τ] (x (y z)))
  | comp₂    : RedAff (DCC[τ] ((x ∘∘ y) z)) (DCC[τ] (x (y z)))
  | curr     : RedAff (DCC[τ] (Λ(α, β, x) y z)) (DCC[τ] (x ⟦β⟧(y, z)))
  | curr'    : RedAff (DCC[τ] (!Λ(α, β, x) &(y) &(z))) (DCC[τ] (x &(⟦β⟧(y, z))))
  | sigl     : RedAff x x' → RedAff (DCC[τ] ⟦β⟧(x, y)) (DCC[τ] ⟦β⟧(x', y))
  | sigr     : RedAff y y' → RedAff (DCC[τ] ⟦β⟧(x, y)) (DCC[τ] ⟦β⟧(x, y'))
  | pairl    : RedAff x x' → RedAff (DCC[τ] ⟦β⟧⟨x, y⟩) (DCC[τ] ⟦β⟧⟨x', y⟩)
  | pairr    : RedAff y y' → RedAff (DCC[τ] ⟦β⟧⟨x, y⟩) (DCC[τ] ⟦β⟧⟨x, y'⟩)
  | sigma    : RedAff (DCC[τ] (Σ(f_α, f_β) env)) (DCC[τ] (Coup((f_β env))))
  | coup     : RedAff β β' → RedAff (DCC[τ] (Coup(β))) (DCC[τ] (Coup(β')))
  | congrFun : RedAff f f' → RedAff (DCC[τ] (f x)) (DCC[τ] (f' x))
  | congrArg : RedAff x x' → RedAff (DCC[τ] (f x)) (DCC[τ] (f x'))

@[dcc_force_reduce, dcc_force_aff]
def step?.{u} {τ : Type u} (e : GenericExpr τ) : Option ((e' : GenericExpr τ) × (PULift.{u + 1, 0} (RedAff (τ := τ) e e'))) :=
  match e with
  | (DCC[?] Π(f_α, f_β)) =>
    match f_α.step?, f_β.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.pil h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.pir h₁⟩⟩
    | _, _ => .none
  | (DCC[?] (Eql(_f_α) _env &(_x))) => .some ⟨_, ⟨.eql⟩⟩
  | (DCC[?] (x = y)) =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.eql' h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.eqr' h₁⟩⟩
    | _, _ => .none
  | DCC[?] !(x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.bang h⟩⟩
    | _ => .none
  | DCC[?] (!<_f> &(_x))                                 => .some ⟨_, ⟨.map⟩⟩
  | DCC[?] ($<_f> &(_x))                                 => .some ⟨_, ⟨.fmap⟩⟩
  | DCC[?] (*(_α) &(_x))                                 => .some ⟨_, ⟨.unbox⟩⟩
  | DCC[?] (*<_α> &(_x))                                 => .some ⟨_, ⟨.unmap⟩⟩
  | DCC[?] ((⟦_β⟧⟨_M, _N⟩ &(_x)))                        => .some ⟨_, ⟨.pair⟩⟩
  | (DCC[?] (Eval(_α, _β, _x) ⟦__β⟧(_y, _z)))            => .some ⟨_, ⟨.evalc⟩⟩
  | (DCC[?] (`(_β, _x) _y))                              => .some ⟨_, ⟨.quot⟩⟩
  | (DCC[?] (Id(_α) _x))                                 => .some ⟨_, ⟨.id⟩⟩
  | (DCC[?] (Fstc(_α) ⟦_γ⟧(_a, _b)))                     => .some ⟨_, ⟨.fstc⟩⟩
  | (DCC[?] (Sndc(_α) ⟦_γ⟧(_a, _b)))                     => .some ⟨_, ⟨.sndc⟩⟩
  | (DCC[?] ((_x ∘' _y) _z))                             => .some ⟨_, ⟨.comp'⟩⟩
  | (DCC[?] ((_x ∘ _y) _z))                              => .some ⟨_, ⟨.comp⟩⟩
  | (DCC[?] ((_x ∘∘ _y) _z))                             => .some ⟨_, ⟨.comp₂⟩⟩
  | (DCC[?] (!Λ(_α, _β, _x) &(_y) &(_z)))                => .some ⟨_, ⟨.curr'⟩⟩
  | (DCC[?] (Λ(_α, _β, _x) _y _z))                       => .some ⟨_, ⟨.curr⟩⟩
  | (DCC[?] (Σ(_f_α, _f_β) _env))                        => .some ⟨_, ⟨.sigma⟩⟩
  | DCC[?] ⟦β⟧(x, y) =>
    match x.step?, y.step? with
    | .some ⟨x', ⟨h₁⟩⟩, _ => .some ⟨(DCC[?] ⟦β⟧(x', y)), ⟨.sigl h₁⟩⟩
    | _, .some ⟨y', ⟨h₁⟩⟩ => .some ⟨(DCC[?] ⟦β⟧(x, y')), ⟨.sigr h₁⟩⟩
    | _, _ => .none
  | DCC[?] ⟦_β⟧⟨x, y⟩ =>
    match x.step?, y.step? with
    | .some ⟨_x', ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.pairl h₁⟩⟩
    | _, .some ⟨_y', ⟨h₁⟩⟩ => .some ⟨_, ⟨.pairr h₁⟩⟩
    | _, _ => .none
  | (DCC[?] (Coup(β))) =>
    match β.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
    | _ => .none
  | DCC[?] (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCC[?] (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCC[?] (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | _ => .none

@[dcc_force_reduce, dcc_force_aff]
instance RedAff.instRedRel.{u} {τ : Type u} : RedRel (α := GenericExpr τ) (RedAff (τ := τ)) size where
  run := step?

theorem red_aff_sn.{u} {τ : Type u} : ∀ (e : GenericExpr τ), Acc (fun b a => RedAff (τ := τ) a b) e := RedAff.instRedRel.sn

theorem red_aff_trans_sn.{u} {τ : Type u} [DecidableEq τ] : ∀ (e : GenericExpr τ), Acc (fun b a => Relation.TransGen RedAff a b) e := RedAff.instRedRel.to_trans.sn

instance RedAff.instCongruent.{u} {τ : Type u} : Congruent (RedAff (τ := τ)) where

theorem bang'.{u} {α : Type u} {x x' : GenericExpr α} (h : Relation.ReflTransGen (RedAff (τ := α)) x x') : Relation.ReflTransGen RedAff (DCC[α] !(x)) (DCC[α] !(x')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.bang (by assumption)))

theorem pairl'.{u} {α : Type u} {β x y x' : GenericExpr α} (h : Relation.ReflTransGen (RedAff (τ := α)) x x') : Relation.ReflTransGen RedAff (DCC[α] ⟦β⟧⟨x, y⟩) (DCC[α] ⟦β⟧⟨x', y⟩) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pairl (by assumption)))

theorem pairr'.{u} {α : Type u} {β x y y' : GenericExpr α} (h : Relation.ReflTransGen (RedAff (τ := α)) y y') : Relation.ReflTransGen RedAff (DCC[α] ⟦β⟧⟨x, y⟩) (DCC[α] ⟦β⟧⟨x, y'⟩) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pairr (by assumption)))

theorem eql''.{u} {α : Type u} {x y x' : GenericExpr α} (h : Relation.ReflTransGen (RedAff (τ := α)) x x') : Relation.ReflTransGen RedAff (DCC[α] (x = y)) (DCC[α] (x' = y)) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.eql' (by assumption)))

theorem eqr''.{u} {α : Type u} {x y y' : GenericExpr α} (h : Relation.ReflTransGen (RedAff (τ := α)) y y') : Relation.ReflTransGen RedAff (DCC[α] (x = y)) (DCC[α] (x = y')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.eqr' (by assumption)))

theorem pil'.{u} {α : Type u} {f_α f_β f_α' : GenericExpr α} (h : Relation.ReflTransGen (RedAff (τ := α)) f_α f_α') : Relation.ReflTransGen RedAff (DCC[α] Π(f_α, f_β)) (DCC[α] Π(f_α', f_β)) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pil (by assumption)))

theorem pir'.{u} {α : Type u} {f_α f_β f_β' : GenericExpr α} (h : Relation.ReflTransGen (RedAff (τ := α)) f_β f_β') : Relation.ReflTransGen RedAff (DCC[α] Π(f_α, f_β)) (DCC[α] Π(f_α, f_β')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pir (by assumption)))

open Congruent in @[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])]
theorem RedAff.conf.{u} {α : Type u} {A B C : GenericExpr α} (h₁ : (RedAff (τ := α)) A B) (h₂ : RedAff A C) : ∃ D, RedAff.instRedRel.ReflTrans B D ∧ RedAff.instRedRel.ReflTrans C D := by
  induction h₁ generalizing C with
  | eql =>
    cases h₂ with
    | eql =>
      exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .refl, .single .eql⟩
    | congrArg h => cases h
  | eql' hr a_ih =>
    cases h₂ with
    | eql' hr₂ =>
      have ⟨D, h₁, h₂⟩ := a_ih hr₂
      exact ⟨_, eql'' h₁, eql'' h₂⟩
    | eqr' hr₂ =>
      exact ⟨_, .single (.eqr' (by assumption)), .single (.eql' (by assumption))⟩
   | pil hr a_ih =>
    cases h₂ with
    | pil hr₂ =>
      have ⟨D, h₁, h₂⟩ := a_ih hr₂
      exact ⟨_, pil' h₁, pil' h₂⟩
    | pir hr₂ =>
      exact ⟨_, .single (.pir (by assumption)), .single (.pil (by assumption))⟩
  | pir hr a_ih =>
    cases h₂ with
    | pir hr₂ =>
      have ⟨D, h₁, h₂⟩ := a_ih hr₂
      exact ⟨_, pir' h₁, pir' h₂⟩
    | pil hr₂ =>
      exact ⟨_, .single (.pil (by assumption)), .single (.pir (by assumption))⟩
  | eqr' hr a_ih =>
    cases h₂ with
    | eqr' hr₂ =>
      have ⟨D, h₁, h₂⟩ := a_ih hr₂
      exact ⟨_, eqr'' h₁, eqr'' h₂⟩
    | eql' hr₂ =>
      exact ⟨_, .single (.eql' (by assumption)), .single (.eqr' (by assumption))⟩
  | pairl hr₁ ih =>
    cases h₂ with
    | pairl hr₂ =>
      have ⟨D, h₁, h₂⟩ := ih hr₂
      exact ⟨_, pairl' (by assumption), pairl' (by assumption)⟩
    | pairr =>
      exact ⟨_, ⟨.single (.pairr (by assumption)), .single (.pairl (by assumption))⟩⟩
  | pairr hr₁ ih =>
    cases h₂ with
    | pairr hr₂ =>
      have ⟨D, h₁, h₂⟩ := ih hr₂
      exact ⟨_, ⟨pairr' (by assumption), pairr' (by assumption)⟩⟩
    | pairl =>
      exact ⟨_, ⟨.single (.pairl (by assumption)), .single (.pairr (by assumption))⟩⟩
  | bang hr₁ ih =>
    cases h₂ with
    | bang hr₂ =>
      have ⟨D, h₁, h₂⟩ := ih hr₂
      exact ⟨_, ⟨bang' (by assumption), bang' (by assumption)⟩⟩
  | map =>
    cases h₂ with
    | map => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => cases h
  | fmap =>
    cases h₂ with
    | fmap => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => cases h
  | unbox | unmap =>
    cases h₂ with
    | congrArg h => cases h
    | congrFun h => cases h
    | _ => exact ⟨_, .refl, .refl⟩
  | pair =>
    cases h₂ with
    | pair => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | pairl =>
        exact ⟨_, (.trans (.single (.sigl (.congrFun (by assumption)))) (.single (.sigr (.congrArg (.congrFun (by assumption)))))), .single .pair⟩
      | pairr =>
        exact ⟨_, .single (.sigr (.congrFun (.congrFun (by assumption)))), .single .pair⟩
    | congrArg h => cases h
  | evalc =>
    cases h₂ with
    | evalc => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h =>
      cases h with
      | sigl h => exact ⟨_, .single (.congrFun (.congrArg h)), .single .evalc⟩
      | sigr h => exact ⟨_, .single (.congrArg h), .single .evalc⟩
  | sigma =>
    cases h₂ with
    | sigma => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.coup (.congrArg h)), .single .sigma⟩
  | coup hr₁ ih =>
    cases h₂ with
    | coup hr₂ =>
      have ⟨_, ha, hb⟩ := ih hr₂
      exact ⟨_, coup' ha, coup' hb⟩
  | quot =>
    cases h₂ with
    | quot => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .refl, .single .quot⟩
  | id =>
    cases h₂ with
    | id => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single h, .single .id⟩
  | sigl h ih =>
    cases h₂ with
    | sigl h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, sigl' h₁, sigl' h₂⟩
    | sigr h =>
      exact ⟨_, .single (.sigr h), .single (.sigl (by assumption))⟩
  | sigr h ih =>
    cases h₂ with
    | sigl h =>
      exact ⟨_, .single (.sigl h), .single (.sigr (by assumption))⟩
    | sigr h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, sigr' h₁, sigr' h₂⟩
  | fstc =>
    cases h₂ with
    | fstc => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => cases h with
      | sigl h => exact ⟨_, .single h, .single .fstc⟩
      | sigr h => exact ⟨_, .refl, .single .fstc⟩
  | sndc =>
    cases h₂ with
    | sndc => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => cases h with
      | sigl h => exact ⟨_, .refl, .single .sndc⟩
      | sigr h => exact ⟨_, .single h, .single .sndc⟩
  | comp =>
    cases h₂ with
    | comp => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp⟩
  | comp₂ =>
    cases h₂ with
    | comp₂ => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp₂⟩
  | comp' =>
    cases h₂ with
    | comp' => exact ⟨_, .refl, .refl⟩
    | congrFun h => cases h
    | congrArg h => exact ⟨_, .single (.congrArg (.congrArg (by assumption))), .single .comp'⟩
  | curr =>
    cases h₂ with
    | curr => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single (.congrArg (.sigl h)), .single .curr⟩
    | congrArg h => exact ⟨_, .single (.congrArg (.sigr (by assumption))), .single .curr⟩
  | curr' =>
    cases h₂ with
    | curr' => exact ⟨_, .refl, .refl⟩
    | congrFun h =>
      cases h with
      | congrFun h => cases h
      | congrArg h => cases h
    | congrArg h => cases h
  | congrFun h_r ih =>
    cases h₂
    case comp₂ | fmap | map | unmap | unbox | fstc | sndc | sigma | evalc | comp' | quot | id | comp => cases h_r
    case eql =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .eql, .refl⟩
    case pair =>
      cases h_r with
      | pairl =>
        exact ⟨_, .single .pair, .trans (.single (.sigl (.congrFun (by assumption)))) (.single (.sigr (.congrArg (.congrFun (by assumption)))))⟩
      | pairr =>
        exact ⟨_, .single .pair, .single (.sigr (.congrFun (.congrFun (by assumption))))⟩
    case curr =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => exact ⟨_, .single .curr, .single (.congrArg (.sigl (by assumption)))⟩
    case curr' =>
      cases h_r with
      | congrFun h => cases h
      | congrArg h => cases h
    case congrFun f f' x f'' h =>
      have ⟨_, h₁, h₂⟩ := ih h
      exact ⟨_, congrFun' h₁, congrFun' h₂⟩
    case congrArg f f' x x'' h_x =>
      exact ⟨_, congrArg' (.single h_x), congrFun' (.single h_r)⟩
  | congrArg h_r ih =>
    cases h₂ with
    | eql
    | fmap
    | map | unbox | unmap
    | pair => cases h_r
    | evalc => cases h_r with
      | sigl h => exact ⟨_, .single .evalc, .single (.congrFun (.congrArg h))⟩
      | sigr h => exact ⟨_, .single .evalc, .single (.congrArg h)⟩
    | fstc => cases h_r with
      | sigl h => exact ⟨_, .single .fstc, .single h⟩
      | sigr h => exact ⟨_, .single .fstc, .refl⟩
    | sndc => cases h_r with
      | sigl h => exact ⟨_, .single .sndc, .refl⟩
      | sigr h => exact ⟨_, .single .sndc, .single h⟩
    | quot => exact ⟨_, .single .quot, .refl⟩
    | id => exact ⟨_, .single .id, .single h_r⟩
    | comp₂  => exact ⟨_, .single .comp₂, congrArg' (congrArg' (.single (by assumption)))⟩
    | comp  => exact ⟨_, .single .comp, congrArg' (congrArg' (.single (by assumption)))⟩
    | comp' => exact ⟨_, .single .comp', congrArg' (congrArg' (.single (by assumption)))⟩
    | curr  => exact ⟨_, .single .curr, congrArg' (sigr' (.single (by assumption)))⟩
    | curr' => cases h_r
    | sigma => exact ⟨_, .single .sigma, coup' (.single (.congrArg (by assumption)))⟩
    | congrFun => exact ⟨_, congrFun' (.single (by assumption)), congrArg' (.single (by assumption))⟩
    | congrArg h =>
      have ⟨D, h₁, h₂⟩ := ih h
      exact ⟨_, congrArg' h₁, congrArg' h₂⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instConf.{u} {τ : Type u} : Confluent (RedAff (τ := τ)) := ⟨RedAff.conf⟩

theorem red_aff_globally_conf.{u} {τ : Type u} {A B C : GenericExpr τ} : Relation.ReflTransGen (RedAff (τ := τ)) A B → Relation.ReflTransGen RedAff A C → ∃ D,
  Relation.ReflTransGen RedAff B D ∧ Relation.ReflTransGen RedAff C D :=
  RedAff.instRedRel.globally_confluent.conf

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instConfRedAffTrans.{u} {τ : Type u} : Confluent (RedAff (τ := τ)) (m := Relation.ReflTransGen) := RedAff.instRedRel.globally_confluent

def semi_complete.{u} {τ : Type u} {A B : GenericExpr τ} (hr : A.RedAff B) : ∃ B', ∃ (h : A.RedAff B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
  change ∃ _, ∃ _, (step? _) = .some _
  unfold step?
  split
  case h_1 =>
    rename_i e x y
    cases hr with
    | pil hr =>
      have ⟨_, h, heq⟩ := semi_complete hr
      exact ⟨_, .pil (by assumption), by rw [heq]⟩
    | pir hr =>
      split
      case h_1 hr heq => exact ⟨_, .pil hr, rfl⟩
      case h_2 hr heq ih => exact ⟨_, .pir hr, rfl⟩
      case h_3 ih₁ ih₂ =>
        have ⟨_, hr, heq⟩ := semi_complete hr
        exact (ih₂ _ hr heq).elim
  case h_2 => exact ⟨_, .eql, rfl⟩
  case h_3 =>
    rename_i e x y
    cases hr with
    | eql' hr =>
      have ⟨_, h, heq⟩ := semi_complete hr
      exact ⟨_, .eql' (by assumption), by rw [heq]⟩
    | eqr' hr =>
      split
      case h_1 hr heq => exact ⟨_, .eql' hr, rfl⟩
      case h_2 hr heq ih => exact ⟨_, .eqr' hr, rfl⟩
      case h_3 ih₁ ih₂ =>
        have ⟨_, hr, heq⟩ := semi_complete hr
        exact (ih₂ _ hr heq).elim
  case h_4 =>
    cases hr with
    | bang hr =>
      have ⟨B, h, heq⟩ := semi_complete hr
      simp [heq]
      exact .bang h
  repeat exact ⟨_, (RedAff.instRedRel.sound rfl), rfl⟩
  case h_21 =>
    cases hr with
    | sigl h_x =>
      have ⟨_, hrx', heq'⟩ := semi_complete h_x
      exact ⟨_, .sigl (by assumption), by rw [heq']⟩
    | sigr h_y =>
      rename_i x y _
      have ⟨_, hry', heq'⟩ := semi_complete h_y
      match x.step? with
      | .none =>
        exact ⟨_, .sigr (by assumption), by rw [heq']⟩
      | .some ⟨_, ⟨h_x'⟩⟩ =>
        exact ⟨_, .sigl (by assumption), by rw [heq']⟩
  case h_22 =>
    cases hr with
    | pairl h =>
      have ⟨_, hrx', heq'⟩ := semi_complete h
      exact ⟨_, .pairl hrx', by simp_all⟩
    | pairr h =>
      rename_i x y _
      have ⟨_, hry', heq'⟩ := semi_complete h
      match x.step? with
      | .none =>
        exact ⟨_, .pairr (by assumption), by rw [heq']⟩
      | .some ⟨_, ⟨h_x'⟩⟩ =>
        exact ⟨_, .pairl (by assumption), by rw [heq']⟩
  case h_23 =>
    cases hr with
    | coup h =>
      have ⟨_, hrx', heq'⟩ := semi_complete h
      exact ⟨_, .coup hrx', by simp_all⟩
  case h_24 =>
    cases hr with
    | eql => simp_all
    | curr' =>
      rename_i h
      exact (h _ _ _ _ _ rfl rfl).elim
    | unmap | unbox =>
      simp_all
    | pair =>
      simp_all
      rename_i h
      exact (h _ _ _ _ rfl rfl rfl rfl).elim
    | evalc =>
      simp_all
      rename_i h
      exact (h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl).elim
    | sigma => simp_all
    | fstc =>
      simp_all
      rename_i h
      exact (h _ _ _ _ rfl rfl rfl rfl).elim
    | sndc =>
      simp_all
      rename_i h
      exact (h _ _ _ _ rfl rfl rfl rfl).elim
    | fmap | map => simp_all
    | congrFun h =>
      have ⟨_, hrf, heqf⟩ := semi_complete h
      exact ⟨_, .congrFun hrf, by rw [heqf]⟩
    | congrArg h =>
      have ⟨_, hrx, heqx⟩ := semi_complete h
      rename_i f x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      match f.step? with
      | .none => exact ⟨_, .congrArg hrx, by simp_all⟩
      | .some ⟨_, ⟨hrf⟩⟩ => exact ⟨_, .congrFun hrf, by simp⟩
    | comp₂ | comp' | quot | id | comp => simp_all
    | curr =>
      rename_i h _
      exact (h _ _ _ _ rfl).elim
  case h_25 hpi heql heq hbang _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmk hpair hcoup happ =>
    simp_all
    induction A <;> (
      first
      | (focus
        cases hr
        done)
      | (exact (hpi _ _ rfl).elim)
      | (exact (hcoup _ rfl).elim)
      | (exact (happ _ _ rfl).elim)
      | (exact (hmk _ _ _ rfl).elim)
      | (exact (hpair _ _ _ rfl).elim)
      | (exact (hbang _ rfl).elim)
      | (exact (heq _ _ rfl).elim))

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance RedAff.instSemicomplete.{u} {τ : Type u} : SemiComplete (RedAff (τ := τ)) := ⟨semi_complete⟩

theorem aff_complete (h : Relation.ReflTransGen RedAff A B)
  (hn : IsNorm RedAff B) : reduce RedAff A = ⟨B, ⟨h⟩⟩ :=
  RedAff.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance instComplete.{u} {τ : Type u} : Complete (Relation.ReflTransGen (RedAff (τ := τ))) (P := IsNorm RedAff) := RedAff.instRedRel.instComplete

-- RedRel.reduce Size RedAff.instRedRel : (e : Expr) → (e' : Expr) × PULift (Relation.ReflTransGen RedAff e e')
#check reduce RedAff

/-
Complete.complete
  Id : ∀ (h : Relation.ReflTransGen RedAff ?m.8 ?m.9), IsNorm RedAff ?m.9 → Rel.run Id ?m.8 = pure ⟨?m.9, { down := h }⟩
-/
#check instComplete.complete

@[grind ., grind →]
theorem red_aff_decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : Relation.ReflTransGen (RedAff (τ := τ)) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← Relation.reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := RedAff.instRedRel.to_trans.decreasing h
      grind

@[grind ., grind →]
theorem red_aff_trans_decreasing.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] : Relation.TransGen (RedAff (τ := τ)) A B → (size B) < (size A) :=
  RedAff.instRedRel.to_trans.decreasing

@[dcc_force_reduce, dcc_force_aff]
abbrev RedAff.reduce.{u} {τ : Type u} := GenericExpr.reduce (RedAff (τ := τ))

attribute [dcc_force_reduce, dcc_force_aff] RedAff.reduce.eq_def

instance RedAff.instDecidableNorm.{u} {α : Type u} [DecidableEq α]
{A : GenericExpr α}  : Decidable (IsNorm (RedAff (τ := α)) A) :=
  match heq₀ : GenericExpr.reduce RedAff A with
  | ⟨A', ⟨h⟩⟩ =>
    if heq : A' = A then
      have h_norm := reduce_norm (h := heq ▸ h) (A := A) (B := A) (hR := RedAff.instRedRel) (heq ▸ heq₀)
      .isTrue (fun ⟨a, b⟩ => by
        exact h_norm ⟨_, b⟩)
    else
      .isFalse (fun h => by
        have h := RedAff.instRedRel.reduce_norm_fst h
        simp_all)

@[dcc_judge]
def RedAffReflTrans.{u} {τ : Type u} := Relation.ReflTransGen (RedAff (τ := τ))

theorem RedAffReflTrans.reflGen_transGen.{u} {τ : Type u} : Relation.ReflGen (Relation.TransGen RedAff) = RedAffReflTrans (τ := τ) :=
  Relation.reflGen_transGen

@[dcc_judge]
def RedAffTrans.{u} {τ : Type u} := Relation.TransGen (RedAff (τ := τ))

namespace RedAffTrans

def single (r : RedAff A B) : RedAffTrans A B := Relation.TransGen.single r

def trans (r₁ : RedAffTrans A B) (r₂ : RedAffTrans B C) : RedAffTrans A C := Relation.TransGen.trans r₁ r₂

def to_reflTrans {a b : Expr} (r : RedAffTrans a b) : RedAffReflTrans a b :=
  Relation.TransGen.to_reflTransGen (a := a) (b := b) r

end RedAffTrans

namespace RedAffReflTrans

def cases_head.{u} {τ_c : Type u} {a b : GenericExpr τ_c} (r : RedAffReflTrans a b) :=
  Relation.ReflTransGen.cases_head (a := a) (b := b) r

def single.{u} {τ : Type u} {A B : GenericExpr τ}
  (r : RedAff A B) : (RedAffReflTrans (τ := τ)) A B := Relation.ReflTransGen.single r

def trans.{u} {τ : Type u} {A B C : GenericExpr τ} (r₁ : RedAffReflTrans A B)
  (r₂ : RedAffReflTrans B C) : RedAffReflTrans A C := Relation.ReflTransGen.trans r₁ r₂

def conf.{u} {τ : Type u} {A B C : GenericExpr τ} (h₁ : RedAffReflTrans A B) (h₂ : RedAffReflTrans A C) : ∃ D, RedAffReflTrans B D ∧ RedAffReflTrans C D := RedAff.instRedRel.globally_confluent.conf h₁ h₂

def elim_head_norm.{u} {τ : Type u} {A B : GenericExpr τ} (h : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B :=
  hn.unique_refl h

@[grind ., grind →]
theorem red_aff_decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := by
  if hs : (size A) = (size B) then
    simp_all
  else
    rw [← reflGen_transGen] at h
    match h with
    | .refl => grind
    | .single h =>
      have hn' : B.size < A.size := RedAff.instRedRel.to_trans.decreasing h
      grind

def elim_norm (hr : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

@[grind ., grind <=]
theorem elim_norm' (hr : RedAffReflTrans A B) (hn : IsNorm RedAff A) : A = B := by
  change Relation.ReflTransGen _ _ _ at hr
  exact hn.unique_refl hr

def push_head (hr₁ : RedAffReflTrans A C) (hn : IsNorm RedAff C) (hr₂ : RedAff A B) : RedAffReflTrans B C :=
  have ⟨_, h₁, h₂⟩ := RedAff.instRedRel.globally_confluent.conf hr₁ (.single hr₂)
  hn.unique_refl h₁ ▸ h₂

end RedAffReflTrans

namespace RedAffTrans

@[grind ., grind →]
theorem red_aff_trans_decreasing.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] : (RedAffTrans (τ := τ)) A B → (size B) < (size A) := by
  change Relation.TransGen _ _ _ → _
  exact (RedAff.instRedRel (τ := τ)).to_trans.decreasing

end RedAffTrans

namespace RedAff

abbrev decreasing.{u} {τ_c : Type u} (x y : GenericExpr τ_c) := (RedAff.instRedRel (τ := τ_c)).decreasing (x := x) (y := y)

end RedAff

namespace RedAffReflTrans

def push_head' (hr₁ : RedAffReflTrans A C) (hn : IsNorm RedAff C) (hr₂ : RedAffReflTrans A B) : RedAffReflTrans B C := by
  have ⟨_, h₁, h₂⟩ := hr₁.conf hr₂
  have heq := hn.unique_refl h₁
  exact heq ▸ h₂

@[grind ., grind →]
theorem decreasing?.{u} {τ : Type u} {A B : GenericExpr τ} [DecidableEq τ] (h : (RedAffReflTrans (τ := τ)) A B) : (size B) ≤ (size A) := red_aff_decreasing? h

end RedAffReflTrans

inductive RedAffNorm : GenericExpr τ_c → NormExpr (RedAff (τ := τ_c)) → Type u
  | mk : (hr : RedAffReflTrans A B) → (hn : IsNorm RedAff B) → RedAffNorm A ⟨B, hn⟩

@[dcc_step]
def RedAffNorm.decreasing? (h : RedAffNorm A B) : B.size ≤ A.size :=
  match h with
  | ⟨hr, _hn⟩ => GenericExpr.decreasing? _ hr

@[grind]
def RedAffNorm.raw (_r : RedAffNorm (τ_c := τ_c) A B) : NormExpr (RedAff (τ := τ_c)) := B

@[grind]
def aff_sound (heq : reduce RedAff A = ⟨B, ⟨h⟩⟩) : RedAffNorm A ⟨B, reduce_norm heq⟩ := ⟨reduce_sound heq, reduce_norm heq⟩

@[grind]
def aff_sound' (A : GenericExpr τ_c) : RedAffNorm A ⟨(reduce RedAff A).fst, reduce_norm rfl⟩ := ⟨reduce_sound rfl, reduce_norm rfl⟩

@[grind, inline, dcc_reduce]
def red_aff (A : GenericExpr τ_c) : NormExpr (RedAff (τ := τ_c)) := ⟨(reduce RedAff A).fst, reduce_norm (A := A) rfl⟩

@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
def RedAffNorm.complete {A : GenericExpr τ_c} {B : NormExpr RedAff (τ := τ_c)} (h : RedAffNorm A B) : red_aff A = B :=
  match h with
  | ⟨hr, hn⟩ => by
    have ha := reduce_complete_fst hr hn
    simp [red_aff, ha]

@[dcc_reduce]
def RedAffNorm.eq (hr : RedAffNorm e (red_aff e)) : hr = aff_sound rfl :=
  match hr with
  | ⟨hr, hn⟩ => by
    have heq := reduce_complete hr hn
    grind

abbrev RedAffNorm.red (h : RedAffNorm A ⟨B, hn⟩) : RedAffReflTrans A B :=
  match h with
  | ⟨hr, _⟩ => hr

def RedAffNorm.aff_complete (h : RedAffNorm A ⟨B, hn⟩) : reduce RedAff A = ⟨B, ⟨h.red⟩⟩ :=
  match h with
  | ⟨hr₁, hn₁⟩ => reduce_complete hr₁ hn₁

/-def RedAffNorm.eq {A : GenericExpr τ_c} {B : NormExpr RedAff (τ := τ_c)} (h₁ : RedAffNorm A B) : h₁ = aff_sound (by sorry) := by
  sorry-/

end GenericExpr

abbrev Expr.RedAff := GenericExpr.RedAff (τ := Unit)
