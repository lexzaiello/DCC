import Dcc.Ast
import Dcc.Relation

open Relation (ReflTransGen)

/-
An alternative η-reduction algorithm that does not appeal to semantics.

simple algorithm:
- extend AST with a constructor "hole"
- apply "hole" to expr

Base eta:
  Hole = 0 ... n
  If application reduces to:
  - Hole -> function eta-reduces to Id
  - f' Hole -> function reduces to f'
  - c, where c does not contain Hole -> eta-reduces to `(α, c)

If domain is:
- Coup(β)
  - hole = ⟦β⟧(1, 2)
  Projection eta:
    If application reduces to:
    1. Base eta (hole := 1), η-reduces to f₁
      -> eta-reduces to f₁ ∘' Fstc(β)
    2. Base eta (hole := 2), η-reduces to f₁
      -> eta-reduces to f₁ ∘' Sndc(β)

- Sort | ⊤ | (Π(f_α, f_β) ...) | (f x)
  Use base
-/

inductive Hole where
  | mk : ℕ → Hole
deriving BEq, Repr, DecidableEq

gen_ast as EtaExpr
  with Hole *
  deriving BEq, Repr, DecidableEq, Inhabited
gen_dsl "DCCη" for EtaExpr

namespace EtaExpr

inductive RedAffEta : EtaExpr → EtaExpr → Prop
  | pil      : RedAffEta f_α f_α' → RedAffEta (DCCη Π(f_α, f_β)) (DCCη Π(f_α', f_β))
  | pir      : RedAffEta f_β f_β' → RedAffEta (DCCη Π(f_α, f_β)) (DCCη Π(f_α, f_β'))
  | eql      : RedAffEta (DCCη (Eql(f_α) env &(x))) (DCCη x = x)
  | eql'     : RedAffEta x x' → RedAffEta (DCCη (x = y)) (DCCη (x' = y))
  | eqr'     : RedAffEta y y' → RedAffEta (DCCη (x = y)) (DCCη (x = y'))
  | bang     : RedAffEta x x' → RedAffEta (DCCη !(x)) (DCCη !(x'))
  | map      : RedAffEta (DCCη (!<f> &(x))) (DCCη !((f x)))
  | fmap     : RedAffEta (DCCη ($<f> &(x))) (DCCη &((f x)))
  | unbox    : RedAffEta (DCCη (*(α) &(x))) x
  | pair     : RedAffEta (DCCη (⟦β⟧⟨M, N⟩ &(x))) (DCCη ⟦β⟧((M x), (N x (M x))))
  | evalc    : RedAffEta (DCCη (Eval(_α, _β, x) ⟦__β⟧(y, z))) (DCCη (x y z))
  | quot     : RedAffEta (DCCη (`(β, x) y)) x
  | id       : RedAffEta (DCCη (Id(α) x)) x
  | fstc     : RedAffEta (DCCη (Fstc(_α) ⟦β⟧(a, b))) a
  | sndc     : RedAffEta (DCCη (Sndc(_α) ⟦β⟧(a, b))) b
  | comp'    : RedAffEta (DCCη ((x ∘' y) z)) (DCCη (x (y z)))
  | comp     : RedAffEta (DCCη ((x ∘ y) z)) (DCCη (x (y z)))
  | comp₂    : RedAffEta (DCCη ((x ∘∘ y) z)) (DCCη (x (y z)))
  | curr     : RedAffEta (DCCη (Λ(α, β, x) y z)) (DCCη (x ⟦β⟧(y, z)))
  | curr'    : RedAffEta (DCCη (!Λ(α, β, x) &(y) &(z))) (DCCη (x &(⟦β⟧(y, z))))
  | sigl     : RedAffEta x x' → RedAffEta (DCCη ⟦β⟧(x, y)) (DCCη ⟦β⟧(x', y))
  | sigr     : RedAffEta y y' → RedAffEta (DCCη ⟦β⟧(x, y)) (DCCη ⟦β⟧(x, y'))
  | pairl    : RedAffEta x x' → RedAffEta (DCCη ⟦β⟧⟨x, y⟩) (DCCη ⟦β⟧⟨x', y⟩)
  | pairr    : RedAffEta y y' → RedAffEta (DCCη ⟦β⟧⟨x, y⟩) (DCCη ⟦β⟧⟨x, y'⟩)
  | sigma    : RedAffEta (DCCη (Σ(f_α, f_β) env)) (DCCη (Coup((f_β env))))
  | coup     : RedAffEta β β' → RedAffEta (DCCη (Coup(β))) (DCCη (Coup(β')))
  | congrFun : RedAffEta f f' → RedAffEta (DCCη (f x)) (DCCη (f' x))
  | congrArg : RedAffEta x x' → RedAffEta (DCCη (f x)) (DCCη (f x'))

@[dcc_force_reduce, dcc_force_aff]
def step? (e : EtaExpr) : Option ((e' : EtaExpr) × (PULift.{1, 0} (RedAffEta e e'))) :=
  match e with
  | (DCCη Π(f_α, f_β)) =>
    match f_α.step?, f_β.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.pil h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.pir h₁⟩⟩
    | _, _ => .none
  | (DCCη (Eql(_f_α) _env &(_x))) => .some ⟨_, ⟨.eql⟩⟩
  | (DCCη (x = y)) =>
    match x.step?, y.step? with
    | .some ⟨_, ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.eql' h₁⟩⟩
    | _, .some ⟨_, ⟨h₁⟩⟩ => .some ⟨_, ⟨.eqr' h₁⟩⟩
    | _, _ => .none
  | DCCη !(x) =>
    match x.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.bang h⟩⟩
    | _ => .none
  | DCCη (!<_f> &(_x))                                 => .some ⟨_, ⟨.map⟩⟩
  | DCCη ($<_f> &(_x))                                 => .some ⟨_, ⟨.fmap⟩⟩
  | DCCη (*(_α) &(_x))                                 => .some ⟨_, ⟨.unbox⟩⟩
  | DCCη ((⟦_β⟧⟨_M, _N⟩ &(_x)))                        => .some ⟨_, ⟨.pair⟩⟩
  | (DCCη (Eval(_α, _β, _x) ⟦__β⟧(_y, _z)))            => .some ⟨_, ⟨.evalc⟩⟩
  | (DCCη (`(_β, _x) _y))                              => .some ⟨_, ⟨.quot⟩⟩
  | (DCCη (Id(_α) _x))                                 => .some ⟨_, ⟨.id⟩⟩
  | (DCCη (Fstc(_α) ⟦_γ⟧(_a, _b)))                     => .some ⟨_, ⟨.fstc⟩⟩
  | (DCCη (Sndc(_α) ⟦_γ⟧(_a, _b)))                     => .some ⟨_, ⟨.sndc⟩⟩
  | (DCCη ((_x ∘' _y) _z))                             => .some ⟨_, ⟨.comp'⟩⟩
  | (DCCη ((_x ∘ _y) _z))                              => .some ⟨_, ⟨.comp⟩⟩
  | (DCCη ((_x ∘∘ _y) _z))                             => .some ⟨_, ⟨.comp₂⟩⟩
  | (DCCη (!Λ(_α, _β, _x) &(_y) &(_z)))                => .some ⟨_, ⟨.curr'⟩⟩
  | (DCCη (Λ(_α, _β, _x) _y _z))                       => .some ⟨_, ⟨.curr⟩⟩
  | (DCCη (Σ(_f_α, _f_β) _env))                        => .some ⟨_, ⟨.sigma⟩⟩
  | DCCη ⟦β⟧(x, y) =>
    match x.step?, y.step? with
    | .some ⟨x', ⟨h₁⟩⟩, _ => .some ⟨(DCCη ⟦β⟧(x', y)), ⟨.sigl h₁⟩⟩
    | _, .some ⟨y', ⟨h₁⟩⟩ => .some ⟨(DCCη ⟦β⟧(x, y')), ⟨.sigr h₁⟩⟩
    | _, _ => .none
  | DCCη ⟦_β⟧⟨x, y⟩ =>
    match x.step?, y.step? with
    | .some ⟨_x', ⟨h₁⟩⟩, _ => .some ⟨_, ⟨.pairl h₁⟩⟩
    | _, .some ⟨_y', ⟨h₁⟩⟩ => .some ⟨_, ⟨.pairr h₁⟩⟩
    | _, _ => .none
  | (DCCη (Coup(β))) =>
    match β.step? with
    | .some ⟨_, ⟨h⟩⟩ => .some ⟨_, ⟨.coup h⟩⟩
    | _ => .none
  | DCCη (f x) =>
    match f.step?, x.step? with
    | .some ⟨f', ⟨h₁⟩⟩, _ => .some ⟨(DCCη (f' x)), ⟨.congrFun h₁⟩⟩
    | _, .some ⟨x', ⟨h₁⟩⟩ => .some ⟨(DCCη (f x')), ⟨.congrArg h₁⟩⟩
    | _, _ => .none
  | _ => .none

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind] def size (e : EtaExpr) : ℕ :=
  match e with
  | DCCη ∗ => 0
  | DCCη ⊤ => 2
  | DCCη ⊥ => 2
  | DCCη x = y => x.size + y.size
  | DCCη Eql(α)  => α.size + 3
  | DCCη refl(α) => α.size + 2
  | DCCη Sort m => m
  | DCCη Σ(α, β) => α.size + β.size + 2
  | DCCη `(β, x) => β.size + x.size + 2
  | DCCη ⟦_β⟧(x, y) => x.size + y.size
  | DCCη Coup(β) => β.size
  | DCCη Id(α)      => α.size + 2
  | DCCη Fstc(α)    => α.size + 2
  | DCCη Sndc(α)    => α.size + 2
  | DCCη Π(α, β) => α.size + β.size + 1
  | DCCη (f ∘' g) => f.size + f.size + g.size + 2
  | DCCη (f ∘ g)  => f.size + f.size + g.size + 2
  | DCCη (f ∘∘ g)  => f.size + f.size + g.size + 2
  | DCCη ⟦_β⟧⟨a, b⟩   => a.size + a.size + b.size + 2
  | DCCη Λ(α, β, x) => α.size + β.size + x.size + 2
  | DCCη !Λ(α, β, x) => α.size + β.size + x.size + 2
  | DCCη Eval(_α, _β, x) => x.size + 1
  | DCCη !(x)   => x.size
  | DCCη *(α)   => α.size + 1
  | DCCη &(x)   => x.size + x.size + x.size + 2
  | DCCη !<x>   => x.size + x.size + x.size + 2
  | DCCη $<x>   => x.size + x.size + x.size + 2
  | DCCη (f x) => f.size + x.size
  | .hole _n => 1


@[dcc_force_reduce, dcc_force_aff]
instance RedAffEta.instRedRel : Expr.RedRel RedAffEta size where
  run := step?

theorem bang' (h : Relation.ReflTransGen RedAffEta x x') : Relation.ReflTransGen RedAffEta (DCCη !(x)) (DCCη !(x')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.bang (by assumption)))

theorem pairl' (h : Relation.ReflTransGen RedAffEta x x') : Relation.ReflTransGen RedAffEta (DCCη ⟦β⟧⟨x, y⟩) (DCCη ⟦β⟧⟨x', y⟩) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pairl (by assumption)))

theorem pairr' (h : Relation.ReflTransGen RedAffEta y y') : Relation.ReflTransGen RedAffEta (DCCη ⟦β⟧⟨x, y⟩) (DCCη ⟦β⟧⟨x, y'⟩) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pairr (by assumption)))

theorem eql'' (h : Relation.ReflTransGen RedAffEta x x') : Relation.ReflTransGen RedAffEta (DCCη (x = y)) (DCCη (x' = y)) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.eql' (by assumption)))

theorem eqr'' (h : Relation.ReflTransGen RedAffEta y y') : Relation.ReflTransGen RedAffEta (DCCη (x = y)) (DCCη (x = y')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.eqr' (by assumption)))

theorem pil' (h : Relation.ReflTransGen RedAffEta f_α f_α') : Relation.ReflTransGen RedAffEta (DCCη Π(f_α, f_β)) (DCCη Π(f_α', f_β)) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pil (by assumption)))

theorem pir' (h : Relation.ReflTransGen RedAffEta f_β f_β') : Relation.ReflTransGen RedAffEta (DCCη Π(f_α, f_β)) (DCCη Π(f_α, f_β')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.pir (by assumption)))

theorem coup' (h : ReflTransGen RedAffEta β β') : ReflTransGen RedAffEta (DCCη Coup(β)) (DCCη Coup(β')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.coup (by assumption)))

theorem sigl' (h : ReflTransGen RedAffEta x x') : ReflTransGen RedAffEta (DCCη ⟦β⟧(x, y)) (DCCη ⟦β⟧(x', y)) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.sigl (by assumption)))

theorem sigr' (h : ReflTransGen RedAffEta y y') : ReflTransGen RedAffEta (DCCη ⟦β⟧(x, y)) (DCCη ⟦β⟧(x, y')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.sigr (by assumption)))

theorem congrFun' (h : ReflTransGen RedAffEta f f') : ReflTransGen RedAffEta (DCCη (f x)) (DCCη (f' x)) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.congrFun (by assumption)))

theorem congrArg' (h : ReflTransGen RedAffEta x x') : ReflTransGen RedAffEta (DCCη (f x)) (DCCη (f x')) := by
  induction h with
  | refl => exact .refl
  | tail ih h a_ih =>
    exact .trans a_ih (.single (.congrArg (by assumption)))

@[dcc_reduce, aesop safe apply (rule_sets := [DccReduce])] theorem RedAffEta.conf (h₁ : RedAffEta A B) (h₂ : RedAffEta A C) : ∃ D, RedAffEta.instRedRel.ReflTrans B D ∧ RedAffEta.instRedRel.ReflTrans C D := by
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
  | unbox =>
    cases h₂ with
    | unbox => exact ⟨_, .refl, .refl⟩
    | congrArg h => cases h
    | congrFun h => cases h
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
    case comp₂ | fmap | map | unbox | fstc | sndc | sigma | evalc | comp' | quot | id | comp => cases h_r
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
    | map
    | unbox
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
instance RedAff.instConf : Expr.Confluent RedAffEta := ⟨RedAffEta.conf⟩

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instConfRedAffTrans : Expr.Confluent RedAffEta (m := Relation.ReflTransGen) := RedAffEta.instRedRel.globally_confluent

def semi_complete {A B : EtaExpr} (hr : A.RedAffEta B) : ∃ B', ∃ (h : A.RedAffEta B'), (step? A) = .some ⟨B', ⟨h⟩⟩ := by
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
  repeat exact ⟨_, (RedAffEta.instRedRel.sound rfl).down, rfl⟩
  case h_20 =>
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
  case h_21 =>
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
  case h_22 =>
    cases hr with
    | coup h =>
      have ⟨_, hrx', heq'⟩ := semi_complete h
      exact ⟨_, .coup hrx', by simp_all⟩
  case h_23 =>
    cases hr with
    | eql => simp_all
    | curr' =>
      rename_i h
      exact (h _ _ _ _ _ rfl rfl).elim
    | unbox =>
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
      rename_i f x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      match f.step? with
      | .none => exact ⟨_, .congrArg hrx, by simp_all⟩
      | .some ⟨_, ⟨hrf⟩⟩ => exact ⟨_, .congrFun hrf, by simp⟩
    | comp₂ | comp' | quot | id | comp => simp_all
    | curr =>
      rename_i h _
      exact (h _ _ _ _ rfl).elim
  case h_24 hpi heql heq hbang _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmk hpair hcoup happ =>
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

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance RedAff.instSemicomplete : Expr.SemiComplete RedAffEta := ⟨semi_complete⟩

theorem aff_complete (h : Relation.ReflTransGen RedAffEta A B)
  (hn : Expr.IsNorm RedAffEta B) : Expr.reduce RedAffEta A = ⟨B, ⟨h⟩⟩ :=
  RedAffEta.instRedRel.instComplete.complete h hn

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance instComplete : Expr.Complete (Relation.ReflTransGen RedAffEta) (P := Expr.IsNorm RedAffEta) := RedAffEta.instRedRel.instComplete

end EtaExpr
