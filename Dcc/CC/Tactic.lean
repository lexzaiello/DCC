import Dcc.CC.Ast
import Dcc.CC.Step2
import Dcc.CC.Judge
import Qq
import Qq.MetaM
import Lean.Elab
import Lean.Elab.Term

open Lean Elab Qq Lean.Elab

namespace tactic

abbrev MLevel := Lean.Expr

inductive MExpr where
  | sort  : MLevel    → MExpr
  | flip  : MExpr     → MExpr
  | id    : MExpr     → MExpr
  | fst   : MExpr     → MExpr  → MExpr
  | snd   : MExpr     → MExpr  → MExpr
  -- Nondependent snd
  | snd'  : MExpr     → MExpr  → MExpr
  | quot  : MExpr     → MExpr  → MExpr  → MExpr
  | comp  : MExpr     → MExpr  → MExpr  → MExpr
  -- Nondependent composition
  | comp' : MExpr     → MExpr  → MExpr
  | pair  : MExpr     → MExpr  → MExpr  → MExpr  → MExpr
  | sigma : MExpr     → MExpr  → MExpr
  | mk    : MExpr     → MExpr  → MExpr
  | pi    : MLevel    → MLevel → MExpr
  | curr  : MExpr     → MExpr  → MExpr
  -- Nondependent curry
  | curr' : MExpr     → MExpr  → MExpr  → MExpr
  | appl  : MLevel    → MExpr  → MExpr → MExpr
  | app   : MExpr     → MExpr  → MExpr
  | lean  : Lean.Expr → MExpr
deriving BEq, Repr

def MExpr.from_expr (e : Q(_root_.Expr)) : TermElabM MExpr :=
  match e with
  | ~q(Expr.sort $m) => return .sort m
  | _ =>
    match e with
    | .app (.const ``Expr.const []) e => MExpr.flip <$> from_expr e
    | .app (.const ``Expr.id []) e => MExpr.id <$> from_expr e
    | .app (.app (.const ``Expr.fst []) α) β => do
      return MExpr.fst (← from_expr α) (← from_expr β)
    | .app (.app (.const ``Expr.snd []) α) β => do
      return MExpr.snd (← from_expr α) (← from_expr β)
    | .app (.app (.const ``Expr.snd' []) α) β => do
      return MExpr.snd' (← from_expr α) (← from_expr β)
    | .app (.app (.app (.const ``Expr.quot []) α) β) x => do
      return MExpr.quot (← from_expr α) (← from_expr β) (← from_expr x)
    | .app (.app (.const ``Expr.comp' []) α) β => do
      return MExpr.comp' (← from_expr α) (← from_expr β)
    | .app (.app (.app (.app (.const ``Expr.pair []) α) β) x) y => do
      return MExpr.pair
        (← from_expr α)
        (← from_expr β)
        (← from_expr x)
        (← from_expr y)
    | .app (.app (.const ``Expr.sigma []) α) β => do
      return MExpr.sigma (← from_expr α) (← from_expr β)
    | .app (.app (.const ``Expr.mk []) α) β => do
      return MExpr.mk (← from_expr α) (← from_expr β)
    | .app (.app (.const ``Expr.pi []) m) n =>
      return MExpr.pi m n
    | .app (.app (.const ``Expr.curr []) α) x => do
      return MExpr.curr (← from_expr α) (← from_expr x)
    | .app (.app (.app (.const ``Expr.curr' []) α) β) x => do
      return MExpr.curr' (← from_expr α) (← from_expr β) (← from_expr x)
    | .app (.app (.app (.const ``Expr.appl []) m) α) x => do
      return MExpr.appl m (← from_expr α) (← from_expr x)
    | .app f x =>
      (do pure <| (← from_expr f).app (← from_expr x)) <|> return .lean e
    | e => return .lean e

namespace MExpr

declare_syntax_cat mexpr

syntax "#(" term ")"                                             : mexpr
syntax:max "Flip(" mexpr,* ")"                                    : mexpr
syntax:max "Id(" mexpr ")"                                        : mexpr
syntax:max "Fst(" mexpr,* ")"                                     : mexpr
syntax:max "App(" term "," mexpr,* ")"                            : mexpr
syntax:max "Snd(" mexpr,* ")"                                     : mexpr
syntax:max "Snd'(" mexpr,* ")"                                    : mexpr
syntax:max "`(" mexpr,* ")"                                       : mexpr
syntax "Σ(" mexpr,* ")"                                           : mexpr
syntax:max (priority := high) "Λ(" mexpr,* ")"                    : mexpr
syntax:max (priority := high) "Λ'(" mexpr,* ")"                   : mexpr
syntax:max (priority := high) "Π(" term,* ")"                    : mexpr
syntax mexpr "∘'" mexpr                                            : mexpr
syntax "⟦" mexpr,* "⟧" "∘"                                        : mexpr
syntax:30 ident                                                  : mexpr
syntax "(" mexpr+ ")"                                             : mexpr
syntax:max "Sort" term                                           : mexpr
syntax (priority := high) "⟦" mexpr,* "⟧" "⟨" mexpr,* "⟩" : mexpr
syntax (priority := high) "⟦" mexpr,* "⟧" "(" mexpr,* ")"          : mexpr
syntax (priority := high) "⟦" mexpr,* "⟧" "(" "," ")"             : mexpr
syntax (priority := high) "⟦" mexpr,* "⟧" "(" "," mexpr ")"        : mexpr

syntax "MDCC"  mexpr : term

macro_rules
  | `(MDCC ($f:mexpr $x:mexpr))                    => `(MExpr.app   (MDCC $f:mexpr)   (MDCC $x:mexpr))
  | `(MDCC ($f:mexpr $x:mexpr $xs:mexpr*))          => `(MDCC (($f:mexpr $x:mexpr) $xs:mexpr*))
  | `(MDCC `($α:mexpr, $β:mexpr, $x:mexpr))         => `(MExpr.quot (MDCC $α) (MDCC $β) (MDCC $x))
  | `(MDCC Λ($α:mexpr, $e:mexpr))                  => `(MExpr.curr (MDCC $α) (MDCC $e))
  | `(MDCC Λ'($α:mexpr, $β:mexpr, $e:mexpr))        => `(MExpr.curr' (MDCC $α) (MDCC $β) (MDCC $e))
  | `(MDCC Π($m:term, $n:term))                  => `(MExpr.pi $m $n)
  | `(MDCC ⟦$α:mexpr, $β:mexpr⟧⟨$x:mexpr, $y:mexpr⟩) => `(MExpr.pair (MDCC $α) (MDCC $β) (MDCC $x) (MDCC $y))
  | `(MDCC ⟦$α:mexpr, $β:mexpr⟧(,))                => `(MExpr.mk (MDCC $α) (MDCC $β))
  | `(MDCC ⟦$α:mexpr, $β:mexpr⟧(, $x:mexpr))        => `(MDCC (⟦$α, $β⟧(,) $x))
  | `(MDCC ⟦$α:mexpr, $β:mexpr⟧($x:mexpr, $y:mexpr)) => `(MDCC (⟦$α, $β⟧(,) $x $y))
  | `(MDCC Sort $m:term)                         => `(MExpr.sort $m)
  | `(MDCC Σ($α:mexpr, $β:mexpr))                  => `(MExpr.sigma (MDCC $α) (MDCC $β))
  | `(MDCC Flip($e:mexpr))                        => `(MExpr.flip (MDCC $e))
  | `(MDCC Id($α:mexpr))                          => `(MExpr.id (MDCC $α))
  | `(MDCC Fst($α:mexpr, $β:mexpr))                => `(MExpr.fst (MDCC $α) (MDCC $β))
  | `(MDCC Snd($α:mexpr, $β:mexpr))                => `(MExpr.snd (MDCC $α) (MDCC $β))
  | `(MDCC Snd'($α:mexpr, $β:mexpr))               => `(MExpr.snd' (MDCC $α) (MDCC $β))
  | `(MDCC App($n:term, $α:mexpr, $β:mexpr))       => `(MExpr.appl $n (MDCC $α) (MDCC $β))
  | `(MDCC ⟦$α:mexpr, $β:mexpr, $γ:mexpr⟧∘)         => `(MExpr.comp (MDCC $α:mexpr) (MDCC $β:mexpr) (MDCC $γ:mexpr))
  | `(MDCC $f:mexpr ∘' $g:mexpr)                   => `(MExpr.comp' (MDCC $f:mexpr) (MDCC $g:mexpr))
  | `(MDCC #($t:term))                           => `($t)
  | `(MDCC $idt:ident)                           => `($idt:term)
  | `(MDCC ($t:mexpr))                            => `(MDCC $t)


def unify (e : MExpr) : Lean.Elab.Tactic.TacticM Q(_root_.Expr) :=
  match e with
  | MDCC Sort m => do
    let e := Lean.Expr.app (.const ``_root_.Expr.sort []) m
    let some e' ← checkTypeQ e q(_root_.Expr) | throwError s!"not an expr: {e}"
    return e'
  | .lean e => do
    let some e ← checkTypeQ e q(_root_.Expr) | throwError s!"not an expr: {e}"
    return e
  | MDCC (Λ(α, x)) => do
    let α ← α.unify
    let x ← x.unify
    return q(_root_.Expr.curr $α $x)
  | MDCC (Λ'(α, β, x)) => do
    let α ← α.unify
    let β ← β.unify
    let x ← x.unify
    return q(_root_.Expr.curr' $α $β $x)
  | MDCC (App(m, α, x)) => do
    let α ← α.unify
    let x ← x.unify
    let some m' ← checkTypeQ m q(_root_.Level) | throwError s!"not a level: {m}"
    return q(_root_.Expr.appl $m' $α $x)
  | MDCC (Π(m, n)) => do
    let some m' ← checkTypeQ m q(_root_.Level) | throwError s!"not a level: {m}"
    let some n' ← checkTypeQ n q(_root_.Level) | throwError s!"not a level: {n}"
    return q(_root_.Expr.pi $m' $n')
  | MDCC (Σ(α, β)) => do
    let α ← α.unify
    let β ← β.unify
    return q(_root_.Expr.sigma $α $β)
  | MDCC (Fst(α, β)) => do
    let α ← α.unify
    let β ← β.unify
    return q(_root_.Expr.fst $α $β)
  | MDCC (Snd(α, β)) => do
    let α ← α.unify
    let β ← β.unify
    return q(_root_.Expr.snd $α $β)
  | MDCC (Snd'(α, β)) => do
    let α ← α.unify
    let β ← β.unify
    return q(_root_.Expr.snd' $α $β)
  | MDCC (Id(α)) => do
    let α ← α.unify
    return q(_root_.Expr.id $α)
  | MDCC (`(α, β, x)) => do
    let α ← α.unify
    let β ← β.unify
    let x ← x.unify
    return q(_root_.Expr.quot $α $β $x)
  | MDCC (Flip(x)) => do
    let x ← x.unify
    return q(_root_.Expr.flip $x)
  | MDCC (⟦α, β⟧(,)) => do
    let α ← α.unify
    let β ← β.unify
    return q(_root_.Expr.mk $α $β)
  | MDCC ⟦α, β⟧⟨a, b⟩ => do
    let α ← α.unify
    let β ← β.unify
    let a ← a.unify
    let b ← b.unify
    return q(_root_.Expr.pair $α $β $a $b)
  | MDCC f ∘' g => do
    let f ← f.unify
    let g ← g.unify
    return q(_root_.Expr.comp' $f $g)
  | MDCC ⟦α, β, γ⟧∘ => do
    let α ← α.unify
    let β ← β.unify
    let γ ← γ.unify
    return q(_root_.Expr.comp $α $β $γ)
  | MDCC (f x) => do
    let f' ← f.unify
    let x' ← x.unify
    return q(_root_.Expr.app $f' $x')

inductive RedAff' : MExpr → MExpr → Type
  | app      : RedAff' (MDCC (App(_n, _δ, _τ) ⟦α, β⟧(f, x))) (MDCC (f x))
  | fst      : RedAff' (MDCC (Fst(_δ, _τ) ⟦α, β⟧(a, b))) a
  | snd      : RedAff' (MDCC (Snd(_δ, _τ) ⟦α, β⟧(a, b))) b
  | snd'     : RedAff' (MDCC (Snd'(_δ, _τ) ⟦α, β⟧(a, b))) b
  | flip     : RedAff' (MDCC (Flip(e) x y)) (MDCC (e y x))
  | id       : RedAff' (MDCC (Id(_α) x)) x
  | quot     : RedAff' (MDCC (`(_α, _β, x) y)) x
  | comp     : RedAff' (MDCC ((⟦α, β, γ⟧∘ x y) z)) (MDCC (x (y z)))
  | comp'    : RedAff' (MDCC ((x ∘' y) z)) (MDCC (x (y z)))
  | curr     : RedAff' (MDCC (Λ(α, x) y z)) (MDCC (x ⟦α, Id(α)⟧(y, z)))
  | curr'    : RedAff' (MDCC (Λ'(α, β, x) y z)) (MDCC (x ⟦α, β⟧(y, z)))
  | congrFun : RedAff' f f' → RedAff' (MDCC (f x)) (MDCC (f' x))
  | congrArg : RedAff' x x' → RedAff' (MDCC (f x)) (MDCC (f x'))
  | lean     : Lean.Expr    → RedAff' A B

def step? (e : MExpr) : Lean.Elab.Tactic.TacticM (Option ((e' : MExpr) × (RedAff' e e'))) :=
  match e with
  | (MDCC (App(_n, _δ, _τ) ⟦_α, _β⟧(f, x)))  => return .some ⟨(MDCC (f x)), .app⟩
  | (MDCC (Fst(_δ, _τ) ⟦_α, _β⟧(a, _b)))     => return .some ⟨a, .fst⟩
  | (MDCC (Snd(_δ, _τ) ⟦_α, _β⟧(_a, b)))     => return .some ⟨b, .snd⟩
  | (MDCC (Snd'(_δ, _τ) ⟦_α, _β⟧(_a, b)))    => return .some ⟨b, .snd'⟩
  | (MDCC (Flip(e) x y))                     => return .some ⟨(MDCC (e y x)), .flip⟩
  | (MDCC (Id(_α) x))                        => return .some ⟨x, .id⟩
  | (MDCC (`(_α, _β, x) _y))                 => return .some ⟨x, .quot⟩
  | (MDCC ((⟦_α, _β, _γ⟧∘ x y) z))           => return .some ⟨(MDCC (x (y z))), .comp⟩
  | (MDCC ((x ∘' y) z))                      => return .some ⟨(MDCC (x (y z))), .comp'⟩
  | (MDCC (Λ(α, x) y z))                     => return .some ⟨(MDCC (x ⟦α, Id(α)⟧(y, z))), .curr⟩
  | (MDCC (Λ'(α, β, x) y z))                 => return .some ⟨(MDCC (x ⟦α, β⟧(y, z))), .curr'⟩
  | MDCC (f x) => do
    match ← f.step?, ← x.step? with
    | .some ⟨f', h₁⟩, _ => return .some ⟨(MDCC (f' x)), .congrFun h₁⟩
    | _, .some ⟨x', h₁⟩ => return .some ⟨(MDCC (f x')), .congrArg h₁⟩
    | _, _ => pure .none
  | e => do
    Lean.Elab.Tactic.withMainContext do
      let lctx ← getLCtx
      lctx.findDeclM? (fun hyp => do
        match hyp.type with
        | .app (.app (.const ``_root_.Expr.RedAff []) e') b =>
          let _ ← Lean.Meta.isDefEq (← e.unify) e'
          return Option.some (Sigma.mk (MExpr.lean b)
            (RedAff'.lean hyp.value))
        | _ => return Option.none)

inductive RedAff'ReflTrans : MExpr → MExpr → Type where
  | refl  : RedAff'ReflTrans e e
  | trans : RedAff' A B → RedAff'ReflTrans B C → RedAff'ReflTrans A C

def reduce (e : MExpr) (gas : ℕ := 100000) : Lean.Elab.Tactic.TacticM ((e' : MExpr) ×  (RedAff'ReflTrans e e')) := do
  match gas with
  | .zero => return ⟨e, .refl⟩
  | .succ n =>
    match ← step? e with
    | .some ⟨e', h⟩ =>
      -- This hypothesis allows the recursion. Easy to prove.
      let ⟨e'', h₂⟩ ← e'.reduce n
      return ⟨e'', .trans h h₂⟩
    | .none => return ⟨e, .refl⟩

end MExpr

/-
Tactic to reduce hypotheses like Reduce a b into Reduce a (reduce b), except b is reduced to normal form.
-/
syntax "reduce_reduces'" term : tactic

elab "reduce_reduces" hyp:term : tactic => do
  let hyp := ← Lean.Meta.whnf (← ← Lean.Meta.reduceAll <$> Lean.Elab.Term.elabTerm hyp .none)
  let ty ← Lean.Meta.inferType hyp
  match ty with
  | Lean.Expr.app (Lean.Expr.app (.const ``Expr.Reduces []) α) β =>
    let some α ← checkTypeQ α q(_root_.Expr) | throwError s!"{β} is not an expr"
    let some β ← checkTypeQ β q(_root_.Expr) | throwError s!"{α} is not an expr"
    let some h := ← checkTypeQ hyp q(_root_.Expr.Reduces $α $β) | throwError s!"{hyp} is not a Reduces {α} {β}"
    let h' := q(_root_.Expr.Reduces.complete $h)
    sorry
  | _ => throwError s!"{ty} is not a Reduces A B"

end tactic
