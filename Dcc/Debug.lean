import Dcc.Ast
import Dcc.Judge
import Qq
import Lean

open Qq

def decode_dcc (e : Lean.Expr) : Lean.Elab.Term.TermElabM _root_.Expr := do
  match e with
  | .app (.const ``Expr.sort []) m =>
    let some n ← (pure m.nat?) | throwError s!"unsupported: {m}"
    return .sort n
  | .const ``Expr.top [] =>
    return .top
  | .const ``Expr.bot [] =>
    return .bot
  | .const ``Expr.tintro [] =>
    return .tintro
  | .app (.const ``Expr.fst []) β =>
    let β' ← decode_dcc β
    return .fst β'
  | .app (.const ``Expr.snd []) β =>
    let β' ← decode_dcc β
    return .snd β'
  | .app (.const ``Expr.sigma []) β =>
    let β' ← decode_dcc β
    return .sigma β'
  | .app (.const ``Expr.id []) α =>
    let α' ← decode_dcc α
    return .sigma α'
  | .app (.app (.const ``Expr.snd' []) α) β =>
    let α' ← decode_dcc α
    let β' ← decode_dcc β
    return .snd' α' β'
  | .app (.app (.const ``Expr.comp []) f) g =>
    let f ← decode_dcc f
    let g ← decode_dcc g
    return .comp f g
  | .app (.app (.const ``Expr.pair []) f) g =>
    let f ← decode_dcc f
    let g ← decode_dcc g
    return .pair f g
  | .app (.app (.app (.const ``Expr.mk []) β) x) y =>
    let β ← decode_dcc β
    let x ← decode_dcc x
    let y ← decode_dcc y
    return .mk β x y
  | .app (.app (.const ``Expr.pi []) f_α) f_β =>
    let f_α ← decode_dcc f_α
    let f_β ← decode_dcc f_β
    return .pi f_α f_β
  | .app (.app (.app (.const ``Expr.curr []) α) β) x =>
    let α ← decode_dcc α
    let β ← decode_dcc β
    let x ← decode_dcc x
    return .curr α β x
  | .app (.app (.const ``Expr.quot []) β) x =>
    let β ← decode_dcc β
    let x ← decode_dcc x
    return .quot β x
  | .app (.app (.const ``Expr.subst []) f_α) f =>
    let f_α ← decode_dcc f_α
    let f ← decode_dcc f
    return .subst f_α f
  | .app (.app (.const ``Expr.app []) f) x =>
    let f ← decode_dcc f
    let x ← decode_dcc x
    return .app f x
  | e => throwError s!"unsupported: {e}"

syntax "dcc_trace" term : command

elab "dcc_trace" e:term : command => do
  for stx in Lean.Syntax.topDown e do
    try
      let e ← Lean.Elab.Command.liftTermElabM
        (Lean.Elab.Term.elabTermEnsuringType stx (.some (.const ``_root_.Expr [])) >>= decode_dcc)
      let fmt := ((Std.format ∘ Sigma.fst) <$> e.infer).getD "?"
      Lean.logInfoAt stx fmt
    catch _e =>
      continue

dcc_trace (DCC ⊤)
