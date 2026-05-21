import Dcc.Ast
import Dcc.Judge
import Lean

def decode_dcc (e : Lean.Expr) : Lean.Elab.Term.TermElabM _root_.Expr := do
  match e with
  | .app (.const ``_root_.Expr.sort []) m =>
    let some n ← (pure m.nat?) | throwError s!"unsupported: {m}"
    return .sort n
  | .const ``_root_.Expr.top [] =>
    return .top
  | .const ``_root_.Expr.bot [] =>
    return .bot
  | .const ``_root_.Expr.tintro [] =>
    return .tintro
  | .app (.const ``_root_.Expr.sndc []) β =>
    let β' ← decode_dcc β
    return .sndc β'
  | .app (.const ``_root_.Expr.fstc []) β =>
    let β' ← decode_dcc β
    return .fstc β'
  | .app (.const ``_root_.Expr.coup []) β =>
    let β' ← decode_dcc β
    return .coup β'
  | .app (.app (.const ``_root_.Expr.sigma []) α) β =>
    let α' ← decode_dcc α
    let β' ← decode_dcc β
    return .sigma α' β'
  | .app (.const ``_root_.Expr.id []) α =>
    let α' ← decode_dcc α
    return .id α'
  | .app (.app (.const ``_root_.Expr.comp []) f) g =>
    let f ← decode_dcc f
    let g ← decode_dcc g
    return .comp f g
  | .app (.app (.const ``_root_.Expr.pair []) f) g =>
    let f ← decode_dcc f
    let g ← decode_dcc g
    return .pair f g
  | .app (.app (.app (.const ``_root_.Expr.mk []) β) x) y =>
    let β ← decode_dcc β
    let x ← decode_dcc x
    let y ← decode_dcc y
    return .mk β x y
  | .app (.app (.const ``_root_.Expr.pi []) f_α) f_β =>
    let f_α ← decode_dcc f_α
    let f_β ← decode_dcc f_β
    return .pi f_α f_β
  | .app (.app (.app (.const ``_root_.Expr.curr []) α) β) x =>
    let α ← decode_dcc α
    let β ← decode_dcc β
    let x ← decode_dcc x
    return .curr α β x
  | .app (.app (.const ``_root_.Expr.quot []) β) x =>
    let β ← decode_dcc β
    let x ← decode_dcc x
    return .quot β x
  | .app (.app (.const ``_root_.Expr.app []) f) x =>
    let f ← decode_dcc f
    let x ← decode_dcc x
    return .app f x
  | e => throwError s!"unsupported: {e}"

syntax "dcc_trace" "?"? expr : command

elab "dcc_trace" err:"?"? e:expr : command => do
  for stx in Lean.Syntax.topDown e do
    match stx with
    | `(expr| ($_e)) => continue
    | stx =>
      try
        let stx' ← Lean.Elab.liftMacroM <| runDcc stx
        let e ← Lean.Elab.Command.liftTermElabM
          <| Lean.Elab.Term.withoutErrToSorry
            (Lean.Elab.Term.elabTermEnsuringType stx' (.some (.const ``_root_.Expr [])) >>= decode_dcc)
        match e.infer with
        | .some _ =>
          if err.isNone then
            let fmt := ((Std.format ∘ Sigma.fst) <$> e.infer).getD "?"
            Lean.logInfoAt stx m!"{stx}: {fmt}"
          else
            continue
        | _ => Lean.logInfoAt stx m!"{stx}: ?"
      catch _e =>
        continue

dcc_trace (Id(Sort 1) (Sort 1))
