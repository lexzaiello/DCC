import Dcc.Ast
import Dcc.Judge
import Dcc.Judge2

deriving instance DecidableEq for Lean.Name
deriving instance DecidableEq for Lean.FVarId

#check GenericExpr

-- This is for the compiler. I'm fine with this being conservative.

def decode_dcc (e : Lean.Expr) : Lean.Elab.Term.TermElabM (GenericExpr (τ := Lean.FVarId)) := do
  match e with
  | .app (.app (.const ``_root_.GenericExpr.fmap _us) _α) x =>
    let x' ← decode_dcc x
    return .fmap x'
  | .app (.app (.const ``_root_.GenericExpr.sort _us) _α) m =>
    let some n ← (pure m.nat?) | throwError s!"unsupported: {m}"
    return .sort n
  | .app (.const ``_root_.GenericExpr.top _us) _α =>
    return .top
  | .app (.const ``_root_.GenericExpr.bot _us) _α =>
    return .bot
  | .app (.const ``_root_.GenericExpr.tintro _us) _α =>
    return .tintro
  | .app (.app (.const ``_root_.GenericExpr.sndc _us) _α) β =>
    let β' ← decode_dcc β
    return .sndc β'
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.eval _us) _α) α) β) x =>
    let α' ← decode_dcc α
    let β' ← decode_dcc β
    let x' ← decode_dcc x
    return .eval α' β' x'
  | .app (.app (.const ``_root_.GenericExpr.fstc _us) _α) β =>
    let β' ← decode_dcc β
    return .fstc β'
  | .app (.app (.const ``_root_.GenericExpr.coup _us) _α) β =>
    let β' ← decode_dcc β
    return .coup β'
  | .app (.app (.app (.const ``_root_.GenericExpr.sigma _us) _α) α) β =>
    let α' ← decode_dcc α
    let β' ← decode_dcc β
    return .sigma α' β'
  | .app (.app (.const ``_root_.GenericExpr.id _us) _α) α =>
    let α' ← decode_dcc α
    return .id α'
  | .app (.app (.app (.const ``_root_.GenericExpr.comp _us) _α) f) g =>
    let f ← decode_dcc f
    let g ← decode_dcc g
    return .comp f g
  | .app (.app (.app (.const ``_root_.GenericExpr.comp' _us) _α) f) g =>
    let f ← decode_dcc f
    let g ← decode_dcc g
    return .comp' f g
  | .app (.app (.app (.const ``_root_.GenericExpr.comp₂ _us) _α) f) g =>
    let f ← decode_dcc f
    let g ← decode_dcc g
    return .comp₂ f g
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.pair _us) _α) β) f) g =>
    let β ← decode_dcc β
    let f ← decode_dcc f
    let g ← decode_dcc g
    return .pair β f g
  | .app (.app (.const ``_root_.GenericExpr.refl _us) _α) f_α =>
    let f_α' ← decode_dcc f_α
    return .refl f_α'
  | .app (.app (.const ``_root_.GenericExpr.eql _us) _α) f_α =>
    let f_α' ← decode_dcc f_α
    return .eql f_α'
  | .app (.app (.app (.const ``_root_.GenericExpr.eq _us) x) _α) y =>
    let x' ← decode_dcc x
    let y' ← decode_dcc y
    return .eq x' y'
  | .app (.app (.const ``_root_.GenericExpr.bang _us) _α) x =>
    let x ← decode_dcc x
    return .bang x
  | .app (.app (.const ``_root_.GenericExpr.unbox _us) _α) x =>
    let x ← decode_dcc x
    return .unbox x
  | .app (.app (.const ``_root_.GenericExpr.box _us) _α) x =>
    let x ← decode_dcc x
    return .box x
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.mkc _us) _α) β) x) y =>
    let β ← decode_dcc β
    let x ← decode_dcc x
    let y ← decode_dcc y
    return .mkc β x y
  | .app (.app (.app (.const ``_root_.GenericExpr.pi _us) _α) f_α) f_β =>
    let f_α ← decode_dcc f_α
    let f_β ← decode_dcc f_β
    return .pi f_α f_β
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.curr _us) _α) α) β) x =>
    let α ← decode_dcc α
    let β ← decode_dcc β
    let x ← decode_dcc x
    return .curr α β x
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.curr' _us) _α) α) β) x =>
    let α ← decode_dcc α
    let β ← decode_dcc β
    let x ← decode_dcc x
    return .curr' α β x
  | .app (.app (.app (.const ``_root_.GenericExpr.quot _us) _α) β) x =>
    let β ← decode_dcc β
    let x ← decode_dcc x
    return .quot β x
  | .app (.app (.app (.const ``_root_.GenericExpr.app _us) _α) f) x =>
    let f ← decode_dcc f
    let x ← decode_dcc x
    return .app f x
  | .fvar fv => pure (.const fv)
  | e => throwError m!"unsupported: {e}"

def decode_dcc' (e : Lean.Expr) : Lean.Elab.Term.TermElabM (GenericExpr (τ := Unit)) := do
  match e with
  | .app (.app (.const ``_root_.GenericExpr.fmap _us) _α) x =>
    let x' ← decode_dcc' x
    return .fmap x'
  | .app (.app (.const ``_root_.GenericExpr.sort _us) _α) m =>
    let some n ← (pure m.nat?) | throwError s!"unsupported: {m}"
    return .sort n
  | .app (.const ``_root_.GenericExpr.top _us) _α =>
    return .top
  | .app (.const ``_root_.GenericExpr.bot _us) _α =>
    return .bot
  | .app (.const ``_root_.GenericExpr.tintro _us) _α =>
    return .tintro
  | .app (.app (.const ``_root_.GenericExpr.sndc _us) _α) β =>
    let β' ← decode_dcc' β
    return .sndc β'
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.eval _us) _α) α) β) x =>
    let α' ← decode_dcc' α
    let β' ← decode_dcc' β
    let x' ← decode_dcc' x
    return .eval α' β' x'
  | .app (.app (.const ``_root_.GenericExpr.fstc _us) _α) β =>
    let β' ← decode_dcc' β
    return .fstc β'
  | .app (.app (.const ``_root_.GenericExpr.coup _us) _α) β =>
    let β' ← decode_dcc' β
    return .coup β'
  | .app (.app (.app (.const ``_root_.GenericExpr.sigma _us) _α) α) β =>
    let α' ← decode_dcc' α
    let β' ← decode_dcc' β
    return .sigma α' β'
  | .app (.app (.const ``_root_.GenericExpr.id _us) _α) α =>
    let α' ← decode_dcc' α
    return .id α'
  | .app (.app (.app (.const ``_root_.GenericExpr.comp _us) _α) f) g =>
    let f ← decode_dcc' f
    let g ← decode_dcc' g
    return .comp f g
  | .app (.app (.app (.const ``_root_.GenericExpr.comp' _us) _α) f) g =>
    let f ← decode_dcc' f
    let g ← decode_dcc' g
    return .comp' f g
  | .app (.app (.app (.const ``_root_.GenericExpr.comp₂ _us) _α) f) g =>
    let f ← decode_dcc' f
    let g ← decode_dcc' g
    return .comp₂ f g
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.pair _us) _α) β) f) g =>
    let β ← decode_dcc' β
    let f ← decode_dcc' f
    let g ← decode_dcc' g
    return .pair β f g
  | .app (.app (.const ``_root_.GenericExpr.refl _us) _α) f_α =>
    let f_α' ← decode_dcc' f_α
    return .refl f_α'
  | .app (.app (.const ``_root_.GenericExpr.eql _us) _α) f_α =>
    let f_α' ← decode_dcc' f_α
    return .eql f_α'
  | .app (.app (.app (.const ``_root_.GenericExpr.eq _us) x) _α) y =>
    let x' ← decode_dcc' x
    let y' ← decode_dcc' y
    return .eq x' y'
  | .app (.app (.const ``_root_.GenericExpr.bang _us) _α) x =>
    let x ← decode_dcc' x
    return .bang x
  | .app (.app (.const ``_root_.GenericExpr.unbox _us) _α) x =>
    let x ← decode_dcc' x
    return .unbox x
  | .app (.app (.const ``_root_.GenericExpr.box _us) _α) x =>
    let x ← decode_dcc' x
    return .box x
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.mkc _us) _α) β) x) y =>
    let β ← decode_dcc' β
    let x ← decode_dcc' x
    let y ← decode_dcc' y
    return .mkc β x y
  | .app (.app (.app (.const ``_root_.GenericExpr.pi _us) _α) f_α) f_β =>
    let f_α ← decode_dcc' f_α
    let f_β ← decode_dcc' f_β
    return .pi f_α f_β
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.curr _us) _α) α) β) x =>
    let α ← decode_dcc' α
    let β ← decode_dcc' β
    let x ← decode_dcc' x
    return .curr α β x
  | .app (.app (.app (.app (.const ``_root_.GenericExpr.curr' _us) _α) α) β) x =>
    let α ← decode_dcc' α
    let β ← decode_dcc' β
    let x ← decode_dcc' x
    return .curr' α β x
  | .app (.app (.app (.const ``_root_.GenericExpr.quot _us) _α) β) x =>
    let β ← decode_dcc' β
    let x ← decode_dcc' x
    return .quot β x
  | .app (.app (.app (.const ``_root_.GenericExpr.app _us) _α) f) x =>
    let f ← decode_dcc' f
    let x ← decode_dcc' x
    return .app f x
  | e => throwError m!"unsupported: {e}"

syntax "dcc_trace" "?"? gen_dcc : command
syntax "dcc_trace'" "?"? gen_dcc : command

elab "dcc_trace" err:"?"? e:gen_dcc : command => do
  for stx in Lean.Syntax.topDown e do
    match stx with
    | `(gen_dcc| ($_e)) => continue
    | stx =>
      try
        let stx' ← Lean.Elab.liftMacroM <| runDcc stx
        let e ← Lean.Elab.Command.liftTermElabM
          <| Lean.Elab.Term.withoutErrToSorry
            (Lean.Elab.Term.elabTerm stx' .none >>= decode_dcc')
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

elab "dcc_trace'" err:"?"? e:gen_dcc : command => do
  let mut logs : Array (Lean.Syntax × Lean.MessageData) := #[]
  for stx in Lean.Syntax.topDown e do
    match stx with
    | `(gen_dcc| ($_e)) => continue
    | stx =>
      try
        let stx' ← Lean.Elab.liftMacroM <| runDcc stx
        let e ← Lean.Elab.Command.liftTermElabM
          <| Lean.Elab.Term.withoutErrToSorry
            (Lean.Elab.Term.elabTerm stx' .none >>= decode_dcc)
        match e.infer₂ with
        | .some _ =>
          if err.isNone then
            let fmt := ((Std.format ∘ Sigma.fst) <$> e.infer₂).getD "?"
            logs := logs.push (stx, m!"{stx}: {fmt}")
          else
            continue
        | _ =>
          logs := logs.push (stx, m!"{stx}: ?")
      catch _e =>
        continue
  let logs' := logs.mergeSort (fun (e₁, _) (e₂, _) => (toString e₁).length < (toString e₂).length)
  for (stx, msg) in logs' do
    Lean.logInfoAt stx msg

dcc_trace (Id(Sort 1) (Sort 1))
