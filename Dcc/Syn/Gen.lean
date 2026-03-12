import Dcc.Syn.JudgePi
import Qq
import Lean
import Lean.Elab
import Mathlib.Data.List.Defs

open Lean (Level)

namespace gen

inductive MExpr where
  | Srt    : Level → MExpr
  | Pi     : Level → MExpr → MExpr → MExpr -- Pi (α : Syntax (Sort m)) (β : Sort n) : (Sort n)
  | K'     : Level → Level → MExpr
  | K      : Level → Level → MExpr
  | S      : Level → Level → Level → MExpr
  | I      : Level → MExpr
  | hole   : MExpr
  | next   : MExpr
  | read   : MExpr
  | assert : MExpr
  | app'   : MExpr
  | app    : MExpr  → MExpr → MExpr
   -- ONLY for tactics: Theorems are written in Expr, fvar for hypothesis automation
  | fvar   : Lean.FVarId → MExpr
  | lean_e : Lean.Expr → MExpr
deriving BEq, Repr, Lean.ToExpr

end gen

def Expr.toMeta : Expr → gen.MExpr
  | .I m => .I m
  | .K' m n => .K' m n
  | .K m n => .K m n
  | .S m n o => .S m n o
  | .app f x => .app f.toMeta x.toMeta
  | .app' => .app'
  | .assert => .assert
  | .read => .read
  | .next => .next
  | .hole => .hole
  | Expr.Pi m a b => .Pi m (toMeta a) (toMeta b)
  | .Srt m => .Srt m

namespace gen

open Lean Meta in unsafe def evalLevelUnsafe (e : Lean.Expr) : MetaM Level :=
  evalExpr Level (.const ``Lean.Level []) e

open Lean Meta in  @[implemented_by evalLevelUnsafe]
def evalLevelSafe (e : Lean.Expr) : MetaM Level :=
  throwError s!"not a valid sort: {repr e}"

open Qq Lean Elab Meta Tactic in def MExpr.decode (e : Lean.Expr) : Lean.Elab.TermElabM MExpr := do
  match e with
  | (.app (.app (.const `Expr.app []) f) x) => return .app (← decode f) (← decode x)
  | .app (.app (.app (.const ``Expr.Pi []) m) α) β => do
    let α' ← decode α
    let β' ← decode β
    let m ← evalLevelSafe m
    return .Pi m α' β'
  | .app (.const ``Expr.Srt []) m  => return .Srt (←  evalLevelSafe m)
  | (.app (.app (.const `Expr.K' []) m) n) => do
    return .K' (← evalLevelSafe m) (← evalLevelSafe n)
  | (.app (.app (.const `Expr.K []) m) n) => do
    return .K (← evalLevelSafe m) (← evalLevelSafe n)
  | (.app (.app (.app (.const `Expr.S []) m) n) o) => do
    return .S (← evalLevelSafe m) (← evalLevelSafe n) (← evalLevelSafe o)
  | (.app (.const `Expr.I []) m) => do
    return .I (← evalLevelSafe m)
  | .const `Expr.hole [] => return .hole
  | .const `Expr.next [] => return .next
  | .const `Expr.read [] => return .read
  | .const `Expr.assert [] => return .assert
  | .const `Expr.app' [] => return .app'
  | e => match (← getLCtx).findFVar? e with
    | .some decl => return .fvar decl.fvarId
    | .none => throwError s!"not supported: {repr e}"

open MExpr

inductive ParRed' : MExpr → MExpr → Type where
  | refl_fvar   : ParRed' (.fvar m) (.fvar m)
  | proof       : Lean.Expr → ParRed' e e'
  | refl_K'     : ParRed' (K' m n) (K' m n)
  | refl_K      : ParRed' (K m n) (K m n)
  | refl_S      : ParRed' (S m n o) (S m n o)
  | refl_I      : ParRed' (I m) (I m)
  | refl_hole   : ParRed' .hole .hole
  | refl_Srt    : ParRed' (Srt m) (Srt m)
  | refl_next   : ParRed' next next
  | refl_read   : ParRed' read read
  | refl_assert : ParRed' assert assert
  | refl_app'   : ParRed' .app' .app'
  | I           : ParRed' x x' → ParRed' (((I _m).app _α).app x) x'
  | K           : ParRed' x x' → ParRed' (((((K _m _n).app _α).app _β).app x).app _y) x'
  | K'          : ParRed' x x' → ParRed' (((((K' _m _n).app _α).app _β).app x).app _y) x'
  | S           : ParRed' x x' → ParRed' y y' → ParRed' z z'
    → ParRed' (((((((S _m _n _o).app _α).app _β).app _γ).app x).app y).app z) ((x'.app z').app (y'.app z'))
  | Pi          : ParRed' α α' → ParRed' β β' → ParRed' x x'
    → ParRed' ((MExpr.Pi m α β).app x) (.Pi m (α'.app x') (β'.app x'))
  | Pival       : ParRed' α α' → ParRed' β β' → ParRed' (MExpr.Pi m α β) (MExpr.Pi m α' β')
  | next        : ParRed' f f' → ParRed' ((next.app f).app _x) f'
  | read        : ParRed' e e' → ParRed' (read.app e) e'
  | assert      : ParRed' e e' → ParRed' ((assert.app e).app _x) e'
  | app'        : ParRed' f f' → ParRed' g g' → ParRed' x x'
    → ParRed' ((((MExpr.app'.app π).app f).app g).app x) ((MExpr.app π (f'.app x')).app (g'.app x'))
  | app         : ParRed' f f'
    → ParRed' x x'
    → ParRed' (f.app x) (f'.app x')
deriving Repr

syntax "*⸨" term* "⸩" : term

macro_rules
  | `(*⸨$f:term $x:term⸩) => `(MExpr.app $f:term $x:term)
  | `(*⸨$f:term $x:term $xs:term*⸩) => `(*⸨*⸨$f:term $x:term⸩ $xs:term*⸩)

open Qq Lean Meta Elab Tactic in def try_first_hyp (pred : Lean.Name) (on_e : FVarId) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let goal ← getMainGoal
  goal.withContext do
    let lctx ← getLCtx

    let mut proof : Option (Lean.Expr × Lean.Expr) := Option.none

    for hyp in lctx do
      match hyp.type with
      | Lean.Expr.app (Lean.Expr.app b (Lean.Expr.fvar e')) _t  =>
        if b == (Lean.Expr.const pred []) ∧ e' == on_e then
          proof := .some ⟨hyp.type, (Lean.Expr.fvar hyp.fvarId)⟩
        else continue
      | _ => continue
    return proof

-- TODO: Use Lean.TacticM to look up potential reduction for fvar
open Lean Elab Tactic in def reduce (e : MExpr) : TacticM ((e' : MExpr) × (ParRed' e e')) :=
  match e with
  | .lean_e e => throwError s!"not supported: {repr e}"
  | .fvar v => do
    let p? := (← try_first_hyp (``ParRed) v)
    match p? with
    | .some ⟨.app (.app (.const ``ParRed []) _ety) e', proof⟩ =>
      return ⟨.lean_e e', .proof proof (e := .fvar v) (e' := .lean_e e')⟩
    | _ => throwError "no matching hypothesis"
  | MExpr.app (.app (.I _m) _α) x => do
    let ⟨x', h⟩ ← reduce x
    return ⟨x', .I h⟩
  | *⸨(.K _m _n) _α _β x _y⸩ => do
    let ⟨x', h⟩ ← reduce x
    return ⟨x', .K h⟩
  | *⸨(.K' _m _n) _α _β x _y⸩ => do
    let ⟨x', h⟩ ← reduce x
    return ⟨x', .K' h⟩
  | *⸨(.S _m _n _o) _α _β _γ x y z⸩ => do
    let ⟨x', h₁⟩ ← reduce x
    let ⟨y', h₂⟩ ← reduce y
    let ⟨z', h₃⟩ ← reduce z
    return ⟨((x'.app z').app (y'.app z')), .S h₁ h₂ h₃⟩
  | *⸨(.Pi m α β) x⸩ => do
    let ⟨α', h₁⟩ ← reduce α
    let ⟨β', h₂⟩ ← reduce β
    let ⟨x', h₃⟩ ← reduce x
    return ⟨MExpr.Pi m (α'.app x') (β'.app x'), .Pi h₁ h₂ h₃⟩
  | (.Pi m α β) => do
    let ⟨α', h₁⟩ ← reduce α
    let ⟨β', h₂⟩ ← reduce β
    return ⟨MExpr.Pi m α' β', .Pival h₁ h₂⟩
  | *⸨.next f _x⸩ => do
    let ⟨f', h₁⟩ ← reduce f
    return ⟨f', .next h₁⟩
  | *⸨.read e⸩ => do
    let ⟨e', h₁⟩ ← reduce e
    return ⟨e', .read h₁⟩
  | *⸨.assert f _x⸩ => do
    let ⟨f', h₁⟩ ← reduce f
    return ⟨f', .assert h₁⟩
  | *⸨.app' π f g x⸩ => do
    let ⟨f', h₁⟩ ← reduce f
    let ⟨g', h₂⟩ ← reduce g
    let ⟨x', h₃⟩ ← reduce x
    return ⟨(MExpr.app π (f'.app x')).app (g'.app x'), .app' h₁ h₂ h₃⟩
  | *⸨f x⸩ => do
    let ⟨f', h₁⟩ ← reduce f
    let ⟨x', h₂⟩ ← reduce x

    return ⟨f'.app x', .app h₁ h₂⟩
  | .K' m n => return ⟨K' m n, .refl_K'⟩
  | .K m n => return ⟨K m n, .refl_K⟩
  | .S m n o => return ⟨S m n o, .refl_S⟩
  | .I m => return ⟨I m, .refl_I⟩
  | .Srt m => return ⟨Srt m, .refl_Srt⟩
  | .next => return ⟨.next, .refl_next⟩
  | .read => return ⟨.read, .refl_read⟩
  | .assert => return ⟨.assert, .refl_assert⟩
  | .app'   => return ⟨.app', .refl_app'⟩
  | .hole   => return ⟨.hole, .refl_hole⟩

open Lean Elab Tactic Qq in def MExpr.unify (e : MExpr) : TacticM Q(_root_.Expr) := do
  match e with
  | .lean_e e => pure e
  | .fvar v =>
    let l ← getLCtx
    match l.find? v with
    | .some v => return (.fvar v.fvarId)
    | .none => throwError s!"not supported"
  | .K m n => pure q(Expr.K $m $n)
  | .Srt m => pure q(Expr.Srt $m)
  | .Pi m α β =>
    let α' : Q(_root_.Expr) := ← α.unify
    let β' : Q(_root_.Expr) := ← β.unify
    pure q(Expr.Pi $m $α' $β')
  | .K' m n => pure q(Expr.K' $m $n)
  | .S m n o => pure q(Expr.S $m $n $o)
  | .I m  => pure q(Expr.I $m)
  | .hole => pure q(Expr.hole)
  | .next => pure q(Expr.next)
  | .read => pure q(Expr.read)
  | .assert => pure q(Expr.assert)
  | .app' => pure q(Expr.app')
  | .app f x => do
    let f : Q(_root_.Expr) ← f.unify
    let x : Q(_root_.Expr) ← x.unify
    return q(Expr.app $f $x)

end gen

open gen Lean Elab Tactic Qq in def gen_par_red_proof (p : ParRed' e e') : Lean.Elab.Tactic.TacticM Lean.Expr :=
  match p with
  | @ParRed'.proof _ _ p      => return p
  | @ParRed'.refl_fvar m      => return ((Lean.Expr.const ``rfl [1]).app (.const ``_root_.Expr []))
  | @ParRed'.refl_K' m n      => return q(@ParRed.refl_K' $m $n)
  | @ParRed'.refl_K m n       => return q(@ParRed.refl_K $m $n)
  | @ParRed'.refl_S m n o     => return q(@ParRed.refl_S $m $n $o)
  | @ParRed'.refl_I m         => return q(@ParRed.refl_I $m)
  | @ParRed'.refl_hole        => return q(@ParRed.refl_hole)
  | @ParRed'.refl_Srt m       => return q(@ParRed.refl_Srt $m)
  | @ParRed'.refl_next        => return q(@ParRed.refl_next)
  | @ParRed'.refl_read        => return q(@ParRed.refl_read)
  | @ParRed'.refl_assert      => return q(@ParRed.refl_assert)
  | @ParRed'.refl_app'        => return q(@ParRed.refl_app')
  | @ParRed'.I x x' m α h     => do
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let α : Q(_root_.Expr)  ← α.unify
    let inner : Q(ParRed $x $x') ← gen_par_red_proof h
    return q(@ParRed.I $x $x' $m $α $inner)
  | @ParRed'.K x x' m n α β y h => do
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let α : Q(_root_.Expr) ← α.unify
    let β : Q(_root_.Expr) ← β.unify
    let y : Q(_root_.Expr) ← y.unify
    let inner : Q(ParRed $x $x') ← gen_par_red_proof h
    return q(@ParRed.K $x $x' $m $n $α $β $y $inner)
  | @ParRed'.K' x x' m n α β y h => do
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let α : Q(_root_.Expr) ← α.unify
    let β : Q(_root_.Expr) ← β.unify
    let y : Q(_root_.Expr) ← y.unify
    let inner : Q(ParRed $x $x') ← gen_par_red_proof h
    return q(@ParRed.K' $x $x' $m $n $α $β $y $inner)
  | @ParRed'.S x x' y y' z z' m n o α β γ hx hy hz => do
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let y : Q(_root_.Expr) ← y.unify
    let y' : Q(_root_.Expr) ← y'.unify
    let z : Q(_root_.Expr) ← z.unify
    let z' : Q(_root_.Expr) ← z'.unify
    let α : Q(_root_.Expr) ← α.unify
    let β : Q(_root_.Expr) ← β.unify
    let γ : Q(_root_.Expr) ← γ.unify
    let hx' : Q(ParRed $x $x') ← gen_par_red_proof hx
    let hy' : Q(ParRed $y $y') ← gen_par_red_proof hy
    let hz' : Q(ParRed $z $z') ← gen_par_red_proof hz

    return q(@ParRed.S $x $x' $y $y' $z $z' $m $n $o $α $β $γ $hx' $hy' $hz')
  | @ParRed'.Pi α α' β β' x x' m h_α h_β h_x => do
    let α : Q(_root_.Expr) ← α.unify
    let α' : Q(_root_.Expr) ← α'.unify
    let β' : Q(_root_.Expr) ← β'.unify
    let β : Q(_root_.Expr) ← β.unify
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let hx' : Q(ParRed $α $α') ←  gen_par_red_proof h_α
    let hy' : Q(ParRed $β $β') ←  gen_par_red_proof h_β
    let hz' : Q(ParRed $x $x') ←  gen_par_red_proof h_x

    return q(@ParRed.Pi $α $α' $β $β' $x $x' $m $hx' $hy' $hz')
  | @ParRed'.Pival α α' β β' m h_α h_β => do
    let α : Q(_root_.Expr) ← α.unify
    let α' : Q(_root_.Expr) ← α'.unify
    let β' : Q(_root_.Expr) ← β'.unify
    let β : Q(_root_.Expr) ← β.unify
    let hx' : Q(ParRed $α $α') ← gen_par_red_proof h_α
    let hy' : Q(ParRed $β $β') ← gen_par_red_proof h_β
    return q(@ParRed.Pival $α $α' $β $β' $m $hx' $hy')
  | @ParRed'.next f f' x hf   => do
    let f : Q(_root_.Expr) ← f.unify
    let f' : Q(_root_.Expr) ← f'.unify
    let x : Q(_root_.Expr) ← x.unify
    let hf : Q(ParRed $f $f') ← gen_par_red_proof hf
    return q(@ParRed.next $f $f' $x $hf)
  | @ParRed'.read e e' he     => do
    let e : Q(_root_.Expr) ← e.unify
    let e' : Q(_root_.Expr) ← e'.unify
    let he : Q(ParRed $e $e') ← gen_par_red_proof he
    return q(@ParRed.read $e $e' $he)
  | @ParRed'.assert e e' x he => do
    let e : Q(_root_.Expr) ← e.unify
    let e' : Q(_root_.Expr) ← e'.unify
    let x : Q(_root_.Expr) ← x.unify
    let he : Q(ParRed $e $e') ← gen_par_red_proof he
    return q(@ParRed.assert $e $e' $x $he)
  | @ParRed'.app' f f' g g' x x' π h_f h_g h_x => do
    let f : Q(_root_.Expr) ← f.unify
    let f' : Q(_root_.Expr) ← f'.unify
    let g : Q(_root_.Expr) ← g.unify
    let g' : Q(_root_.Expr) ← g'.unify
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let π : Q(_root_.Expr) ← π.unify
    let h_f : Q(ParRed $f $f') ← gen_par_red_proof h_f
    let h_g : Q(ParRed $g $g') ← gen_par_red_proof h_g
    let h_x : Q(ParRed $x $x') ← gen_par_red_proof h_x
    return q(@ParRed.app' $f $f' $g $g' $x $x' $π $h_f $h_g $h_x)
  | @ParRed'.app f f' x x' h_f h_x => do
    let f : Q(_root_.Expr) ← f.unify
    let f' : Q(_root_.Expr) ← f'.unify
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let h_f : Q(ParRed $f $f') ← gen_par_red_proof h_f
    let h_x : Q(ParRed $x $x') ← gen_par_red_proof h_x
    return q(@ParRed.app $f $f' $x $x' $h_f $h_x)

syntax "decide_red" : tactic

open gen Lean Meta Elab Tactic in elab "decide_red" : tactic => do
  let goal ← getMainGoal
  let goalType := ← whnf (← Lean.Meta.reduceAll (← goal.getType))
  match goalType with
  | Lean.Expr.app (.app (.const ``ParRed []) x) _x' =>
    let tgt_term ← whnf (← Lean.Meta.reduceAll x)
    let e ← MExpr.decode tgt_term
    let ⟨_, proof⟩ ← reduce e
    let expr ← gen_par_red_proof proof
    goal.assign (← whnf (← Lean.Meta.reduceAll expr))
  | _ => throwError "unsupported"

namespace examples

open Expr

example : ParRed ⸨(K 2 2) (Srt 1) (Srt 1) (Srt 0) (Srt 0)⸩ (Srt 0) := by
  decide_red

example (h : ParRed e (Srt 0)) : ParRed ⸨(K 2 2) (Srt 1) (Srt 1) e (Srt 0)⸩ (Srt 0) := by
  decide_red

end examples
