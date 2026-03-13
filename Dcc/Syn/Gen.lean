import Dcc.Syn.JudgePi
import Qq
import Lean
import Dcc.Syn.Reduce'
import Lean.Elab
import Mathlib.Data.List.Defs

namespace gen

open Qq

abbrev Level := Lean.Expr

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
deriving BEq, Repr

end gen

/-def Expr.toMeta : Expr → gen.MExpr
  | .I m => .I (Lean.toExpr m)
  | .K' m n => .K' (Lean.toExpr m) (Lean.toExpr n)
  | .K m n => .K (Lean.toExpr m) (Lean.toExpr n)
  | .S m n o => .S (Lean.toExpr m) (Lean.toExpr n) (Lean.toExpr o)
  | .app f x => .app f.toMeta x.toMeta
  | .app' => .app'
  | .assert => .assert
  | .read => .read
  | .next => .next
  | .hole => .hole
  | Expr.Pi m a b => .Pi (Lean.toExpr m) (toMeta a) (toMeta b)
  | .Srt m => .Srt (Lean.toExpr m)-/

namespace gen

open Qq Lean Elab Meta Tactic in def MExpr.decode (e : Lean.Expr) : Lean.Elab.TermElabM MExpr := do
  match e with
  | (.app (.app (.const `Expr.app []) f) x) => return .app (← decode f) (← decode x)
  | .app (.app (.app (.const ``Expr.Pi []) m) α) β => do
    let α' ← decode α
    let β' ← decode β
    return .Pi m α' β'
  | .app (.const ``Expr.Srt []) m  => return .Srt m
  | (.app (.app (.const `Expr.K' []) m) n) => do
    return .K' m n
  | (.app (.app (.const `Expr.K []) m) n) => do
    return .K m n
  | (.app (.app (.app (.const `Expr.S []) m) n) o) => do
    return .S m n o
  | (.app (.const `Expr.I []) m) => do
    return .I m
  | .const `Expr.hole [] => return .hole
  | .const `Expr.next [] => return .next
  | .const `Expr.read [] => return .read
  | .const `Expr.assert [] => return .assert
  | .const `Expr.app' [] => return .app'
  | .fvar v => return .fvar v
  | e => return .lean_e e

open MExpr

inductive ParRed' : MExpr → MExpr → Type where
  | parred_refl : ParRed' e e₂
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

open Qq Lean Meta Elab Tactic in def try_first_hyp (matcher : Lean.Expr → Bool) : TacticM (Option (Lean.Expr × Lean.Expr)) := do
  let goal ← getMainGoal
  goal.withContext do
    let lctx ← getLCtx

    let match_hyp := (lctx.decls.toList.reverse.filterMap id).find? (matcher ∘ (·.type))
    return match_hyp.map (fun hyp => ⟨hyp.type, (Lean.Expr.fvar hyp.fvarId)⟩)

open Lean Elab Tactic in def reduce.matcher (on_e : FVarId) (hyp_type : Lean.Expr) : Bool :=
  match hyp_type with
  | Lean.Expr.app (Lean.Expr.app b (Lean.Expr.fvar e')) _t  =>
    b == (Lean.Expr.const ``ParRed []) ∧ e' == on_e
  | _ => false


open Lean Elab Tactic Qq in def MExpr.unify (e : MExpr) : TacticM Q(_root_.Expr) := do
  match e with
  | .lean_e e => pure e
  | .fvar v =>
    withMainContext do
      let l ← getLCtx
      match l.find? v with
      | .some v => return v.value?.getD (.fvar v.fvarId)
      | .none => throwError s!"not supported"
  | .K m n =>
    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
    pure q(Expr.K $m $n)
  | .Srt m =>
    let m : Q(ℕ) := m
    pure q(Expr.Srt $m)
  | .Pi m α β =>
    let m : Q(ℕ) := m
    let α' : Q(_root_.Expr) := ← α.unify
    let β' : Q(_root_.Expr) := ← β.unify
    pure q(Expr.Pi $m $α' $β')
  | .K' m n =>
    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
    pure q(Expr.K' $m $n)
  | .S m n o =>
    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
    let o : Q(ℕ) := o
    pure q(Expr.S $m $n $o)
  | .I m  =>
    let m : Q(ℕ) := m
    pure q(Expr.I $m)
  | .hole => pure q(Expr.hole)
  | .next => pure q(Expr.next)
  | .read => pure q(Expr.read)
  | .assert => pure q(Expr.assert)
  | .app' => pure q(Expr.app')
  | .app f x => do
    let f : Q(_root_.Expr) ← f.unify
    let x : Q(_root_.Expr) ← x.unify
    return q(Expr.app $f $x)

-- TODO: Use Lean.TacticM to look up potential reduction for fvar
open Lean Elab Tactic in def reduce (e : MExpr) : TacticM ((e' : MExpr) × (ParRed' e e')) :=
  match e with
  | .lean_e e => return ⟨.lean_e e, ParRed'.parred_refl⟩
  | .fvar v => do
    let p? := (← try_first_hyp (reduce.matcher v))
    match p? with
    | .some ⟨.app (.app (.const ``ParRed []) _ety) e', proof⟩ =>
      let e' ← MExpr.decode e'
      return ⟨e', .proof proof (e := .fvar v) (e' := e')⟩
    | _ => return ⟨(.fvar v), ParRed'.parred_refl (e := .fvar v)⟩
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

end gen

open gen Lean Elab Tactic Qq in def gen_par_red_proof (p : ParRed' e e') : Lean.Elab.Tactic.TacticM Lean.Expr :=
  match p with
  | @ParRed'.parred_refl x x' => do
    let x : Q(_root_.Expr) ← x.unify
    return q(@ParRed.refl $x)
  | @ParRed'.proof _ _ p      => return p
  | @ParRed'.refl_fvar m      => return ((Lean.Expr.const ``rfl [1]).app (.const ``_root_.Expr []))
  | @ParRed'.refl_K' m n      =>
    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
    return q(@ParRed.refl_K' $m $n)
  | @ParRed'.refl_K m n       =>
    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
    return q(@ParRed.refl_K $m $n)
  | @ParRed'.refl_S m n o     =>
    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
    let o : Q(ℕ) := o
    return q(@ParRed.refl_S $m $n $o)
  | @ParRed'.refl_I m         =>
    let m : Q(ℕ) := m
    return q(@ParRed.refl_I $m)
  | @ParRed'.refl_hole        => return q(@ParRed.refl_hole)
  | @ParRed'.refl_Srt m       =>
    let m : Q(ℕ) := m
    return q(@ParRed.refl_Srt $m)
  | @ParRed'.refl_next        => return q(@ParRed.refl_next)
  | @ParRed'.refl_read        => return q(@ParRed.refl_read)
  | @ParRed'.refl_assert      => return q(@ParRed.refl_assert)
  | @ParRed'.refl_app'        => return q(@ParRed.refl_app')
  | @ParRed'.I x x' m α h     => do
    let m : Q(ℕ) := m
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let α : Q(_root_.Expr)  ← α.unify
    let inner : Q(ParRed $x $x') ← gen_par_red_proof h
    return q(@ParRed.I $x $x' $m $α $inner)
  | @ParRed'.K x x' m n α β y h => do
    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
    let x : Q(_root_.Expr) ← x.unify
    let x' : Q(_root_.Expr) ← x'.unify
    let α : Q(_root_.Expr) ← α.unify
    let β : Q(_root_.Expr) ← β.unify
    let y : Q(_root_.Expr) ← y.unify
    let inner : Q(ParRed $x $x') ← gen_par_red_proof h
    return q(@ParRed.K $x $x' $m $n $α $β $y $inner)
  | @ParRed'.K' x x' m n α β y h => do
    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
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

    let m : Q(ℕ) := m
    let n : Q(ℕ) := n
    let o : Q(ℕ) := o

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

    let m : Q(ℕ) := m

    return q(@ParRed.Pi $α $α' $β $β' $x $x' $m $hx' $hy' $hz')
  | @ParRed'.Pival α α' β β' m h_α h_β => do
    let α : Q(_root_.Expr) ← α.unify
    let α' : Q(_root_.Expr) ← α'.unify
    let β' : Q(_root_.Expr) ← β'.unify
    let β : Q(_root_.Expr) ← β.unify
    let hx' : Q(ParRed $α $α') ← gen_par_red_proof h_α
    let hy' : Q(ParRed $β $β') ← gen_par_red_proof h_β
    let m : Q(ℕ) := m
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
    if ← isTypeCorrect expr then
      goal.assign (← whnf (← Lean.Meta.reduceAll expr))
    else
      throwError "couldn't solve"
  | _ => throwError "unsupported"

namespace examples

open Expr

example : ParRed ⸨(K 2 2) (Srt 1) (Srt 1) (Srt 0) (Srt 0)⸩ (Srt 0) := by
  decide_red

example (h : ParRed e (Srt 0)) : ParRed ⸨(K 2 2) (Srt 1) (Srt 1) e (Srt 0)⸩ (Srt 0) := by
  decide_red

end examples

syntax "exists_red" : tactic

open Qq gen Lean Meta Elab Tactic in elab "exists_red" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let tgt ← getMainTarget
    let tgt : Option Q(Prop) ← Qq.checkTypeQ tgt q(Prop)
    match tgt with
    | .some ~q(∃ d, ParRed $xe d) =>
      match ← checkTypeQ xe q(_root_.Expr) with
      | .some x' =>
        let m ← MExpr.decode xe
        let r ← reduce m

        let d : Q(_root_.Expr) ← r.fst.unify
        let p : Q(ParRed $x' $d) ← gen_par_red_proof r.snd

        let proof := q(Exists.intro $d $p)

        if ← isTypeCorrect proof then
          goal.assign proof
        else
          throwError "couldn't solve"
      | .none => throwError s!"not a valid Expr: {repr xe}"
    | e => throwError s!"not a ParRed existential: {repr e}"

open Expr in example : ∃ e', ParRed ⸨(I 2) (Srt 1) (Srt 0)⸩ e' := by
  exists_red

/-
Closes conversion goals like "∃ e', ParRed A x ∧ ParRed B x" by:
1. decide_red on A and B
2. check if fst == and close with ∧ + ∃ if so
-/

open Expr Qq gen Lean Meta Elab Tactic in def contains_spine (e : Lean.Expr) : MetaM Bool := do
  match ← checkTypeQ e q(_root_.Expr) with
  | .some e' =>
    match e with
    | .app (.app (.const ``_root_.Expr.app []) f) _x => contains_spine f
    | _ => match e' with
      | ~q((K' $m $n)) => pure true
      | ~q((K $m $n)) => pure true
      | ~q((S $m $n $o)) => pure true
      | ~q(I $m) => pure true
      | ~q(S $m $n $o) => pure true
      | ~q(Pi $m $α $β) => pure true
      | ~q(next) => pure true
      | ~q(read) => pure true
      | ~q(assert) => pure true
      | ~q(app') => pure true
      | ~q(hole) => pure true
      | ~q(Srt $m) => pure true
      | _ => pure false
  | _ => pure false

syntax "cases_spine" : tactic

open Qq Lean Meta Elab Tactic in def do_cases_spine : TacticM (List MVarId) := do
  Tactic.liftMetaMAtMain (fun goal => goal.casesRec (fun decl => do
      match ← checkTypeQ (← whnf decl.type) q(Prop) with
      | .some ~q(Judge $α $e) =>
        contains_spine e
      | .some ~q(ParRed $e $x') =>
        contains_spine e
      | _ => pure false))

syntax "extract_conv" : tactic
syntax "extract_conv?" : tactic

open Qq Lean Meta Elab Tactic in def extract_conv (with_logs : Bool := false) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let hyp : Option Q(Prop) ← Qq.checkTypeQ (← whnf decl.type) q(Prop)
      match hyp with
      | .some ((Lean.Expr.forallE _c (Lean.Expr.const `Expr []) (Lean.Expr.forallE _n (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `ParRed []) x)
        (Lean.Expr.bvar 0)) _imp _b) _b₂)) =>
        let decl₂ : Option (Q(_root_.Expr) × LocalDecl) := ← (lctx.decls.toList.reverse.filterMap id).findSomeM? (fun (decl₂ : LocalDecl) => do
          let solver : Option Q(Prop) ← Qq.checkTypeQ (← whnf decl₂.type) q(Prop)
          match solver with
          | .some ~q(ParRed $x' $c₂) =>
            if ← isDefEq x x' then
              pure <| .some ⟨c₂, decl₂⟩
            else
              if with_logs then dbg_trace s!"no match: {toString x} {toString x'}; skipping"
              pure .none
          | e =>
            if with_logs then dbg_trace s!"cannot solve ParRed proofs: {e}; skipping"
            pure .none)
        match decl₂ with
        | .some ⟨e_solve, solver⟩ =>
          let post ← mkFreshId
          let nm' := Lean.Name.str post decl.userName.toString
          let proof := (Lean.Expr.app (.fvar decl.fvarId) e_solve).app (.fvar solver.fvarId)
          let t ← inferType proof
          let _new_t : Option Q(Prop) := ← Qq.checkTypeQ (← whnf t) q(Prop)
          let ⟨_fvar, g⟩ ← g.assertHypotheses ⟨[Hypothesis.mk nm' t proof .default .default]⟩
          setGoals [g]
          let idt := mkIdent nm'
          evalTactic (← `(tactic| rcases $idt:ident with ⟨D, p₁, p₂⟩))
        | _ => continue
      | _ => continue

elab "extract_conv" : tactic => do
  extract_conv

elab "extract_conv?" : tactic => do
  extract_conv true

open Qq Lean Meta Elab Tactic in elab "cases_spine" : tactic => do
  let gs ← do_cases_spine
  setGoals gs

open Qq gen Lean Meta Elab Tactic in elab "decide_conv" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let tgt ← getMainTarget
    let tgt : Option Q(Prop) ← Qq.checkTypeQ tgt q(Prop)
    match tgt with
    | .some ~q(∃ x, ParRed $A x ∧ ParRed $B x) =>
      match ← checkTypeQ A q(_root_.Expr), ← checkTypeQ B q(_root_.Expr) with
      | .some A, .some B =>
        let mA ← MExpr.decode A
        let mB ← MExpr.decode B

        let red₁ ← reduce mA
        let red₂ ← reduce mB

        let D₁ : Q(_root_.Expr) := ← red₁.fst.unify
        let D₂ : Q(_root_.Expr) := ← red₂.fst.unify

        match ← checkTypeQ D₁ q(_root_.Expr), ← checkTypeQ D₂ q(_root_.Expr) with
        | .some D₁, .some D₂ =>
          match ← isDefEqQ D₁ D₂ with
          | .defEq _heq =>
            let p₁ : Q(ParRed $A $D₁) := ← gen_par_red_proof red₁.snd
            let p₂ : Q(ParRed $B $D₁) := ← gen_par_red_proof red₂.snd

            match ← checkTypeQ p₁ q(ParRed $A $D₁), ← checkTypeQ p₂ q(ParRed $B $D₂) with
            | .some p₁, .some p₂ =>
              goal.assign q(@Exists.intro _root_.Expr (fun d => ParRed $A d ∧ ParRed $B d) $D₁ (And.intro $p₁ $p₂))
            | _, _ => throwError s!"{D₁} ≠ {D₂}"
          | _ => throwError s!"cannot solve. mismatch:\n{D₁} ≠ \n{D₂}"
        | _, _ => throwError "not an expr"
      | .none, _ => throwError s!"not an Expr: {A}"
      | _, .none => throwError s!"not an Expr: {B}"
    | e => throwError s!"not a valid conversion goal: {repr e}"

open Qq gen Lean Meta Elab Tactic in def decode_red' (A B : Q(_root_.Expr)) : TacticM Q(ParRed $A $B ∨ ¬ ParRed $A $B) := do
  let mA ← MExpr.decode A
  let ⟨g₁, hp₁⟩ ← reduce mA

  let AA ← g₁.unify

  let ehp₁ : Q(ParRed $A $AA) := ← gen_par_red_proof hp₁

  let proof : Q(ParRed $A $B ∨ ¬ ParRed $A $B) := q(by
      let hpr₁ : ParRed $A $AA := $ehp₁
      if heq : $AA = $B then
        rw [← heq]
        exact Or.inl hpr₁
      else
        
        sorry)
  return proof

open Expr in example : ∃ D, ParRed ⸨(I 2) (Srt 1) (Srt 0)⸩ D ∧ ParRed ⸨(I 2) (Srt 1) (Srt 0)⸩ D := by
  decide_conv

theorem I.diamond (ih : ∀ {c : Expr}, ParRed x c → ∃ d, ParRed x' d ∧ ParRed c d) : ParRed (((Expr.I _m).app _α).app x) c → ∃ d, ParRed x' d ∧ ParRed c d := by
  intro h
  cases h
  · simp_all
  · cases_spine
    extract_conv
    decide_conv

instance ParRed.instDecidable : Decidable (ParRed a b) := by
  
  sorry
