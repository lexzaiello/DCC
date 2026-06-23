import Dcc.Judge
import Dcc.Ast
import Dcc.Judge2
import Dcc.Types
import Dcc.Eta.Reduce
import Dcc.Tactic.Debug

#eval (DCC *(Sndc(`(⊤, Sort 0)))).infer₂'

open Lean.Meta (MetaM)

abbrev DebruijnIdx := ℕ

deriving instance Lean.ToExpr for GenericExpr

namespace GenericExpr

open Qq in
open Lean (toExpr) in
def fvar_expr_to_lean (e : GenericExpr Lean.FVarId) (τ : Lean.Name := ``Unit) : Lean.Expr :=
  let exp (nm : Lean.Name := ``_root_.GenericExpr) : Lean.Expr := (.app (.const nm [0]) (.const τ []))
  match e with
  | (DCC? ⊤)                   => exp ``_root_.GenericExpr.top
  | (DCC? ⊥)                   => exp ``_root_.GenericExpr.bot
  | (DCC? ∗)                   => exp ``_root_.GenericExpr.tintro
  | (DCC? !<f>)                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.map) f'
  | (DCC? $<f>)                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.fmap) f'
  | (DCC? &(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.box) f'
  | (DCC? *(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.unbox) f'
  | (DCC? !(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.bang) f'
  | (DCC? Eval(α, β, x))       =>
    let α' := α.fvar_expr_to_lean
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (.app (exp ``_root_.GenericExpr.eval) α') β') x'
  | (DCC? Λ(α, β, x))       =>
    let α' := α.fvar_expr_to_lean
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (.app (exp ``_root_.GenericExpr.curr) α') β') x'
  | (DCC? !Λ(α, β, x))       =>
    let α' := α.fvar_expr_to_lean
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (.app (exp ``_root_.GenericExpr.curr') α') β') x'
  | (DCC? `(β, x)) =>
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (exp ``_root_.GenericExpr.quot) β') x'
  | (DCC? Id(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.id) f'
  | (DCC? Sort m)              =>
    .app (exp ``_root_.GenericExpr.sort) (toExpr m)
  | (DCC? Fstc(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.fstc) f'
  | (DCC? Sndc(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.sndc) f'
  | (DCC? Π(β, x)) =>
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (exp ``_root_.GenericExpr.pi) β') x'
  | (DCC? ⟦β⟧⟨a, b⟩)       =>
    let β' := β.fvar_expr_to_lean
    let a' := a.fvar_expr_to_lean
    let b' := b.fvar_expr_to_lean
    .app (.app (.app (exp ``_root_.GenericExpr.pair) β') a') b'
  | (DCC? ⟦β⟧(a, b))       =>
    let β' := β.fvar_expr_to_lean
    let a' := a.fvar_expr_to_lean
    let b' := b.fvar_expr_to_lean
    .app (.app (.app (exp ``_root_.GenericExpr.mkc) β') a') b'
  | (DCC? Coup(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.coup) f'
  | (DCC? Σ(β, x)) =>
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (exp ``_root_.GenericExpr.sigma) β') x'
  | (DCC? β = x) =>
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (exp ``_root_.GenericExpr.eq) β') x'
  | (DCC? Eql(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.eql) f'
  | (DCC? refl(f))                =>
    let f' := f.fvar_expr_to_lean
    .app (exp ``_root_.GenericExpr.refl) f'
  | (DCC? β ∘ x) =>
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (exp ``_root_.GenericExpr.comp) β') x'
  | (DCC? β ∘' x) =>
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (exp ``_root_.GenericExpr.comp') β') x'
  | (DCC? β ∘∘ x) =>
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (exp ``_root_.GenericExpr.comp₂) β') x'
  | (DCC? (β x))               =>
    let β' := β.fvar_expr_to_lean
    let x' := x.fvar_expr_to_lean
    .app (.app (exp ``_root_.GenericExpr.app) β') x'
  | .const c => .fvar c

end GenericExpr

/-
Auto-detecting sharing?

λ x => M N

x should be shared in this scope.
Just need a stack-like thing.

every variable access under an app needs sharing.
a tree. every split under the lambda where the variable is used must be accounted for.

If a variable occurs in another element that is also shared, then it must also be shared.
-/

partial def occ_shared (depth : Nat) : Lean.Expr → Bool × Nat
  | .bvar n => (n == depth, 0)
  | .app M N =>
    let (oM, sM) := occ_shared depth M
    let (oN, sN) := occ_shared depth N
    ((oM || oN),
      if oM && oN then 1 + sM + sN
      else if oM then 1 + sM
      else if oN then 1 + sN
      else 0)
  | .lam _ t b _ | .forallE _ t b _ =>
    let (ot, st) := occ_shared depth t
    let (ob, sb) := occ_shared depth.succ b
    (ot || ob, st + sb)
  | .letE _ t v b _ =>
    let (ot, st) := occ_shared depth t
    let (ov, sv) := occ_shared depth v
    let (ob, sb) := occ_shared depth.succ b
    (ot || ov || ob, st + sv + sb)
  | .proj _ _ s => occ_shared depth s
  | _ => (false, 0)

def occurs_in (depth : DebruijnIdx) (in_e : Lean.Expr) : Bool :=
  match in_e with
  | .bvar n => n == depth
  | .lam _ bty bdy _ => occurs_in depth bty ∨ occurs_in depth.succ bdy
  | .forallE _ bty bdy _ => occurs_in depth bty ∨ occurs_in depth.succ bdy
  | .letE _ ty val bdy _ => occurs_in depth ty ∨ occurs_in depth val ∨ occurs_in depth bdy
  | .proj _ _ strt => occurs_in depth strt
  | .mdata _ _ | .lit _ | .const _ _ | .sort _ | .mvar _ | .fvar _ => False
  | .app M N => occurs_in depth M ∨ occurs_in depth N

def shared_in (depth : DebruijnIdx) (in_e : Lean.Expr) : ℕ :=
  match in_e with
  | .app M N =>
    match occurs_in depth M, occurs_in depth N with
    | .true, .true       => 1 + (shared_in depth M) + (shared_in depth N)
    | .true, _           => 1 + (shared_in depth M)
    | _, .true           => 1 + (shared_in depth N)
    | _, _               => 0
  | .lam _ bty bdy _     =>
    -- If the variable being checked occurs in another variable that is shared,
    (shared_in depth bty) + (shared_in depth.succ bdy)
  | .forallE _ bty bdy _ =>
    -- If the variable being checked occurs in another variable that is shared,
    (shared_in depth bty) + (shared_in depth.succ bdy)
  | .proj _ _ strt => shared_in depth strt
  | .letE _ ty val bdy _ => (shared_in depth ty) + (shared_in depth val) + (shared_in depth bdy)
  | .bvar _ | .mdata _ _ | .lit _ | .const _ _ | .sort _ | .mvar _ | .fvar _ => 0

def Ctx.{u} (τ_c : Type u) := GenericExpr τ_c
def Ctx.empty.{u} (τ_c : Type u) := ((DCC? !(⊤)) : GenericExpr τ_c)
def Ctx.empty'.{u} (τ_c : Type u) := ((DCC? ⊤) : GenericExpr τ_c)

instance [Std.ToFormat τ_c] : ToString (Ctx τ_c) := ⟨toString ∘ GenericExpr.toFormat⟩
instance [Repr τ_c] : ToString (Ctx τ_c) := ⟨toString ∘ GenericExpr.toFormat (hFmt := ⟨repr⟩)⟩

abbrev ParamInfer.{u} (τ_c : Type u) := (t_judge : (GenericExpr τ_c → GenericExpr τ_c → Prop)) × (∀ (e : GenericExpr τ_c), Option ((τ : GenericExpr τ_c) × PULift.{1, 0} (t_judge e τ)))

/-def cc_var (ctx : Ctx) (idx : DebruijnIdx) (infer : ParamInfer := ⟨Expr.Judge, Expr.infer⟩) (reduce : Expr → Expr := Expr.reduce_all) : Lean.MacroM Expr :=
  match ctx, idx with
  | DCC Coup(β), .zero => pure <| DCC Sndc(β)
  | DCC !(Coup(β)), .zero => pure <| DCC Sndc(β) ∘' *(Coup(β))
  | DCC !(Coup(β)), .succ n => do
    match (·.fst) <$> infer.snd β with
    | .some (DCC (Π(a, _b) x_α)) =>
      (DCC ((#(·) ∘' Fstc(β)) ∘' !(Coup(β)))) <$> cc_var (reduce (DCC (a x_α))) n infer reduce
    | _ => Lean.Macro.throwError s!"Couple β index is not valid: {β}"
  | DCC Coup(β), .succ n => do
    match (·.fst) <$> infer.snd β with
    | .some (DCC (Π(a, _b) x_α)) =>
      (·.comp' (DCC (Fstc(β)))) <$> (cc_var (reduce (DCC (a x_α))) n infer (reduce := reduce))
    | _ => Lean.Macro.throwError s!"Couple β index is not valid: {β}"
  | e, n => Lean.Macro.throwError s!"Cannot be indexed at {n} as a couple: {e}"-/

def cc_var (τ_c : Type) [Repr τ_c] [DecidableEq τ_c] (ctx : Ctx τ_c) (idx : DebruijnIdx) (infer : ParamInfer τ_c := ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩)
  (reduce : GenericExpr τ_c → GenericExpr τ_c := GenericExpr.reduce_all₂) : Lean.MacroM (GenericExpr τ_c) :=
  match ctx with
  | DCC? !(α) => do
    have h_dec : α.size < α.bang.size := by
      grind
    let x ← cc_var (τ_c := τ_c) (ctx := α) idx infer reduce
    pure (DCC? *(x))
  | _ =>
    match ctx, idx with
    | DCC? Coup(β), .zero => pure <| DCC? Sndc(β)
    | DCC? !(Coup(β)), .zero => pure <| DCC? *(Sndc(β))
    | DCC? !(Coup(β)), .succ n => do
      match (·.fst) <$> infer.snd β with
      | .some (DCC? (Π(a, _b) x_α)) =>
        --(DCC? ((#(·) ∘' Fstc(β)) ∘' !(Coup(β)))) <$> cc_var τ_c (reduce (DCC? (a x_α))) n infer reduce
        (DCC? (*((#(·) ∘' Fstc(β))))) <$> cc_var τ_c (reduce (DCC? (a x_α))) n infer reduce
      | τ => Lean.Macro.throwError s!"Couple β index is not valid: ({β} : {τ})"
    | DCC? Coup(β), .succ n => do
      match (·.fst) <$> infer.snd β with
      | .some (DCC? (Π(a, _b) x_α)) =>
        (·.comp' (DCC? (Fstc(β)))) <$> (cc_var τ_c (reduce (DCC? (a x_α))) n infer (reduce := reduce))
      | τ => Lean.Macro.throwError s!"Couple β index is not valid: ({β} : {τ})"
    | e, n => Lean.Macro.throwError s!"Cannot be indexed at {n} as a couple: {e}"
termination_by (idx, GenericExpr.size ctx)

def GenericExpr.deref : GenericExpr τ → GenericExpr τ
  | DCC? !(Γ) => Γ
  | Γ => Γ

/-
TODO: better logic for detecting duplication. Maybe some kind of user marker.

deref needs to see environment, maybe?

e.g.,

deref (α := deref ...) ...

f_α : δ → Sort m
*(f_α) : ∀ (env : !(δ)) (x : !<f_α> env), f_α (*(

this may not be necessary. think this through.

deref (α is function of environment)

is equivalent to just dereferencing environment, then mutating. I think.

Shared.deref (fun (ctx : Γ) => α)

however, the deref is a standalone function.

deref is only really valid on a variable access.

I think we just have the order flipped or something.
-/

#check Eq.refl

abbrev fallback_expr_cc {τ_c : Type} : Lean.Expr →
  Lean.MacroM (GenericExpr τ_c) := fun e => Lean.Macro.throwError s!"not a recognized expression: {e}"

def abstract' (τ_c : Type) [DecidableEq τ_c] [Repr τ_c] (e : Lean.Expr) (ctx : Ctx τ_c) (infer : ParamInfer τ_c := ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩) (reduce : GenericExpr τ_c → GenericExpr τ_c := GenericExpr.reduce_all₂)
  (fallback : Lean.Expr → Lean.MacroM (GenericExpr τ_c) := fallback_expr_cc) : Lean.MacroM (GenericExpr τ_c) := do
  match e with
  | .fvar v => fallback (.fvar v)
  --| .app (.app (.const ``Shared.deref _us) _α) (.app (.app (.const ``Shared.share _us₁) _α₁) x) => abstract' τ_c x ctx infer reduce fallback
  | .app (.app (.const ``Shared.deref _us) _α) f =>
    let f' ← abstract' τ_c f ctx infer reduce fallback
    pure f'
    /-let f' ← abstract' τ_c f ctx.deref infer reduce fallback
    return (DCC? *(f'))-/
  | .app (.app (.const ``Shared.share _us) _α) (.sort .zero) => return DCC? (`(ctx, &(Sort 0)))
  | .app (.const ``Shared _us) (.sort .zero) => return DCC? (`(ctx, !(Sort 0)))
  | .app (.app (.const ``Shared.share _us) _α) (.sort (.succ m)) => do
    match ← (abstract' τ_c (.sort m) ctx infer reduce fallback) with
    | DCC? (`(ctx, &(Sort n)))
    | DCC? (`(ctx, Sort n)) => return (DCC? (`(ctx, &(Sort (n + 1)))))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | .app (.const ``Shared _us) (.sort (.succ m)) => do
    match ← (abstract' τ_c (.sort m) ctx infer reduce fallback) with
    | DCC? (`(ctx, !(Sort n)))
    | DCC? (`(ctx, Sort n)) => return (DCC? (`(ctx, !(Sort (n + 1)))))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | .app (.const ``Shared _us) (.const ``True []) => return DCC? (`(ctx, !(⊤)))
  | .app (.app (.const ``Shared.share _us) _α) (.const ``True []) => return DCC? (`(ctx, &(⊤)))
  | .app (.app (.const ``Shared.share _us) _α) (.const ``True.intro []) => return DCC? (`(ctx, &(∗)))
  | .app (.app (.const ``Shared.share _us) _α) x =>
    let x' ← abstract' τ_c x ctx infer reduce fallback
    return DCC? (`(ctx, &(x')))
  | .app (.const ``Shared _us) (.const ``False []) => return DCC? (`(ctx, !(⊥)))
  | .bvar n => cc_var τ_c ctx n (infer := infer) (reduce := reduce)
  | .app (.app (.const ``Sigma []) α) β => do
    let α' ← abstract' τ_c α ctx infer reduce fallback
    let β' ← abstract' τ_c β (DCC? Coup(α')) infer reduce fallback
    return (DCC? Σ(α', β'))
  | .lam _a (.app (.const ``Shared _us) α) bdy _binfo => do
    let α' ← abstract' τ_c α ctx.deref infer reduce fallback
    let inner ← abstract' τ_c bdy (DCC? !(Coup(α'))) infer reduce fallback
    return (DCC? !Λ(ctx.deref, α', inner))
  | .lam _a α bdy _binfo => do
    let α' ← abstract' τ_c α ctx infer reduce fallback
    let inner ← abstract' τ_c bdy (DCC? Coup(α')) infer reduce fallback
    return (DCC? Λ(ctx, α', inner))
  | .forallE _name (.app (.const ``Shared _us) α) β _binfo => do
    let α' ← reduce <$> abstract' τ_c α ctx infer reduce fallback
    let β' ← reduce <$> abstract' τ_c β (DCC? !(Coup(α'))) infer reduce fallback

    return (reduce (DCC? (Π(α', !Λ(ctx.deref, α', β')))))
  | .forallE _name α β _binfo => do
    let α' ← reduce <$> abstract' τ_c α ctx infer reduce fallback
    let β' ← reduce <$> abstract' τ_c β (DCC? Coup(α')) infer reduce fallback

    return reduce (DCC? (Π(α', Λ(ctx, α', β'))))
  | .app (.const ``Shared _us) α => do
    let α' ← reduce <$> abstract' τ_c α ctx infer reduce fallback
    -- could be this one
    return (DCC? (!<α'>))
  | (.app (.const ``Eq.refl _us) α) => do
    let α' ← reduce <$> abstract' τ_c α ctx infer reduce fallback
    return (DCC? refl(α'))
  | .app M N => do
    let ctx' := match ctx with
      | DCC? !(Γ) => Γ
      | Γ => Γ
    let M' ← abstract' τ_c M ctx' infer reduce fallback
    let N' ← abstract' τ_c N ctx' infer reduce fallback

    --dbg_trace M
    --dbg_trace N
    --dbg_trace M'
    --dbg_trace N'

    /-
      M : ∀ (x : α) (y : β x)
    -/

    --dbg_trace Sigma.fst <$> infer.snd M'

    match (·.fst) <$> infer.snd M' with
    | .some (DCC? (Π(f_α, f_β) x_α)) =>
      let α : GenericExpr τ_c := match reduce (f_α.app x_α) with
        | DCC? !(α) => α
        | α => α
      match reduce (f_β.app x_α) with
      | DCC? Π(β, _γ) =>
        dbg_trace α
        dbg_trace N'
        match (·.fst) <$> infer.snd (DCC? Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))) with
        | .some (DCC? (Π(_f_α, f_β₀) x_α₀)) =>
          match reduce (DCC? (f_β₀ x_α₀)) with
          | DCC? Π(_β₂, x_γ') =>
            let inner := reduce (DCC? ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩)
            match (·.fst) <$> infer.snd inner with
            | .some (DCC? (Π(_a₁, `(_a₂, Σ(_a₃, Λ(_a₄, _a₅, `(_α₆, _a₇))) ∘' _a₈)) _a₉)) =>
              -- NOTE: this used to be ∘, but not sure if necessary.
              return (DCC? Eval(α, β, M') ∘ ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩)
            | .some (DCC? (Π(_a₁, `(_a₂, `(_a₃, _a₄))) _a₅)) =>
              return (DCC? Eval(α, β, M') ∘' ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩)
            | _ => return (DCC? Eval(α, β, M') ∘∘ ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩)
          | _ => Lean.Macro.throwError ("app is not well-typed:"
            ++ Std.Format.line ++ (.nestD (Std.format (Lean.Expr.app M N)))
            ++ ("couldn't detect codomain:" ++ Std.Format.line ++ (.nestD (Std.format (reduce (DCC? (f_β₀ x_α₀))))))).pretty
        | τ => Lean.Macro.throwError ("app is not well-typed [1]:" ++ Std.Format.line ++
          (Std.format (Lean.Expr.app M N)) ++ Std.Format.line ++ "at: " ++ (Std.format τ) ++ Std.Format.line ++
          "with (M): " ++ (Std.format M') ++ .line ++ "(N): " ++ (Std.format N')).pretty
      | τ => Lean.Macro.throwError ("app is not well-typed [2]:" ++ Std.Format.line ++
        "found: " ++ (Std.format (Lean.Expr.app M N)) ++ Std.Format.line ++ "at: " ++ (Std.format τ)).pretty
    | x => Lean.Macro.throwError ("app is not well-typed [3]:" ++ Std.Format.line ++ (Std.format (Lean.Expr.app M N)) ++ Std.Format.line ++ "in: " ++ (Std.format (DCC? (M' N'))) ++ Std.Format.line ++ "found: " ++ Std.format x).pretty
  | .const ``True.intro [] => return DCC? (`(ctx, ∗))
  | .const ``True [] => return DCC? (`(ctx, ⊤))
  | .const ``False [] => return DCC? (`(ctx, ⊥))
  | .sort .zero => return DCC? (`(ctx, Sort 0))
  | .sort (.succ m) => do
    match ← (abstract' τ_c (.sort m) ctx infer reduce fallback) with
    | DCC? (`(ctx, Sort n)) => pure (DCC? (`(ctx, Sort (n + 1))))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | e => fallback e

def cc (τ_c : Type) [DecidableEq τ_c] [Repr τ_c] (root : Lean.Expr) (infer : ParamInfer τ_c)
  (reduce : GenericExpr τ_c → GenericExpr τ_c)
  (fallback : Lean.Expr → Lean.MacroM (GenericExpr τ_c) := fallback_expr_cc) : Lean.MacroM (GenericExpr τ_c) :=
  match root with
  | .app (.const ``Shared _us) x => do
    let x' ← cc τ_c x infer reduce fallback
    -- could also be this one
    -- this one is top level though, so probably right
    return DCC? !(x')
  | .app (.app (.const ``Shared.share _us) _α) x => do
    let x' ← cc τ_c x infer reduce fallback
    return DCC? &(x')
  | .app (.lam _a α bdy _binfo) (.app (.app (.const ``Shared.share _us) _α) x) => do
    let f' ← abstract' τ_c (.lam _a α bdy _binfo) (Ctx.empty τ_c) infer reduce fallback
    let x' ← cc τ_c x infer reduce fallback
    return (DCC? (f' &(∗) &(x')))
  | .app (.forallE _a α bdy _binfo) (.app (.app (.const ``Shared.share _us) _α) x) => do
    let f' ← abstract' τ_c (.forallE _a α bdy _binfo) (Ctx.empty τ_c) infer reduce fallback
    let x' ← cc τ_c x infer reduce fallback
    return (DCC? (f' &(∗) &(x')))
  | (.lam _a (.app (.const ``Shared _us) α) bdy _binfo) => do
    let f' ← abstract' τ_c (.lam _a (.app (.const ``Shared _us) α) bdy _binfo) (Ctx.empty τ_c) infer reduce fallback
    return (DCC? (f' &(∗)))
  | (.forallE _a (.app (.const ``Shared _us) α) bdy _binfo) => do
    let f' ← abstract' τ_c (.forallE _a (.app (.const ``Shared _us) α) bdy _binfo) (Ctx.empty τ_c) infer reduce fallback
    return (DCC? (f' &(∗)))
  | .app (.lam _a α bdy _binfo) x => do
    let f' ← abstract' τ_c (.lam _a α bdy _binfo) (Ctx.empty τ_c) infer reduce fallback
    let x' ← cc τ_c x infer reduce fallback
    return (DCC? (f' &(∗) x'))
  | .app (.forallE _a α bdy _binfo) x => do
    let f' ← abstract' τ_c (.forallE _a α bdy _binfo) (Ctx.empty τ_c) infer reduce fallback
    let x' ← cc τ_c x infer reduce fallback
    return (DCC? (f' &(∗) x'))
  | .app M N => do
    let M' ← cc τ_c M infer reduce fallback
    let N' ← cc τ_c N infer reduce fallback
    match infer.snd M', N' with
    | .some ⟨DCC? (Π(_f_α, _f_β) !(_b)), _h⟩, _n =>
      return (DCC? (M' &(N')))
    | _, (DCC? &(_n)) =>
      -- match infer M' to see if we need to wrap &(
      return (DCC? (M' N'))
    | .some ⟨DCC? (Π(!<_f>, _f_β) _b), _h⟩, _n =>
      return (DCC? (M' &(N')))
    | _τ, _ =>
      return (DCC? (M' N'))
    /-match M' with
    | DCC? (f &(x)) => return (DCC? (f &(x) &(N')))
    | _ => return (DCC? (M' N'))-/
  | .const ``True.intro [] => return DCC? (∗)
  | .const ``True [] => return DCC? (⊤)
  | .const ``False [] => return DCC? (⊥)
  | .sort .zero => return DCC? (Sort 0)
  | .sort (.succ m) => do
    match ← (cc τ_c (.sort m) infer reduce fallback) with
    | DCC? Sort n => pure (DCC? Sort (n + 1))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | (.lam _a α bdy _binfo) => do
    let f' ← abstract' τ_c (.lam _a α bdy _binfo) (Ctx.empty' τ_c) infer reduce fallback
    return (DCC? (f' ∗))
  | (.forallE _a α bdy _binfo) => do
    let f' ← abstract' τ_c (.forallE _a α bdy _binfo) (Ctx.empty' τ_c) infer reduce fallback
    return (DCC? (f' ∗))
  | .fvar v => fallback (.fvar v)
  | e => (·.app (DCC? (&(∗)))) <$> abstract' τ_c e (Ctx.empty τ_c) infer reduce fallback

def wrap_shares (n : ℕ) (u : Lean.Level) (e : Lean.Expr) : Lean.Expr :=
  match u with
  | .zero =>
    (List.replicate n (Lean.Expr.const ``Shared [0])).foldr .app e
  | .succ u =>
    (List.replicate n (Lean.Expr.const ``Shared [u])).foldr .app e
  | lvl =>
    (List.replicate n (Lean.Expr.const ``Shared [lvl])).foldr .app e

def n_times_shared (e : Lean.Expr) : (Option Lean.Level) × ℕ × Lean.Expr :=
  match e with
  | (.app (.const ``Shared [l]) α) =>
    let (_l, n, e) := (n_times_shared α)
    (.some l, n.succ, e)
  | e => (.none, .zero, e)

def share_n_times (n : ℕ) (lvl : Lean.Level) (α e : Lean.Expr) : Lean.Expr :=
  Prod.snd <| (List.replicate n (Lean.Expr.const ``Shared.share
    (match lvl with
    | .zero => [.zero]
    | .succ n => [n]
    | lvl => [lvl]))).foldr (init := (α, e))
    (f := fun e ((α, x): Lean.Expr × Lean.Expr) =>
      ((.app (Lean.Expr.const ``Shared [
        match lvl with
        | .zero => .zero
        | .succ n => n
        | lvl => lvl]) α), (.app (Lean.Expr.app e α) x)))

def deref_n_times (n : ℕ) (lvl : Lean.Level) (base_ty e : Lean.Expr) : Lean.Expr :=
  match n with
  | 0 => e
  | n' + 1 =>
    let inner_ty := wrap_shares n' lvl base_ty
    let e' := Lean.Expr.app (Lean.Expr.app (.const ``Shared.deref [
      match lvl with
      | .zero => .zero
      | .succ n => n
      | lvl => lvl]) inner_ty) e
    deref_n_times n' lvl base_ty e'

def deref_vars (k depth : ℕ) (lv : Lean.Level) (with_ty in_e : Lean.Expr) : Lean.Expr :=
  match in_e with
  | .bvar v => if v == depth then deref_n_times k lv with_ty (.bvar v) else .bvar v
  | .lam a bty bdy b => .lam a (deref_vars k depth lv with_ty bty) (deref_vars k depth.succ lv with_ty bdy) b
  | .forallE a bty bdy b => .forallE a (deref_vars k depth lv with_ty bty) (deref_vars k depth.succ lv with_ty bdy) b
  | .letE a ty val bdy b => .letE a (deref_vars k depth lv with_ty ty) (deref_vars k depth lv with_ty val) (deref_vars k depth lv with_ty bdy) b
  | .proj a b strt => .proj a b (deref_vars k depth lv with_ty strt)
  | .mdata _ _ | .lit _ | .const _ _ | .sort _ | .mvar _ | .fvar _ => in_e
  | .app M N => .app (deref_vars k depth lv with_ty M) (deref_vars k depth lv with_ty N)

def wrap_share_auto (e : Lean.Expr) : Lean.Meta.MetaM Lean.Expr := do
  match e with
  | .proj a b strt => return .proj a b (← wrap_share_auto strt)
  | .letE a ty val bdy b =>
    return .letE a (← wrap_share_auto ty) (← wrap_share_auto val) (← wrap_share_auto bdy) b
  | .lam a bty bdy b => do
    let bty' ← wrap_share_auto bty
    let (_, n_used) := occ_shared 0 bdy
    match n_used with
    | 0 => return .lam a bty' (← wrap_share_auto bdy) b
    | k =>
      let lv ← Lean.Meta.getLevel bty <|> Lean.Meta.mkFreshLevelMVar
      let bty' := wrap_shares k lv bty'
      let bdy' := deref_vars k 0 lv bty (← wrap_share_auto bdy)
      return .lam a bty' bdy' b
  | .forallE a bty bdy b => do
    let bty' ← wrap_share_auto bty
    let (_, n_used) := occ_shared 0 bdy
    match n_used with
    | 0 => return .forallE a bty' (← wrap_share_auto bdy) b
    | k =>
      let lv ← Lean.Meta.getLevel bty <|> Lean.Meta.mkFreshLevelMVar
      let bty' := wrap_shares k lv bty'
      let bdy' := deref_vars k 0 lv bty (← wrap_share_auto bdy)
      return .forallE a bty' bdy' b
  /-| .forallE a bty bdy b => do
    let bty' ← wrap_share_auto bty
    let n_used := occ_shared 0 bdy
    match n_used with
    | 0 => return .forallE a bty' (← wrap_share_auto bdy) b
    | k =>
      let lv ← Lean.Meta.getLevel bty'
      let bty' := wrap_shares k lv bty'
      let bdy' := deref_vars k 0 lv bty (← wrap_share_auto bdy)
      return .forallE a bty' bdy' b-/
  | .app M N => do
    let M' ← wrap_share_auto M
    let N' ← wrap_share_auto N
    -- try infertype on M' to smartly fetch whether we need to share
    match M' with
    | .lam _ α _ _ =>
      let ⟨lvl, n_shared, α⟩ := n_times_shared α
      match lvl with
      | .some lv =>
        let N'' := share_n_times n_shared lv α N'
        return .app M' N''
      | _ => return .app M' N'
    | _ =>
      try
        match ← Lean.Meta.inferType M' with
        | .forallE _ α _ _ =>
          let ⟨lvl, n_shared, α⟩ := n_times_shared α
          match lvl with
          | .some lv =>
            let N'' := share_n_times n_shared lv α N'
            return .app M' N''
          | _ => return .app M' N'
        | _ =>
          throwError "panic"
      catch _ =>
        return .app M' N'
  | e => return e

def wrap_share_auto_trans (e : Lean.Expr) : Lean.Meta.MetaM Lean.Expr := do
  match e with
  | .app (.app (.const ``Shared.deref _lvs) _α) _x => return e
  | .app (.app (.const ``Shared.share _lvs) _α) _x => return e
  | .proj a b strt => return .proj a b (← wrap_share_auto_trans strt)
  | .letE a ty val bdy b =>
    return .letE a (← wrap_share_auto_trans ty) (← wrap_share_auto_trans val) (← wrap_share_auto_trans bdy) b
  | .lam _a (.app (.const ``Shared _lvs) bty) bdy b => do
    return .lam _a (.app (.const ``Shared _lvs) bty) (← wrap_share_auto_trans bdy) b
  | .lam a bty bdy b => do
    let bty' ← wrap_share_auto_trans bty
    let (_, n_used) := occ_shared 0 bdy
    match n_used with
    | 0 => return .lam a bty' (← wrap_share_auto_trans bdy) b
    | _k =>
      let lv ← Lean.Meta.getLevel bty <|> Lean.Meta.mkFreshLevelMVar
      let bty' := wrap_shares 1 lv bty'
      let bdy' := deref_vars 1 0 lv bty (← wrap_share_auto_trans bdy)
      return .lam a bty' bdy' b
  | .forallE _a (.app (.const ``Shared _lvs) bty) bdy b => do
    return .forallE _a (.app (.const ``Shared _lvs) bty) (← wrap_share_auto_trans bdy) b
  | .forallE a bty bdy b => do
    let bty' ← wrap_share_auto_trans bty
    let (_, n_used) := occ_shared 0 bdy
    match n_used with
    | 0 => return .forallE a bty' (← wrap_share_auto_trans bdy) b
    | _k =>
      let lv ← Lean.Meta.getLevel bty'
      let bty' := wrap_shares 1 lv bty'
      let bdy' := deref_vars 1 0 lv bty (← wrap_share_auto_trans bdy)
      return .forallE a bty' bdy' b
  | .app M N => do
    let M' ← wrap_share_auto_trans M
    let N' ← wrap_share_auto_trans N
    match M', N' with
    | .lam _ __α _ _, (.app (.app (.const ``Shared.share _u) _α) __x) =>
      return .app M' N'
    | .lam _ α _ _, N' =>
      let ⟨lvl, n_shared, α⟩ := n_times_shared α
      match lvl with
      | .some lv =>
        let N'' := share_n_times n_shared lv α N'
        return .app M' N''
      | _ => return .app M' N'
    | _, _ =>
    -- try infertype on M' to smartly fetch whether we need to share
    return .app M' N'
  | e => return e

open Qq in
def Lean.Expr.cc' {u : Lean.Level} {α : Q(Sort u)} (root : Q($α)) (infer : ParamInfer Unit := ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩)
  (reduce : _root_.Expr → _root_.Expr := GenericExpr.reduce_all₂) : Lean.MacroM _root_.Expr :=
  cc Unit root (infer := infer) (reduce := reduce)

open Qq in
def Lean.Expr.cc'_fvars {u : Lean.Level} {α : Q(Sort u)} (root : Q($α)) (infer : ParamInfer Lean.FVarId := ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩)
  (reduce : GenericExpr Lean.FVarId → GenericExpr Lean.FVarId := GenericExpr.reduce_all₂) : Lean.MacroM (GenericExpr Lean.FVarId) :=
  cc Lean.FVarId root (infer := infer) (reduce := reduce)

declare_syntax_cat infer_cmd_param

syntax "{" term "}" : infer_cmd_param

def do_dcc_compile (flags : Lean.TSyntaxArray `infer_cmd_param) (tm : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  match flags.toList with
  | [_infer] =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit tm ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂)
  | [_infer, _reduce] =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit tm ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂)
  | _ =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit tm ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂)

def do_dcc_compile_fvars (flags : Lean.TSyntaxArray `infer_cmd_param) (tm : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  match flags.toList with
  | [_infer] =>
    return GenericExpr.fvar_expr_to_lean (← Lean.Elab.liftMacroM <| cc Lean.FVarId tm ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂)
  | [_infer, _reduce] =>
    return GenericExpr.fvar_expr_to_lean (← Lean.Elab.liftMacroM <| cc Lean.FVarId tm ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂)
  | _ =>
    return GenericExpr.fvar_expr_to_lean (← Lean.Elab.liftMacroM <| cc Lean.FVarId tm ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂)

elab "dcc_compile'" infer:infer_cmd_param* tm:term : term => do
  let e_tm ← Lean.Elab.Term.elabTerm tm .none
  let e_tm ← Lean.instantiateMVars e_tm
  let e_tm' ← Lean.instantiateExprMVars (← wrap_share_auto_trans (← (wrap_share_auto e_tm)))
  match infer.toList with
  | [_infer] =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ Expr.reduce_all)
  | [_infer, _reduce] =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂)
  | _ =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit e_tm' ⟨GenericExpr.Judge, GenericExpr.infer⟩ GenericExpr.reduce_all₂)

elab "dcc_compile''" infer:infer_cmd_param* tm:term : term => do
  let e_tm ← Lean.Elab.Term.elabTerm tm .none
  let e_tm ← Lean.instantiateMVars e_tm
  let e_tm' ← Lean.instantiateExprMVars (← wrap_share_auto_trans (← (wrap_share_auto e_tm)))

  let cc_raw_expr (e : Lean.Expr) : Lean.MacroM (GenericExpr Lean.FVarId) :=
    match e with
    | .fvar fv => pure (.const fv)
    | e => Lean.Macro.throwError s!"unrecognized expression: {e}"

  match infer.toList with
  | [_infer] =>
    return GenericExpr.fvar_expr_to_lean (← Lean.Elab.liftMacroM <| cc Lean.FVarId e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂ cc_raw_expr)
  | [_infer, _reduce] =>
    return GenericExpr.fvar_expr_to_lean (← Lean.Elab.liftMacroM <| cc Lean.FVarId e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂ cc_raw_expr)
  | _ =>
    return GenericExpr.fvar_expr_to_lean (← Lean.Elab.liftMacroM <| cc Lean.FVarId e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂ cc_raw_expr)

#eval dcc_compile' {Expr.Judge₂} {Expr.infer₂} ((fun (x : Sort 0) => ((fun (x : Sort 0) => x) x)) True)

elab "dcc_infer''" infer:infer_cmd_param* tm:term : term => do
  let e_tm ← Lean.Elab.Term.elabTerm tm .none
  let e_tm ← Lean.instantiateMVars e_tm
  let e_tm' ← Lean.instantiateExprMVars (← wrap_share_auto_trans (← (wrap_share_auto e_tm)))
  let dcc_e ← do_dcc_compile infer e_tm'
  return dcc_e

macro "dcc_infer'" infer:infer_cmd_param* tm:term : term =>
  match infer.toList with
  | [infer] =>
    match infer with
    | `(infer_cmd_param| { $infer:term }) =>
      `(term| do Sigma.fst <$> ($infer:term (dcc_compile' {$infer:term} $tm:term)))
    | _ => `(term| do Sigma.fst <$> Expr.infer₂ (dcc_compile' $tm:term))
  | [infer, reduce] =>
    match infer with
    | `(infer_cmd_param| { $infer:term }) =>
      match reduce with
      | `(infer_cmd_param| { $reduce:term }) =>
        `(term| do Sigma.fst <$> ($infer:term (dcc_compile' {$infer:term} {$reduce:term} $tm:term)))
      | _ => `(term| do Sigma.fst <$> Expr.infer₂ (dcc_compile' $tm:term))
    | _ => `(term| do Sigma.fst <$> Expr.infer₂ (dcc_compile' $tm:term))
  | _ =>
    `(term| do Sigma.fst <$> (dcc_compile' $tm:term).infer)

syntax "dcc_compile" infer_cmd_param* term : term
syntax "dcc_infer" infer_cmd_param* term   : term

open Qq in
macro_rules
  | `(dcc_compile $infer:infer_cmd_param* $tm:term) =>
    match infer.toList with
    | [_infer] =>
      `((Lean.Expr.cc' q($tm:term) ⟨Expr.Judge₂, Expr.infer₂⟩))
    | _ => `((Lean.Expr.cc' q($tm:term)))
  | `(dcc_infer $infer:infer_cmd_param* $tm:term) =>
    match infer.toList with
    | [infer] =>
      match infer with
      | `(infer_cmd_param| {$infer:term}) =>
        `(do Sigma.fst <$> ($infer:term (← (Lean.Expr.cc' q($tm:term)))))
      | _ => `((do Sigma.fst <$> (← (Lean.Expr.cc' q($tm:term))).infer))
    | _ =>
      `((do Sigma.fst <$> (← (Lean.Expr.cc' q($tm:term))).infer))

/-
seemingly need to make the compiler less reliant on the lean internal type-checker
either we are producing a malformed expression, or our compilation requires type inference at some midway
point that we should be doing syntactically anyway

ideally, the compiler should not even use elabTerm.
elabTerm does a lot of preprocessing, and it is not exactly compilation if we are using the lean type checker itself.
-/
