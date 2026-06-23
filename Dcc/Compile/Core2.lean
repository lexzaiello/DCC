import Dcc.Judge
import Dcc.Ast
import Dcc.Judge2
import Dcc.Types
import Dcc.Eta.Reduce
import Dcc.Tactic.Debug

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
> 1 means the value showed up in an app, not just any access
-/
def n_occurrences (depth : DebruijnIdx) (in_e : Lean.Expr) : ℕ :=
  match in_e with
  | .bvar n => if n == depth then 1 else 0
  | .lam _ bty bdy _ => max (n_occurrences depth bty) (n_occurrences depth.succ bdy)
  | .forallE _ bty bdy _ => max (n_occurrences depth bty) (n_occurrences depth.succ bdy)
  | .letE _ ty val bdy _ => max (n_occurrences depth ty) (max (n_occurrences depth val)
    (n_occurrences depth.succ bdy))
  | .proj _ _ strt => n_occurrences depth strt
  | .mdata _ _ | .lit _ | .const _ _ | .sort _ | .mvar _ | .fvar _ => 0
  | .app M N => ((n_occurrences depth M) + (n_occurrences depth N)).succ

def Ctx.{u} (τ_c : Type u) := GenericExpr τ_c
def Ctx.empty.{u} (τ_c : Type u) := ((DCC? !(⊤)) : GenericExpr τ_c)
def Ctx.empty'.{u} (τ_c : Type u) := ((DCC? ⊤) : GenericExpr τ_c)

instance [Std.ToFormat τ_c] : ToString (Ctx τ_c) := ⟨toString ∘ GenericExpr.toFormat⟩
instance [Repr τ_c] : ToString (Ctx τ_c) := ⟨toString ∘ GenericExpr.toFormat (hFmt := ⟨repr⟩)⟩

abbrev ParamInfer.{u} (τ_c : Type u) := (t_judge : (GenericExpr τ_c → GenericExpr τ_c → Prop)) × (∀ (e : GenericExpr τ_c), Option ((τ : GenericExpr τ_c) × PULift.{1, 0} (t_judge e τ)))

/-
The only way for a ! or & to show up in the compiled DCC code is if the compiler injected it for sharing
purposes. Therefore, all ! and & values should be dereferenced eagerly.
-/
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

#check Eq.refl

def map_n_times (n : ℕ) (f : GenericExpr τ_c) : GenericExpr τ_c :=
  (List.replicate n GenericExpr.map).foldr id f

def share_n_times (n : ℕ) (e : GenericExpr τ_c) : GenericExpr τ_c :=
  (List.replicate n GenericExpr.box).foldr id e

example : share_n_times 5 (DCC Sort 0) = (DCC &(&(&(&(&(Sort 0)))))) := rfl

def bang_n_times (n : ℕ) (e : GenericExpr τ_c) : GenericExpr τ_c :=
  (List.replicate n GenericExpr.bang).foldr id e

example : bang_n_times 5 (DCC Sort 0) = (DCC !(!(!(!(!(Sort 0)))))) := rfl

abbrev fallback_expr_cc {τ_c : Type} : Lean.Expr →
  Lean.MacroM (GenericExpr τ_c) := fun e => Lean.Macro.throwError s!"not a recognized expression: {e}"

def abstract' (τ_c : Type) [DecidableEq τ_c] [Repr τ_c] (e : Lean.Expr) (ctx : Ctx τ_c) (infer : ParamInfer τ_c := ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩) (reduce : GenericExpr τ_c → GenericExpr τ_c := GenericExpr.reduce_all₂)
  (fallback : Lean.Expr → Lean.MacroM (GenericExpr τ_c) := fallback_expr_cc) : Lean.MacroM (GenericExpr τ_c) := do
  match e with
  | .fvar v => fallback (.fvar v)
  --| .app (.app (.const ``Shared.deref _us) _α) (.app (.app (.const ``Shared.share _us₁) _α₁) x) => abstract' τ_c x ctx infer reduce fallback
  | .bvar n => cc_var τ_c ctx n (infer := infer) (reduce := reduce)
  | .app (.app (.const ``Sigma []) α) β => do
    let α' ← abstract' τ_c α ctx infer reduce fallback
    let β' ← abstract' τ_c β (DCC? Coup(α')) infer reduce fallback
    return (DCC? Σ(α', β'))
  | .lam _a α bdy _binfo => do
    -- α' maps &(ctx)
    -- α' receives deref'd context due to !Λ type
    let α' ← abstract' τ_c α ctx.deref infer reduce fallback
    let n := (n_occurrences 0 bdy) - 1
    let α'' := map_n_times n α'
    -- mark it as shared by mapping with !<α'> n - 1 times
    let inner ← abstract' τ_c bdy (DCC? !(Coup(α''))) infer reduce fallback
    -- deref ctx here because it will be banged !(x) due to !Λ joining
    -- α' here may need to be banged more times than ctx is derefed, however
    -- wrap α' in n !<...>
    -- bang ctx
    return (DCC? !Λ(ctx.deref, α'', inner))
  | .forallE _name α β _binfo => do
    -- ctx doesn't need to be deref'd here because Π does not slice off box
    let α'  ← reduce <$> abstract' τ_c α ctx infer reduce fallback
    let n₁ := (n_occurrences 0 β)
    let n₂ := (n_occurrences 0 β) - 1
    let α₁  ← (map_n_times n₁ ∘ reduce) <$> abstract' τ_c α ctx infer reduce fallback
    let α₂  ← (map_n_times n₂ ∘ reduce) <$> abstract' τ_c α ctx.deref infer reduce fallback
    let β'  ← reduce <$> abstract' τ_c β (DCC? !(Coup(α₂))) infer reduce fallback

    return (reduce (DCC? (Π(α₁, !Λ(ctx.deref, α₂, β')))))
  | (.app (.const ``Eq.refl _us) α) => do
    let α' ← reduce <$> abstract' τ_c α ctx infer reduce fallback
    return (DCC? refl(α'))
  | .app M N => do
    let ctx' := ctx.deref
    -- TODO: M' might also receive N' in ctx?
    let M' ← abstract' τ_c M ctx' infer reduce fallback
    let N' ← abstract' τ_c N ctx' infer reduce fallback

    match (·.fst) <$> infer.snd M' with
    | .some (DCC? (Π(f_α, f_β) x_α)) =>
      -- Deref this due to pair destructing box
      let α : GenericExpr τ_c := (reduce (f_α.app x_α)).deref
      match reduce (f_β.app x_α) with
      | DCC? Π(β, _γ) =>
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

def count_bangs (e : GenericExpr τ_c) : ℕ :=
  match e with
  | DCC? !(x) => (count_bangs x).succ
  | _ => 0

def cc (τ_c : Type) [DecidableEq τ_c] [Repr τ_c] (root : Lean.Expr) (infer : ParamInfer τ_c)
  (reduce : GenericExpr τ_c → GenericExpr τ_c)
  (fallback : Lean.Expr → Lean.MacroM (GenericExpr τ_c) := fallback_expr_cc) : Lean.MacroM (GenericExpr τ_c) :=
  match root with
  | .app (.lam _a α bdy _binfo) x => do
    -- maximum number of times the argument x will be used / shared
    -- need to box terminal object likewise and the context itself
    let n := (n_occurrences 0 bdy)
    let ctx' := bang_n_times n (Ctx.empty' τ_c)

    let f' ← abstract' τ_c (.lam _a α bdy _binfo) ctx' infer reduce fallback
    let x' ← cc τ_c x infer reduce fallback

    let s_x' := share_n_times n x'
    let tintro' := share_n_times n (DCC? ∗)

    return (DCC? (f' tintro' s_x'))
  | .app (.forallE _a α bdy _binfo) x => do
    -- maximum number of times the argument x will be used / shared
    -- need to box terminal object likewise and the context itself
    let n := (n_occurrences 0 bdy)
    let ctx' := bang_n_times n (Ctx.empty' τ_c)

    let f' ← abstract' τ_c (.forallE _a α bdy _binfo) ctx' infer reduce fallback
    let x' ← cc τ_c x infer reduce fallback

    let s_x' := share_n_times n x'
    let tintro' := share_n_times n (DCC? ∗)

    return (DCC? (f' tintro' s_x'))
  | .app M N => do
    let M' ← cc τ_c M infer reduce fallback
    let N' ← cc τ_c N infer reduce fallback
    match infer.snd M' with
    | .some ⟨DCC? (Π(f_α, _f_β) x_α), _h⟩ =>
      let n := count_bangs (reduce (DCC? (f_α x_α)))
      let N'' := share_n_times n N'
      return (DCC? (M' N''))
    | _ => return (DCC? (M' N'))
  | .const ``True.intro [] => return DCC? (∗)
  | .const ``True [] => return DCC? (⊤)
  | .const ``False [] => return DCC? (⊥)
  | .sort .zero => return DCC? (Sort 0)
  | .sort (.succ m) => do
    match ← (cc τ_c (.sort m) infer reduce fallback) with
    | DCC? Sort n => pure (DCC? Sort (n + 1))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | (.lam _a α bdy _binfo) => do
    -- maximum number of times the argument x will be used / shared
    -- need to box terminal object likewise and the context itself
    let n := (n_occurrences 0 bdy)
    let ctx' := bang_n_times n (Ctx.empty' τ_c)

    let f' ← abstract' τ_c (.lam _a α bdy _binfo) ctx' infer reduce fallback
    let tintro' := share_n_times n (DCC? ∗)

    return (DCC? (f' tintro'))
  | (.forallE _a α bdy _binfo) => do
    -- maximum number of times the argument x will be used / shared
    -- need to box terminal object likewise and the context itself
    let n := (n_occurrences 0 bdy)
    let ctx' := bang_n_times n (Ctx.empty' τ_c)

    let f' ← abstract' τ_c (.forallE _a α bdy _binfo) ctx' infer reduce fallback
    let tintro' := share_n_times n (DCC? ∗)

    return (DCC? (f' tintro'))
  | .fvar v => fallback (.fvar v)
  | e => (·.app (DCC? (&(∗)))) <$> abstract' τ_c e (Ctx.empty τ_c) infer reduce fallback

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

elab "dcc_compile" infer:infer_cmd_param* tm:term : term => do
  let e_tm ← Lean.Elab.Term.elabTerm tm .none
  let e_tm' ← Lean.instantiateMVars e_tm
  match infer.toList with
  | [_infer] =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ Expr.reduce_all)
  | [_infer, _reduce] =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂)
  | _ =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc Unit e_tm' ⟨GenericExpr.Judge, GenericExpr.infer⟩ GenericExpr.reduce_all₂)

elab "dcc_compile'" infer:infer_cmd_param* tm:term : term => do
  let e_tm ← Lean.Elab.Term.elabTerm tm .none
  let e_tm' ← Lean.instantiateMVars e_tm

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

#eval dcc_compile {Expr.Judge₂} {Expr.infer₂} ((fun (x : Sort 0) => ((fun (x : Sort 0) => x) x)) True)

elab "dcc_infer" infer:infer_cmd_param* tm:term : term => do
  let e_tm ← Lean.Elab.Term.elabTerm tm .none
  let e_tm' ← Lean.instantiateMVars e_tm

  let cc_raw_expr (e : Lean.Expr) : Lean.MacroM (GenericExpr Lean.FVarId) :=
    match e with
    | .fvar fv => pure (.const fv)
    | e => Lean.Macro.throwError s!"unrecognized expression: {e}"

  let e' ← match infer.toList with
  | [_infer] =>
    Lean.Elab.liftMacroM <| cc Lean.FVarId e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂ cc_raw_expr
  | [_infer, _reduce] =>
    Lean.Elab.liftMacroM <| cc Lean.FVarId e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂ cc_raw_expr
  | _ =>
    Lean.Elab.liftMacroM <| cc Lean.FVarId e_tm' ⟨GenericExpr.Judge₂, GenericExpr.infer₂⟩ GenericExpr.reduce_all₂ cc_raw_expr

  let some τ ← (pure (GenericExpr.infer₂ e')) | throwError m!"does not type-check: {e'}"
  return (GenericExpr.fvar_expr_to_lean τ.fst)

/-macro "dcc_infer" infer:infer_cmd_param* tm:term : term =>
  match infer.toList with
  | [infer] =>
    match infer with
    | `(infer_cmd_param| { $infer:term }) =>
      `(term| do Sigma.fst <$> ($infer:term (dcc_compile {$infer:term} $tm:term)))
    | _ => `(term| do Sigma.fst <$> Expr.infer₂ (dcc_compile $tm:term))
  | [infer, reduce] =>
    match infer with
    | `(infer_cmd_param| { $infer:term }) =>
      match reduce with
      | `(infer_cmd_param| { $reduce:term }) =>
        `(term| do Sigma.fst <$> ($infer:term (dcc_compile {$infer:term} {$reduce:term} $tm:term)))
      | _ => `(term| do Sigma.fst <$> Expr.infer₂ (dcc_compile $tm:term))
    | _ => `(term| do Sigma.fst <$> Expr.infer₂ (dcc_compile $tm:term))
  | _ =>
    `(term| do Sigma.fst <$> (dcc_compile $tm:term).infer₂)-/

#eval Std.format <| dcc_infer (fun (α : Type) (x : α) => x)
#eval Std.format <| dcc_infer (fun (α : Type) (x : α → Type) => x)
