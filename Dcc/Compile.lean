import Dcc.Judge
import Dcc.Judge2
import Dcc.Types
import Dcc.Eta.Reduce
import Dcc.Tactic.Debug

deriving instance Lean.ToExpr for Expr

instance (priority := high) : Repr Expr := ⟨Function.const _ ∘ Expr.toFormat (pretty := False)⟩

/-
Auto-detecting sharing?

λ x => M N

x should be shared in this scope.
Just need a stack-like thing.

every variable access under an app needs sharing.
a tree. every split under the lambda where the variable is used must be accounted for.
-/

def occurs_in (depth : ℕ) (in_e : Lean.Expr) : Bool :=
  match in_e with
  | .bvar n => n == depth
  | .lam _ bty bdy _ => occurs_in depth bty ∨ occurs_in depth.succ bdy
  | .forallE _ bty bdy _ => occurs_in depth bty ∨ occurs_in depth.succ bdy
  | .letE _ ty val bdy _ => occurs_in depth ty ∨ occurs_in depth val ∨ occurs_in depth bdy
  | .proj _ _ strt => occurs_in depth strt
  | .mdata _ _ | .lit _ | .const _ _ | .sort _ | .mvar _ | .fvar _ => False
  | .app M N => occurs_in depth M ∨ occurs_in depth N

def shared_in (depth : ℕ) (in_e : Lean.Expr) : ℕ :=
  match in_e with
  | .app M N =>
    match occurs_in depth M, occurs_in depth N with
    | .true, .true       => 1 + (shared_in depth M) + (shared_in depth N)
    | .true, _           => 1 + (shared_in depth M)
    | _, .true           => 1 + (shared_in depth N)
    | _, _               => 0
  | .lam _ bty bdy _     => (shared_in depth bty) + (shared_in depth.succ bdy)
  | .forallE _ bty bdy _ => (shared_in depth bty) + (shared_in depth.succ bdy)
  | .proj _ _ strt => shared_in depth strt
  | .letE _ ty val bdy _ => (shared_in depth ty) + (shared_in depth val) + (shared_in depth bdy)
  | .bvar _ | .mdata _ _ | .lit _ | .const _ _ | .sort _ | .mvar _ | .fvar _ => 0

inductive Shared.{u} (α : Type u) where
  | share : α → Shared α
deriving Lean.ToExpr

def Shared.deref.{u} {α : Type u} (s : Shared α) : α :=
  match s with
  | ⟨s⟩ => s

#check Shared.deref

def use.{u, v, s} {α : Type u}
  {β : α → Type v} {γ : ∀ (x : α), (β x) → Type s} (f : ∀ (x : α) (y : β x), γ x y)
  (g : ∀ (x : α), β x) : ∀ (x : Shared α), γ x.deref (g x.deref) := fun x =>
  f x.deref (g x.deref)

open Shared

syntax "&(" term ")" : term
syntax "*(" term ")" : term
syntax "↑(" term ")" : term

macro_rules
  | `(&($e:term)) => `(share $e:term)
  | `(*($e:term)) => `(Shared $e:term)
  | `(↑($e:term)) => `(deref $e:term)

def Ctx := Expr
def Ctx.empty := DCC !(⊤)

instance : ToString Ctx := ⟨toString ∘ Expr.toFormat⟩

abbrev ParamInfer := (t_judge : (Expr → Expr → Prop)) × (∀ (e : Expr), Option ((τ : Expr) × PULift.{1, 0} (t_judge e τ)))

def cc_var (ctx : Ctx) (idx : ℕ) (infer : ParamInfer := ⟨Expr.Judge, Expr.infer⟩) (reduce : Expr → Expr := Expr.reduce_all) : Lean.MacroM Expr :=
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
  | e, n => Lean.Macro.throwError s!"Cannot be indexed at {n} as a couple: {e}"

def Expr.deref : Expr → Expr
  | DCC !(Γ) => Γ
  | Γ => Γ

/-
TODO: better logic for detecting duplication. Maybe some kind of user marker.

-/

def abstract' (e : Lean.Expr) (ctx : Ctx) (infer : ParamInfer := ⟨Expr.Judge, Expr.infer⟩) (reduce : Expr → Expr := Expr.reduce_all) : Lean.MacroM _root_.Expr := do
  match e with
  | .app (.app (.const ``Shared.deref _us) _α) x => abstract' x ctx infer reduce
  | .app (.app (.const ``Shared.share _us) _α) (.sort .zero) => return DCC (`(ctx, &(Sort 0)))
  | .app (.const ``Shared _us) (.sort .zero) => return DCC (`(ctx, !(Sort 0)))
  | .app (.app (.const ``Shared.share _us) _α) (.sort (.succ m)) => do
    match ← (abstract' (.sort m) ctx infer reduce) with
    | DCC (`(ctx, &(Sort n)))
    | DCC (`(ctx, Sort n)) => return (DCC (`(ctx, &(Sort (n + 1)))))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | .app (.const ``Shared _us) (.sort (.succ m)) => do
    match ← (abstract' (.sort m) ctx infer reduce) with
    | DCC (`(ctx, !(Sort n)))
    | DCC (`(ctx, Sort n)) => return (DCC (`(ctx, !(Sort (n + 1)))))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | .app (.app (.const ``Shared.share _us) _α) (.const ``True.intro []) => return DCC (`(ctx, &(∗)))
  | .app (.const ``Shared _us) (.const ``False []) => return DCC (`(ctx, !(⊥)))
  | .bvar n => cc_var ctx n (infer := infer) (reduce := reduce)
  | .app (.app (.const ``Sigma []) α) β => do
    let α' ← abstract' α ctx infer reduce
    let β' ← abstract' β (DCC Coup(α')) infer reduce
    return (DCC Σ(α', β'))
  | .lam _a (.app (.const ``Shared _us) α) bdy _binfo => do
    let α' ← abstract' α ctx.deref infer reduce
    dbg_trace s!"α': {α'}"
    let inner ← abstract' bdy (DCC !(Coup(α'))) infer reduce
    dbg_trace s!"inner: {inner}"
    return (DCC !Λ(ctx.deref, α', inner))
  | .lam _a α bdy _binfo => do
    let α' ← abstract' α ctx infer reduce
    let inner ← abstract' bdy (DCC Coup(α')) infer reduce
    return (DCC Λ(ctx, α', inner))
  | .forallE _name (.app (.const ``Shared _us) α) β _binfo => do
    let α' ← reduce <$> abstract' α ctx infer reduce
    let β' ← reduce <$> abstract' β (DCC !(Coup(α'))) infer reduce

    return (reduce (DCC (Π(α', !Λ(ctx.deref, α', β')))))
  | .forallE _name α β _binfo => do
    let α' ← reduce <$> abstract' α ctx infer reduce
    let β' ← reduce <$> abstract' β (DCC Coup(α')) infer reduce

    return reduce (DCC (Π(α', Λ(ctx, α', β'))))
  | .app (.app (.app (.app (.app (.app (.const ``use _us) _α) _β) _γ) M) N) _
  | .app (.app (.app (.app (.app (.const ``use _us) _α) _β) _γ) M) N
  | .app M N => do
    let ctx' := match ctx with
      | DCC !(Γ) => Γ
      | Γ => Γ
    let M' ← abstract' M ctx' infer reduce
    let N' ← abstract' N ctx' infer reduce

    /-
      M : ∀ (x : α) (y : β x)
    -/

    match (·.fst) <$> infer.snd M' with
    | .some (_root_.Expr.app (.pi f_α f_β) x_α) =>
      let α : _root_.Expr := match reduce (f_α.app x_α) with
        | DCC !(α) => α
        | α => α
      match reduce (f_β.app x_α) with
      | DCC Π(β, _γ) =>
        match (·.fst) <$> infer.snd (DCC Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))) with
        | .some (DCC (Π(_f_α, f_β₀) x_α₀)) =>
          match reduce (DCC (f_β₀ x_α₀)) with
          | DCC Π(_β₂, x_γ') =>
            match (·.fst) <$> infer.snd (DCC ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩) with
            | .some (DCC (Π(_a₁, `(_a₂, Σ(_a₃, Λ(_a₄, _a₅, `(_α₆, _a₇))) ∘' _a₈)) _a₉)) =>
              return (DCC Eval(α, β, M') ∘ ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩)
            | .some (DCC (Π(_a₁, `(_a₂, `(_a₃, _a₄))) _a₅)) =>
              return (DCC Eval(α, β, M') ∘' ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩)
            | _ => return (DCC Eval(α, β, M') ∘∘ ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩)
          | _ => Lean.Macro.throwError ("app is not well-typed:"
            ++ Std.Format.line ++ (.nestD (Std.format (Lean.Expr.app M N)))
            ++ ("couldn't detect codomain:" ++ Std.Format.line ++ (.nestD (Std.format (reduce (DCC (f_β₀ x_α₀))))))).pretty
        | τ => Lean.Macro.throwError ("app is not well-typed [1]:" ++ Std.Format.line ++ (Std.format (Lean.Expr.app M N)) ++ Std.Format.line ++ "at: " ++ (Std.format τ)).pretty
      | τ => Lean.Macro.throwError ("app is not well-typed [2]:" ++ Std.Format.line ++
        (Std.format (Lean.Expr.app M N)) ++ Std.Format.line ++ "at: " ++ (Std.format τ)).pretty
    | x => Lean.Macro.throwError ("app is not well-typed [3]:" ++ Std.Format.line ++ (Std.format (Lean.Expr.app M N)) ++ Std.Format.line ++ "in: " ++ (Std.format (DCC (M' N'))) ++ Std.Format.line ++ "found: " ++ Std.format x).pretty
  | .const ``True.intro [] => return DCC (`(ctx, ∗))
  | .const ``True [] =>
    return DCC (`(ctx, Ctx.empty))
  | .const ``False [] => return DCC (`(ctx, ⊥))
  | .sort .zero => return DCC (`(ctx, Sort 0))
  | .sort (.succ m) => do
    match ← (abstract' (.sort m) ctx infer reduce) with
    | DCC (`(ctx, Sort n)) => pure (DCC (`(ctx, Sort (n + 1))))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | e => Lean.Macro.throwError s!"not a recognized expression: {e}"

def cc (root : Lean.Expr) (infer : ParamInfer) (reduce : Expr → Expr) : Lean.MacroM _root_.Expr :=
  match root with
  | .app (.const ``Shared _us) x => do
    let x' ← cc x infer reduce
    return DCC !(x')
  | .app (.app (.const ``Shared.share _us) _α) x => do
    let x' ← cc x infer reduce
    return DCC &(x')
  | .app (.lam _a α bdy _binfo) (.app (.app (.const ``Shared.share _us) _α) x) => do
    let f' ← abstract' (.lam _a α bdy _binfo) Ctx.empty infer reduce
    let x' ← cc x infer reduce
    return (DCC (f' &(∗) &(x')))
  | .app (.forallE _a α bdy _binfo) (.app (.app (.const ``Shared.share _us) _α) x) => do
    let f' ← abstract' (.forallE _a α bdy _binfo) Ctx.empty infer reduce
    let x' ← cc x infer reduce
    return (DCC (f' &(∗) &(x')))
  | .app (.lam _a α bdy _binfo) x => do
    let f' ← abstract' (.lam _a α bdy _binfo) Ctx.empty infer reduce
    let x' ← cc x infer reduce
    return (DCC (f' &(∗) x'))
  | .app (.forallE _a α bdy _binfo) x => do
    let f' ← abstract' (.forallE _a α bdy _binfo) Ctx.empty infer reduce
    let x' ← cc x infer reduce
    return (DCC (f' &(∗) x'))
  | .app M N => do
    let M' ← cc M infer reduce
    let N' ← cc N infer reduce
    match infer.snd M' with
    | .some ⟨DCC (Π(_f_α, _f_β) !(_b)), _h⟩ =>
      return (DCC (M' &(N')))
    | _ =>
      -- match infer M' to see if we need to wrap &(
      return (DCC (M' N'))
    /-match M' with
    | DCC (f &(x)) => return (DCC (f &(x) &(N')))
    | _ => return (DCC (M' N'))-/
  | .const ``True.intro [] => return DCC (∗)
  | .const ``True [] => return DCC (⊤)
  | .const ``False [] => return DCC (⊥)
  | .sort .zero => return DCC (Sort 0)
  | .sort (.succ m) => do
    match ← (cc (.sort m) infer reduce) with
    | DCC Sort n => pure (DCC Sort (n + 1))
    | m => Lean.Macro.throwError s!"not a valid sort: {m}"
  | e => (·.app (DCC (&(∗)))) <$> abstract' e Ctx.empty infer reduce

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
    let n_used := shared_in 0 bdy
    match n_used with
    | 0 => return .lam a bty' (← wrap_share_auto bdy) b
    | k =>
      let lv ← Lean.Meta.getLevel bty <|> Lean.Meta.mkFreshLevelMVar
      let bty' := wrap_shares k lv bty'
      let bdy' := deref_vars k 0 lv bty (← wrap_share_auto bdy)
      return .lam a bty' bdy' b
  | .forallE a bty bdy b => do
    let bty' ← wrap_share_auto bty
    let n_used := shared_in 0 bdy
    match n_used with
    | 0 => return .forallE a bty' (← wrap_share_auto bdy) b
    | k =>
      let lv ← Lean.Meta.getLevel bty'
      let bty' := wrap_shares k lv bty'
      let bdy' := deref_vars k 0 lv bty (← wrap_share_auto bdy)
      return .forallE a bty' bdy' b
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
      dbg_trace s!"fun: {M'}"
      try
        dbg_trace s!"type: {← Lean.Meta.inferType M'}"
        match ← Lean.Meta.inferType M' with
        | .forallE _ α _ _ =>
          dbg_trace α
          let ⟨lvl, n_shared, α⟩ := n_times_shared α
          match lvl with
          | .some lv =>
            let N'' := share_n_times n_shared lv α N'
            return .app M' N''
          | _ => return .app M' N'
        | _ =>
          throwError "panic"
      catch _ =>
        dbg_trace "hi"
        return .app M' N'
  | e => return e

open Qq in
def Lean.Expr.cc' {u : Lean.Level} {α : Q(Sort u)} (root : Q($α)) (infer : ParamInfer := ⟨Expr.Judge, Expr.infer⟩)
  (reduce : _root_.Expr → _root_.Expr := Expr.reduce_all) : Lean.MacroM _root_.Expr :=
  cc root (infer := infer) (reduce := reduce)

def Lean.Expr.ccM (root : Lean.Expr) (infer : ParamInfer := ⟨Expr.Judge, Expr.infer⟩) (reduce : _root_.Expr → _root_.Expr := Expr.reduce_all) : Lean.Elab.TermElabM (Option _root_.Expr) := do
  Elab.liftMacroM <| cc (← wrap_share_auto root) infer reduce

declare_syntax_cat infer_cmd_param

syntax "{" term "}" : infer_cmd_param

elab "dcc_compile'" infer:infer_cmd_param* tm:term : term => do
  let e_tm ← Lean.Elab.Term.elabTerm tm .none
  let e_tm' ← Lean.instantiateExprMVars =<< wrap_share_auto e_tm
  dbg_trace e_tm'
  match infer.toList with
  | [_infer] =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc e_tm' ⟨Expr.Judge₂, Expr.infer₂⟩ Expr.reduce_all)
  | [_infer, _reduce] =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc e_tm' ⟨Expr.Judge₂, Expr.infer₂⟩ Expr.reduce_all₂)
  | _ =>
    return Lean.toExpr (← Lean.Elab.liftMacroM <| cc e_tm' ⟨Expr.Judge, Expr.infer⟩ Expr.reduce_all)

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

#eval Std.format <| dcc_compile' {Expr.infer₂} ((fun (α : Sort 0) (x : α) => x) True True.intro)

#eval (DCC `(⊤, Sort 0)).infer₂'
#eval Sigma.fst <$> (DCC (`(Sort 1, (`(⊤, Sort 0) ∘' Fstc(`(⊤, Sort 0)))) Coup(`(⊤, Sort 0)))).red_eta??
#eval Std.format <| (DCC ((Π(Id(Sort 1), `(Sort 1, (`(⊤, Sort 0) ∘' Fstc(`(⊤, Sort 0))))) Coup(`(⊤, Sort 0))))).reduce_all₂
#eval Std.format <$> (DCC Sndc(`(⊤, Sort 0))).infer₂'
#eval Std.format <| (DCC Sndc(`(⊤, Sort 0))).infer₂'
#eval Std.format <| dcc_compile' {Expr.infer₂} (fun (α : Sort 0) (x : α) => x) True True.intro
#eval Std.format <| dcc_infer' {Expr.infer₂} (fun (α : Sort 0) (x : α) => x) True True.intro

#eval Std.format <| (DCC Id(Coup(`(⊤, Sort 0)))).infer₂'
#eval Std.format <| (DCC Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))),
                                        (Sndc(`(⊤, Sort 0)) ∘' Fstc(`(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))))))).infer'
#eval Std.format <| (DCC ⟦`(Coup(`(⊤, Sort 0)),
            `(Coup(`(⊤, Sort 0)),
              Sort 0))⟧⟨Id(Coup(`(⊤, Sort 0))),
                                      Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))),
                                        (Sndc(`(⊤, Sort 0)) ∘' Fstc(`(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))))))⟩).infer'

#eval Std.format <| (DCC Eval(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0),
            Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0), Sndc(`(Coup(`(⊤, Sort 0)), Sort 0))))).infer'

#eval Std.format <| (DCC ⟦`(Coup(`(⊤, Sort 0)),
            `(Coup(`(⊤, Sort 0)),
              Sort 0))⟧⟨Id(Coup(`(⊤, Sort 0))),
                                      Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))),
                                        (Sndc(`(⊤, Sort 0)) ∘' Fstc(`(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))))))⟩).infer'

#eval Std.format <| (DCC (Eval(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0),
            Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0), Sndc(`(Coup(`(⊤, Sort 0)), Sort 0)))) ∘'
       ⟦`(Coup(`(⊤, Sort 0)),
            `(Coup(`(⊤, Sort 0)),
              Sort 0))⟧⟨Id(Coup(`(⊤, Sort 0))),
                                      Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))),
                                        (Sndc(`(⊤, Sort 0)) ∘' Fstc(`(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))))))⟩)).infer₂'

#eval Std.format <| (DCC ⟦`(Coup(`(⊤, Sort 0)),
            `(Coup(`(⊤, Sort 0)),
              Sort 0))⟧⟨Id(Coup(`(⊤, Sort 0))),
                                      Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))),
                                        (Sndc(`(⊤, Sort 0)) ∘' Fstc(`(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))))))⟩).infer₂'
#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} (fun (x : Sort 0) => (fun (x : Sort 0) => x) x)
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} (fun (x : Sort 0) => (fun (x : Sort 0) => x) x)
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))
#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))
#eval Std.format <| (DCC (Π(Id(Sort (max 1 2)), `(Sort (max 1 2), Id(Sort 1) ∘' Fstc(`(Sort 1, Sort 1)))) Coup(`(Sort 1, Sort 1)))).reduce_all
#eval Std.format <| (DCC Sndc(`(⊤, Sort 2))).infer₂'
#eval Std.format <| (DCC (Π(Id(Sort 3), `(Sort 3, (`(⊤, Sort 2) ∘' Fstc(`(⊤, Sort 2))))) Coup(`(⊤, Sort 2)))).reduce_all
#eval (DCC Coup(Sndc(`(⊤, Sort 2)))).infer₂'
#eval Std.format <| (DCC Eval(Coup(Sndc(`(⊤, Sort 2))), (Sndc(`(⊤, Sort 2)) ∘' Fstc(Sndc(`(⊤, Sort 2)))),
                 Λ(Coup(Sndc(`(⊤, Sort 2))), (Sndc(`(⊤, Sort 2)) ∘' Fstc(Sndc(`(⊤, Sort 2)))),
                   Sndc((Sndc(`(⊤, Sort 2)) ∘' Fstc(Sndc(`(⊤, Sort 2))))))) ∘∘
            ⟦Λ(Coup(Sndc(`(⊤, Sort 2))), `(Coup(Sndc(`(⊤, Sort 2))), Coup(Sndc(`(⊤, Sort 2)))),
                 ((Sndc(`(⊤, Sort 2)) ∘' Fstc(Sndc(`(⊤, Sort 2)))) ∘'
                    Fstc(`(Coup(Sndc(`(⊤, Sort 2))),
                           Coup(Sndc(`(⊤,
                                       Sort 2)))))))⟧⟨Id(Coup(Sndc(`(⊤, Sort 2)))),
                                           Λ(Coup(Sndc(`(⊤, Sort 2))),
                                             `(Coup(Sndc(`(⊤, Sort 2))), Coup(Sndc(`(⊤, Sort 2)))),
                                             (Sndc(Sndc(`(⊤, Sort 2))) ∘'
                                                Fstc(`(Coup(Sndc(`(⊤, Sort 2))), Coup(Sndc(`(⊤, Sort 2)))))))⟩).infer₂'
#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))
#eval (Std.format ∘ Sigma.fst) <$> (DCC Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))).infer₂
-- Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))
#eval Std.format <| (DCC (`(Sort 1,
     `(Coup(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))))),
       Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))))) (Coup(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))).reduce_all₂
#eval Expr.toFormat (pretty := true) <$> (DCC Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))).infer₂'
#eval Std.format <| Sigma.fst <$> (DCC Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))).infer₂
#eval Std.format <| (DCC `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), !(⊤))).infer₂'
-- check if sharing is right
#check (fun (f : Shared.{0} (Prop -> Prop)) (x : (@Shared.deref.{0} (Prop -> Prop) f) True) => x) (@Shared.share.{0} (Prop -> Prop) (fun (x : Prop) => x))
--#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x))
/-dcc_trace (!Λ(⊤, Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))),
    Λ(!(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
      (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
              Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))) ∘∘
         ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
              `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                        Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                          `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                            Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                          (`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                               !(⊤)) ∘'
                                             Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                    Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩),
      Sndc((Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))) ∘∘
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0),
                                                           Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                    !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩))))
   &(∗))
#eval (DCC (!Λ(⊤, Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))),
    Λ(!(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
      (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
              Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))) ∘∘
         ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
              `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                        Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                          `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                            Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                          (`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                               !(⊤)) ∘'
                                             Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                    Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩),
      Sndc((Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))) ∘∘
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0),
                                                           Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                    !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩))))
   &(∗))).infer₂'-/

dcc_trace Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))

#eval Std.format <| (DCC Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))).infer₂'
dcc_trace' ? (!Λ(⊤, Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))),
    Λ(!(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
      (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
              Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘∘
         ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
              `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                        Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                          `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                            Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                          (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                             Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                    Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩),
      Sndc((Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘∘
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩)))))

/-#eval (DCC (!Λ(⊤, Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))),
    Λ(!(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
      (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
              Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘∘
         ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
              `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                        Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                          `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                            Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                          (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                             Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                    Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩),
      Sndc((Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘∘
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩)))))).infer₂'-/

#eval Std.format <| (DCC (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
              Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘'
         ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
              `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                        Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                          `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                            Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                          (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                             Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                    Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩)).infer₂'

#eval Std.format <| (DCC (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘'
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩)).infer₂'

#eval (do return (← ((DCC Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
        Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘∘
   ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
        `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
          Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                  Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                    `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                      Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                    (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                       Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                              Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩).to_eta_expr).fst.domain?).fst)

#eval Std.format <| (DCC ((Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
        Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘∘
   ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
        `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
          Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                  Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                    `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                      Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                    (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                       Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                              Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩) &(⟦Sort 1⟧(⟦Sort 2⟧(Sort 0, Sort 1), Sort 3)))).reduce_all₂

#eval Std.format <| (DCC (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘∘
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩)).reduce_all₂
/-
Sndc((Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘∘
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩))

However, this is a quotation.

this is problematic. we're evaluating in a pair to do (f True)

this requires flipping the order. sndc doesn't like that.

a flip combinator could get around this, maybe.
Still though. Eval inside sndc.... can we eta reduce?

maybe we can make a function codomain to check output type? idk.

`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Sort 0, Sort 0))

this says it is an arrow. we can just blindly add to eval.

γ is constant.

why does γ receive two arguments?
yes.
Eval(.., ..., 

(Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Sort 0, Sort 0)))
-/

#eval Std.format <| (DCC (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘'
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩)).infer₂'

#eval Std.format <$> (DCC Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘'
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩).infer₂'

#eval (DCC Sndc((Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
                   Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘'
              ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                   `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                     Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                             Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                               `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                 Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                               (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                                  Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                         Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩))).infer₂'

#eval Std.format <| (DCC (Eval(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), Sort 0),
              Sndc(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))) ∘'
         ⟦`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
              `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                        Λ(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                          `(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                            Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))),
                                          (`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))), !(⊤)) ∘'
                                             Fstc(`(Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))),
                                                    Coup(Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))))))))⟩)).infer₂'
#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x) (fun x => x))
#eval Std.format <| (DCC &((Λ(!(⊤), `(!(⊤), Sort 0), Sndc(`(!(⊤), Sort 0))) &(∗)))).infer₂'
#eval Std.format <| (DCC (Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0))) ∗)).reduce_all₂
#eval Std.format <| (DCC &((Λ(!(⊤), `(⊤, Sort 0), Sndc(`(⊤, Sort 0))) &(∗)))).infer₂'
#eval Std.format <| (DCC (!<Π(`(⊤, Sort 0), `(⊤, `(Sort 0, Sort 0)))> &(∗))).reduce_all₂
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x))
#eval (Std.format ∘ Sigma.fst) <$> (DCC Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))).infer₂
#eval Std.format <| (DCC Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))).reduce_all₂



#eval Expr.toFormat (pretty := True) <$> (DCC Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))).infer₂'

/-

#eval (Std.format ∘ Sigma.fst) <$> (DCC Eval(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0),
            Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Sort 0), Sndc(`(Coup(`(⊤, Sort 0)), Sort 0))))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC ⟦`(Coup(`(⊤, Sort 0)),
            `(Coup(`(⊤, Sort 0)),
              Sort 0))⟧⟨Id(Coup(`(⊤, Sort 0))),
                                      Λ(Coup(`(⊤, Sort 0)), `(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))),
                                        (Sndc(`(⊤, Sort 0)) ∘' Fstc(`(Coup(`(⊤, Sort 0)), Coup(`(⊤, Sort 0))))))⟩).infer

#eval Std.format <| dcc_compile' (fun (x : Sort 0) => (fun (x : Sort 0) => x) x)
#eval Std.format <| dcc_infer' ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))
#eval Std.format <| dcc_infer' ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))
#eval Std.format <| dcc_compile' ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))
#eval Std.format <| dcc_infer' ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))
#eval Std.format <| dcc_compile' ((fun (f : Sort 0 → Sort 0) (x : f True) => x) (fun (x : Sort 0) => x) True.intro)

#eval (Std.format ∘ Sigma.fst) <$> (DCC Eval(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
        (`(⊤, Sort 0)∘'Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
        Sndc(Π(`(⊤, Sort 0),
            Λ(⊤, `(⊤, Sort 0),
              `(Coup(`(⊤, Sort 0)),
                Sort
                  0)))))).infer

-- rule for this
#eval Std.format <| (DCC Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))).reduce_all
#eval Std.format <| (DCC (Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)) ∘'
             Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))).reduce_all

-- turns this into a quotation
/-
(Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)) ∘'
             Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))
-/

/-
η rules for pair are right, but need refinement

Λ(..., ..., `(...)) ∘' Fstc

Fstc is only applying to first argument.

Λ part is destructing order is reversed in rule.
Λ dictates what to do.
-/

#eval (Std.format ∘ Sigma.fst) <$> (DCC ⟦Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
          `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
            Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
          `(Coup(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))),
            Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
        Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
          `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
            Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
          (`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                !(⊤))∘'Fstc(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                  Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))))))⟩).infer

#eval (Std.format ∘ Sigma.fst) <$> (DCC Eval(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
        (`(⊤, Sort 0)∘'Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
        Sndc(Π(`(⊤, Sort 0),
            Λ(⊤, `(⊤, Sort 0),
              `(Coup(`(⊤, Sort 0)),
                Sort
                  0)))))∘⟦Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
          `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
            Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
          `(Coup(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))),
            Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
        Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
          `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
            Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
          (`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                !(⊤))∘'Fstc(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                  Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))))))⟩).infer

dcc_trace (((!Λ(⊤, Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))),
      Λ(!(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
        (Eval(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                (`(⊤, Sort 0) ∘' Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))) ∘
           ⟦Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                  Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                `(Coup(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                         Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))),
                  Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                                          Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                            `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                              Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                                            (`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                 !(⊤)) ∘'
                                               Fstc(`(Coup(Π(`(⊤, Sort 0),
                                                             Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                      Coup(Π(`(⊤, Sort 0),
                                                             Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))))))⟩),
        Sndc((Eval(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                     (`(⊤, Sort 0) ∘' Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                     Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))) ∘
                ⟦Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                     `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                       Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                     `(Coup(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                              Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))),
                       Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                                               Λ(Coup(Π(`(⊤, Sort 0),
                                                        Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                 `(Coup(Π(`(⊤, Sort 0),
                                                          Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                   Coup(Π(`(⊤, Sort 0),
                                                          Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                                                 (`(Coup(Π(`(⊤, Sort 0),
                                                             Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                      !(⊤)) ∘'
                                                    Fstc(`(Coup(Π(`(⊤, Sort 0),
                                                                  Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                           Coup(Π(`(⊤, Sort 0),
                                                                  Λ(⊤, `(⊤, Sort 0),
                                                                    `(Coup(`(⊤, Sort 0)), Sort 0))))))))⟩))))
     &(∗))
    &((Λ(!(⊤), `(⊤, Sort 0), Sndc(`(⊤, Sort 0))) &(∗))))
   ∗)

/-dcc_trace (((!Λ(⊤, Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))),
      Λ(!(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
        (Eval(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                (`(⊤, Sort 0) ∘' Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))) ∘
           ⟦Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                  Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                `(Coup(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                         Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))),
                  Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                                          Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                            `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                              Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                                            (`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                 !(⊤)) ∘'
                                               Fstc(`(Coup(Π(`(⊤, Sort 0),
                                                             Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                      Coup(Π(`(⊤, Sort 0),
                                                             Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))))))⟩),
        Sndc((Eval(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                     (`(⊤, Sort 0) ∘' Fstc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                     Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))) ∘
                ⟦Λ(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                     `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                       Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                     `(Coup(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                              Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))))),
                       Sort 0))⟧⟨Id(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                                               Λ(Coup(Π(`(⊤, Sort 0),
                                                        Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                 `(Coup(Π(`(⊤, Sort 0),
                                                          Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                   Coup(Π(`(⊤, Sort 0),
                                                          Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))),
                                                 (`(Coup(Π(`(⊤, Sort 0),
                                                             Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                      !(⊤)) ∘'
                                                    Fstc(`(Coup(Π(`(⊤, Sort 0),
                                                                  Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
                                                           Coup(Π(`(⊤, Sort 0),
                                                                  Λ(⊤, `(⊤, Sort 0),
                                                                    `(Coup(`(⊤, Sort 0)), Sort 0))))))))⟩))))
     &(∗))
    &((Λ(!(⊤), `(⊤, Sort 0), Sndc(`(⊤, Sort 0))) &(∗))))
   ∗)-/

/-dcc_trace (Sndc(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))
   `(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), !(⊤)))

#eval Std.format <| (DCC (!<(Sndc(`(!(⊤), Sort 2)) ∘' *(Coup(`(!(⊤), Sort 2))))> &(⟦`(!(⊤), Sort 2)⟧(∗, Sort 1)))).reduce_all
#eval Std.format <| dcc_infer' ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1))
#eval Std.format <| dcc_compile' ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))

#eval Std.format <| dcc_compile (fun (α : Sort 0) (x : α) => x) True True.intro
#time #eval dcc_infer   (fun (α : Sort 0) (x : α) => x) True True.intro
#eval Std.format <| dcc_compile (fun (x : *(Sort 0)) => (fun (x : Sort 0) => x) x.deref)
#time #eval Std.format <| dcc_infer (((fun (x : *(Sort 1)) => (fun (x : Sort 1) => x) ↑(x))) &(Sort 0))

#eval (Std.format ∘ Sigma.fst) <$> (DCC *(Coup(`(!(⊤), Sort 1)))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC Sndc(`(!(⊤), Sort 1))).infer-/
-/
