import Dcc.Judge
import Dcc.Tactic.Debug

inductive Shared.{u} (α : Type u) where
  | share : α → Shared α
deriving Lean.ToExpr

def Shared.deref (s : Shared α) : α :=
  match s with
  | ⟨s⟩ => s

#check Shared.deref

def use.{u, v, s} {α : Type u}
  {β : α → Type v} {γ : ∀ (x : α), (β x) → Type s} (f : ∀ (x : α) (y : β x), γ x y)
  (g : ∀ (x : α), β x) : ∀ (x : Shared α), γ x.deref (g x.deref) := fun x =>
  f x.deref (g x.deref)

open Shared

def Ctx := Expr
def Ctx.empty := DCC !(⊤)

def Expr.deref : Expr → Expr
  | DCC !(Γ) => Γ
  | Γ => Γ

def cc_var (ctx : Ctx) (idx : ℕ) : Option Expr :=
  match ctx, idx with
  | DCC Coup(β), .zero => pure <| DCC Sndc(β)
  | DCC !(Coup(β)), .zero => pure <| DCC Sndc(β) ∘' *(Coup(β))
  | DCC !(Coup(β)), .succ n => do
    match (← β.infer).fst with
    | DCC (Π(a, _b) x_α) =>
      (·.comp' (DCC (Fstc(β)) ∘' !(Coup(β)))) <$> cc_var (DCC (a x_α)).reduce_all n
    | _ => .none
  | DCC Coup(β), .succ n => do
    match (← β.infer).fst with
    | DCC (Π(a, _b) x_α) =>
      (·.comp' (DCC (Fstc(β)))) <$> cc_var (DCC (a x_α)).reduce_all n
    | _ => .none
  | _, _ => .none

/-
TODO: better logic for detecting duplication. Maybe some kind of user marker.

-/

def abstract' (e : Lean.Expr) (ctx : Ctx) : Option _root_.Expr :=
  match e with
  | .app (.app (.const ``Shared.deref _us) _α) x => abstract' x ctx
  | .app (.app (.const ``Shared.share _us) _α) (.sort .zero) => DCC (`(ctx, &(Sort 0)))
  | .app (.const ``Shared _us) (.sort .zero) => DCC (`(ctx, !(Sort 0)))
  | .app (.app (.const ``Shared.share _us) _α) (.sort (.succ m)) => do
    match ← (abstract' (.sort m)) ctx with
    | DCC (`(ctx, &(Sort n)))
    | DCC (`(ctx, Sort n)) => pure (DCC (`(ctx, &(Sort (n + 1)))))
    | _ => .none
  | .app (.const ``Shared _us) (.sort (.succ m)) => do
    match ← (abstract' (.sort m)) ctx with
    | DCC (`(ctx, !(Sort n)))
    | DCC (`(ctx, Sort n)) => pure (DCC (`(ctx, !(Sort (n + 1)))))
    | _ => .none
  | .app (.app (.const ``Shared.share _us) _α) (.const ``True.intro []) => DCC (`(ctx, &(∗)))
  | .app (.const ``Shared _us) (.const ``False []) => DCC (`(ctx, !(⊥)))
  | .bvar n => cc_var ctx n
  | .app (.app (.const ``Sigma []) α) β => do
    let α' ← abstract' α ctx
    let β' ← abstract' β (DCC Coup(α'))
    .some (DCC Σ(α', β'))
  | .lam _a (.app (.const ``Shared _us) α) bdy _binfo => do
    let α' ← abstract' α ctx
    let inner ← abstract' bdy (DCC !(Coup(α')))
    .some (DCC !Λ(ctx.deref, α', inner))
  | .lam _a α bdy _binfo => do
    let α' ← abstract' α ctx
    let inner ← abstract' bdy (DCC Coup(α'))
    .some (DCC Λ(ctx, α', inner))
  | .forallE _name (.app (.const ``Shared _us) α) β _binfo => do
    let α' ← abstract' α ctx
    let β' ← abstract' β (DCC !(Coup(α')))

    .some (DCC (Π(α', !Λ(ctx.deref, α', β'))))
  | .forallE _name α β _binfo => do
    let α' ← abstract' α ctx
    let β' ← abstract' β (DCC Coup(α'))

    .some (DCC (Π(α', Λ(ctx, α', β'))))
  | .app (.app (.app (.app (.app (.app (.const ``use _us) _α) _β) _γ) M) N) _
  | .app (.app (.app (.app (.app (.const ``use _us) _α) _β) _γ) M) N
  | .app M N => do
    let ctx' := match ctx with
      | DCC !(Γ) => Γ
      | Γ => Γ
    let M' ← abstract' M ctx'
    let N' ← abstract' N ctx'

    /-
      M : ∀ (x : α) (y : β x)
    -/

    match (← M'.infer).fst with
    | _root_.Expr.app (.pi f_α f_β) x_α =>
      let α : _root_.Expr := match (f_α.app x_α).reduce_all with
        | DCC !(α) => α
        | α => α
      match (f_β.app x_α).reduce_all with
      | DCC Π(β, _γ) =>
        match (← (DCC Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))).infer).fst with
        | DCC (Π(_f_α, f_β₀) x_α₀) =>
          match (DCC (f_β₀ x_α₀)).reduce_all with
          | DCC Π(_β₂, x_γ') =>
            .some (DCC Eval(α, β, M') ∘ ⟦x_γ'⟧⟨Id(α), Λ(α, `(α, α), N' ∘' Fstc(`(α, α)))⟩)
          | _ => .none
        | _ => .none
      | _ => .none
    | _ => .none
  | .const ``True.intro [] => DCC (`(ctx, ∗))
  | .const ``True [] => DCC (`(ctx, Ctx.empty))
  | .const ``False [] => DCC (`(ctx, ⊥))
  | .sort .zero => DCC (`(ctx, Sort 0))
  | .sort (.succ m) => do
    match ← (abstract' (.sort m)) ctx with
    | DCC (`(ctx, Sort n)) => pure (DCC (`(ctx, Sort (n + 1))))
    | _ => .none
  | _ => .none

def cc (root : Lean.Expr) : Option _root_.Expr :=
  match root with
  | .app (.const ``Shared _us) x => do
    let x' ← cc x
    .some (DCC !(x'))
  | .app (.app (.const ``Shared.share _us) _α) x => do
    let x' ← cc x
    .some (DCC &(x'))
  | .app (.lam _a α bdy _binfo) (.app (.app (.const ``Shared.share _us) _α) x) => do
    let f' ← abstract' (.lam _a α bdy _binfo) Ctx.empty
    let x' ← cc x
    .some (DCC (f' &(∗) &(x')))
  | .app (.lam _a α bdy _binfo) x => do
    let f' ← abstract' (.lam _a α bdy _binfo) Ctx.empty
    let x' ← cc x
    .some (DCC (f' &(∗) x'))
  | .app M N => do
    let M' ← cc M
    let N' ← cc N
    .some (DCC (M' N'))
  | .const ``True.intro [] => DCC (∗)
  | .const ``True [] => DCC (⊤)
  | .const ``False [] => DCC (⊥)
  | .sort .zero => DCC (Sort 0)
  | .sort (.succ m) => do
    match ← (cc (.sort m)) with
    | DCC Sort n => pure (DCC Sort (n + 1))
    | _ => .none
  | e => (·.app (DCC (&(∗)))) <$> abstract' e Ctx.empty

open Qq in
def Lean.Expr.cc' {u : Lean.Level} {α : Q(Sort u)} (root : Q($α)) : Option _root_.Expr :=
  cc root

open Qq in
#eval Lean.Expr.cc' q(λ (x : Sort 1) => x)

open Qq in
#eval (do Sigma.fst <$> (← (Lean.Expr.cc' q((λ (α : Sort 0) => λ (x : α) => x) True True.intro))).infer)

syntax "dcc_compile" term : term
syntax "dcc_infer" term   : term

open Qq in
macro_rules
  | `(dcc_compile $tm:term) => `((Lean.Expr.cc' q($tm:term)))
  | `(dcc_infer $tm:term) => `((do Sigma.fst <$> (← (Lean.Expr.cc' q($tm:term))).infer))

#eval Std.format <| dcc_compile (fun (α : Sort 0) (x : α) => x) True True.intro
#eval dcc_infer   (fun (α : Sort 0) (x : α) => x) True True.intro
#eval Std.format <| dcc_compile (fun (x : Shared (Sort 0)) => (fun (x : Sort 0) => x) x.deref)
#eval Std.format <| dcc_infer (((fun (x : Shared (Sort 1)) => (fun (x : Sort 1) => x) x.deref)) (share (Sort 0)))

