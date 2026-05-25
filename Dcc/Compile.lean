import Dcc.Ast
import Dcc.Types
import Dcc.Judge
--import Dcc.Debug
import Lean
import Qq
open Qq

def Ctx := Expr

def Ctx.empty := DCC ⊤

def cc_var (ctx : Ctx) (idx : ℕ) : Option Expr :=
  match ctx, idx with
  | DCC Coup(β), .zero => pure <| DCC Sndc(β)
  | DCC Coup(β), .succ n => do
    match (← β.infer).fst with
    | DCC (Π(a, _b) x_α) =>
      (·.comp' (DCC (Fstc(β)))) <$> cc_var (DCC (a x_α)).reduce_all n
    | _ => .none
  | _, _ => .none

def abstract' (e : Lean.Expr) (ctx : Ctx) : Option _root_.Expr :=
  match e with
  | .bvar n => cc_var ctx n
  | .app (.app (.const ``Sigma []) α) β => do
    let α' ← abstract' α ctx
    let β' ← abstract' β (DCC Coup(α'))
    .some (DCC Σ(α', β'))
  | .lam _a α bdy _binfo => do
    let α' ← abstract' α ctx
    let inner ← abstract' bdy (DCC Coup(α'))
    .some (DCC Λ(ctx, α', inner))
  | .forallE _name α β _binfo => do
    let α' ← abstract' α ctx
    let β' ← abstract' β (DCC Coup(α'))

    .some (DCC (Π(α', Λ(ctx, α', β'))))
  | .app M N => do
    let M' ← abstract' M ctx
    let N' ← abstract' N ctx

    match (← M'.infer).fst with
    | _root_.Expr.app (.pi f_α f_β) x_α =>
      let α : _root_.Expr := (f_α.app x_α).reduce_all
      match (f_β.app x_α).reduce_all with
      | DCC Π(_f_β, _γ) =>
        .some (DCC ⟨Id(α), Λ(α, `(α, α), ⟨N', M'⟩ ∘' Fstc(`(α, α)))⟩)
      | _ => .none
    | _ => .none
  | .const ``True.intro [] => DCC (`(ctx, ∗))
  | .const ``True [] => DCC (`(ctx, ⊤))
  | .const ``False [] => DCC (`(ctx, ⊥))
  | .sort .zero => DCC (`(ctx, Sort 0))
  | .sort (.succ m) => do
    match ← (abstract' (.sort m)) ctx with
    | DCC (`(ctx, Sort n)) => pure (DCC (`(ctx, Sort (n + 1))))
    | _ => .none
  | _ => .none

def cc (root : Lean.Expr) : Option _root_.Expr :=
  match root with
  | .app (.lam _a α bdy _binfo) x => do
    let f' ← abstract' (.lam _a α bdy _binfo) Ctx.empty
    let x' ← cc x
    .some (DCC (f' ∗ x'))
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
  | e => (·.app .tintro) <$> abstract' e Ctx.empty

def Lean.Expr.cc' {u : Lean.Level} {α : Q(Sort u)} (root : Q($α)) : Option _root_.Expr :=
  cc root

#eval Lean.Expr.cc' q(λ (x : Sort 1) => x)

#eval (do Sigma.fst <$> (← (Lean.Expr.cc' q((λ (α : Sort 0) => λ (x : α) => x) True True.intro))).infer)

syntax "dcc_compile" term : term
syntax "dcc_infer" term   : term

macro_rules
  | `(dcc_compile $tm:term) => `((Lean.Expr.cc' q($tm:term)))
  | `(dcc_infer $tm:term) => `((do Sigma.fst <$> (← (Lean.Expr.cc' q($tm:term))).infer))

#eval dcc_compile (fun (α : Sort 0) (x : α) => x) True True.intro
#eval dcc_infer   (fun (α : Sort 0) (x : α) => x) True True.intro

#eval dcc_compile (fun (f : Sort 0 → Sort 0) (x : Sort 0) => f x)
