import Dcc.Ast
import Dcc.Types
import Dcc.Judge
import Dcc.Debug
import Lean
import Qq
open Qq

def Ctx := Expr

/-
There is always an environment.
Debruijn index 1 corresponds to snd,
and pushing onto the context is Λ.
-/
def Ctx.empty := DCC ⊤

/-
Should be using subst here instead?
Fstc should be nondependent anyway.


-/
def mk_lookup (ctx : Ctx) (idx : ℕ) : Option Expr :=
  match ctx, idx with
  | DCC Coup(β), .zero => pure <| DCC Sndc(β)
  -- Singleton context
  | DCC Coup(β), .succ n => do
    -- β is a function of fst
    match (← β.infer).fst with
    | DCC (Π(a, _b) x_α) =>
      let ctx' := (DCC (a x_α)).reduce_all
      (·.comp (DCC (Fstc(β)))) <$> mk_lookup ctx' n
    | _ => .none
  | _, _ => .none

open Lean Qq in def Lean.Expr.abstract' (e : Lean.Expr) (ctx : Ctx) : Option _root_.Expr :=
  match e with
  | .bvar n => mk_lookup ctx n
  | .app (.app (.const ``Sigma []) α) β => do
    let α' ← Lean.Expr.abstract' α ctx
    let β' ← Lean.Expr.abstract' β (DCC Coup(α'))
    .some (DCC Σ(β'))
  | .lam _a α bdy _binfo => do
    let α' ← Lean.Expr.abstract' α ctx
    let inner ← Lean.Expr.abstract' bdy (DCC Coup(α'))
    .some (DCC Λ(ctx, α', inner))
  | .forallE _name α β _binfo => do
    let α' ← Lean.Expr.abstract' α ctx
    let β' ← Lean.Expr.abstract' β (DCC Coup(α'))

    .some (DCC (Π(α', Λ(ctx, α', β'))))
  | .app M N => do
    let M' ← Lean.Expr.abstract' M ctx
    let N' ← Lean.Expr.abstract' N ctx

    match (← M'.infer).fst with
    | DCC (Π(f_α, f_β) x_α) =>
      let α := (DCC (f_α x_α)).reduce_all

      match (DCC (f_β x_α)).reduce_all with
      | DCC Π(_f_β, γ) =>
        /-
          ⟨N, M⟩ x = ⟨Id(α), Snd(γ) ∘ ⟨N, M⟩⟩ x = (x, (N x, M x (N x)) x)
          ⟨?, Snd(γ)⟩ x = (? x, Snd(γ) x ?)
          ⟨⟨N, M⟩, Snd(γ)⟩
          ⟨⟨N, M⟩, Snd(γ)⟩ x = ((N x, M x (N x)), Snd(γ) x (N x, M x (N x)))
          = (..., M x (N x))


          ⟨⟨N, M⟩, Snd(γ)⟩
          (N x, M x (N x))
          (M N) = Subst(Snd(γ), Sndc(Σ(γ))) ∘ ⟨Id(α), `(α, ⟨N, M⟩)⟩
        -/
        dbg_trace Sigma.fst <$> N'.infer
        dbg_trace Sigma.fst <$> M'.infer
        dbg_trace M'
        dbg_trace Sigma.fst <$> (DCC ⟨N', M'⟩).infer

        .some (DCC Subst(Snd(γ), Sndc(Σ(γ))) ∘ ⟨Id(α), `(α, ⟨N', M'⟩)⟩)
      | _ => .none
    | _ => .none
  | .const ``True.intro [] => DCC (`(ctx, ∗))
  | .const ``True [] => DCC (`(ctx, ⊤))
  | .const ``False [] => DCC (`(ctx, ⊥))
  | .sort .zero => DCC (`(ctx, Sort 0))
  | .sort (.succ m) => do
    match ← (Lean.Expr.abstract' (.sort m)) ctx with
    | DCC (`(ctx, Sort n)) => pure (DCC (`(ctx, Sort (n + 1))))
    | _ => .none
  | _ => .none

def Lean.Expr.cc (root : Lean.Expr) : Option _root_.Expr :=
  match root with
  | .app (.lam _a α bdy _binfo) x => do
    let ctx₀ := Ctx.empty
    let f' ← Lean.Expr.abstract' (.lam _a α bdy _binfo) ctx₀
    let x' ← Lean.Expr.cc x
    .some (DCC (f' ∗ x'))
  | .app M N => do
    let M' ← Lean.Expr.cc M
    let N' ← Lean.Expr.cc N
    .some (DCC (M' N'))
  | .const ``True.intro [] => DCC (∗)
  | .const ``True [] => DCC (⊤)
  | .const ``False [] => DCC (⊥)
  | .sort .zero => DCC (Sort 0)
  | .sort (.succ m) => do
    match ← (Lean.Expr.cc (.sort m)) with
    | DCC Sort n => pure (DCC Sort (n + 1))
    | _ => .none
  | e => (·.app .tintro) <$> Lean.Expr.abstract' e Ctx.empty

def Lean.Expr.cc' {u : Lean.Level} {α : Q(Sort u)} (root : Q($α)) : Option _root_.Expr :=
  Lean.Expr.cc root

#eval Lean.Expr.cc' q(λ (x : Sort 1) => x)

#eval (do Sigma.fst <$> (← (Lean.Expr.cc' q((λ (α : Sort 0) => λ (x : α) => x) True True.intro))).infer)
