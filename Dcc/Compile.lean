import Dcc.Ast
import Dcc.Judge

inductive LExpr where
  | idx   : ℕ     → LExpr
  | lam   : LExpr → LExpr → LExpr
  | forE  : LExpr → LExpr → LExpr
  | app   : LExpr → LExpr → LExpr
  | sort  : Level → LExpr
  | sigma : LExpr → LExpr → LExpr

def Ctx := Expr

/-
There is always an environment.
Debruijn index 1 corresponds to snd,
and pushing onto the context is Λ.
-/
def Ctx.empty := DCC ⊤

def mk_lookup (ctx : Ctx) (idx : ℕ) : Option Expr :=
  match ctx, idx with
  | DCC (Σ(`(Sort _m, β)) _α), .zero => pure <| DCC Sndc(β)
  -- Singleton context
  | DCC (Σ(`(Sort _m, β)) α), .succ n => (Expr.comp · (DCC Fstc(β))) <$> mk_lookup α n
  | _, _ => .none

/-
Snd is our debruijn index 1 because we always have an environment.

empty ctx: ⊤.

-/

/-
λ (x : α) → λ (y : β x) → x = Λ(α, β, Fstc(m, α, β))

type might depend on any number of arguments in scope.

λ (: α) → λ (: β 0) → x

Ctx.push, just compile type with previous context as context,

ctx₀

ctx at inner x is Coup(m, α, β)
-/
--def Ctx.push (ctx : Ctx) (

declare_syntax_cat lexpr

syntax "Sort" term              : lexpr
syntax "v" ident                : lexpr
syntax num                      : lexpr
syntax "#(" term ")"            : lexpr
syntax "λ" ":" lexpr "→" lexpr  : lexpr
syntax "∀" ":" lexpr "," lexpr  : lexpr
syntax "Σ" ":" lexpr "," lexpr  : lexpr
syntax:30 ident                 : lexpr
syntax "(" lexpr+ ")"           : lexpr

syntax "DLCC" lexpr : term

macro_rules
  | `(DLCC Sort $m:term) => `(LExpr.sort $m)
  | `(DLCC v $idt:ident) => `(LExpr.idx $idt)
  | `(DLCC $n:num) =>
    let n' := Lean.Syntax.mkNatLit n.getNat
    `(LExpr.idx $n')
  | `(DLCC λ :$α:lexpr → $x:lexpr) =>
    `(LExpr.lam (DLCC $α) (DLCC $x))
  | `(DLCC ∀ :$α:lexpr, $x:lexpr)   =>
    `(LExpr.forE (DLCC $α) (DLCC $x))
  | `(DLCC Σ :$α:lexpr, $x:lexpr)   =>
    `(LExpr.sigma (DLCC $α) (DLCC $x))
  | `(DLCC ($f:lexpr $x:lexpr))     =>
    `(LExpr.app (DLCC $f:lexpr) (DLCC $x:lexpr))
  | `(DLCC ($f:lexpr $x:lexpr $xs:lexpr*)) =>
    `(DLCC (($f:lexpr $x:lexpr) $xs:lexpr*))
  | `(DLCC #($t:term)) => `($t)
  | `(DLCC $idt:ident) => `($idt:term)
  | `(DLCC ($t:lexpr)) => `(DLCC $t)

/-
This is just bracket abstraction
-/

def push_ctx_β (ctx : Ctx) (t_α α' : Expr) : Option Expr :=
  match t_α with
  | DCC Sort _m =>
    -- Does not depend on environment
    .some <| DCC `(ctx, α')
  | DCC (Λ(_n, _f_α, _f_β) _env) =>
    -- Does depend on environment, so feed it the environment
    .some <| DCC t_α
  | _ => .none

def LExpr.compile (bdy : LExpr) (ctx : Ctx) : Option Expr :=
  match bdy with
  | .idx n =>
    mk_lookup ctx n
  | DLCC Sort m => .some (DCC Sort m)
  | DLCC Σ : α, β => do
    /-
      α and β might depend on the environment.
      also, β might depend on α.
      luckily, DCC Σ works perfectly for this
      Σ(f_β) env
      we don't actually care about α, except to get
      the context to compile β
    -/
    let α' ← α.compile ctx
    let ⟨t_α, _⟩ ← α'.infer
    let ctx'_β ← push_ctx_β ctx t_α α'
    let ctx' := DCC Coup(ctx'_β)
    let β' ← β.compile ctx'
    .some (DCC Σ(β'))
  | DLCC (λ : α → bdy) => do
    -- how to append context?
    /-
      α may depend on env, so we compile it
      then we can infer to see if it depends on the environment. e.g.,
      λ (α : Sort m) → λ (y : α) → y
    -/
    let α' ← α.compile ctx
    let ⟨t_α, _⟩ ← α'.infer
    let ctx'_β ← push_ctx_β ctx t_α α'
    let ctx' := DCC Coup(ctx'_β)
    let inner ← bdy.compile ctx'
    .some (DCC Λ(ctx, ctx'_β, inner))
  | DLCC (∀ : α, bdy) => do
    let α' ← α.compile ctx
    let ⟨t_α, _⟩ ← α'.infer
    let ctx'_β ← push_ctx_β ctx t_α α'
    let ctx' := DCC Coup(ctx'_β)
    let inner ← bdy.compile ctx'
    let ⟨β, _⟩ ← inner.infer
    match t_α with
    | (DCC Sort m) =>
      .some (DCC (Π(Id(Sort m), β) α'))
    | (DCC (Π(_a, _b) _env)) =>
      .some (DCC (Π(t_α, β)))
    | _ => .none
  | DLCC (M N) => do
    let M' ← M.compile ctx
    let N' ← M.compile ctx

    match (← M'.infer).fst with
    | DCC (Π(f_α, f_β) x_α) =>
      let α := (DCC (f_α x_α)).reduce_all

      match (DCC (f_β x_α)).reduce_all with
      | DCC (Π(_f_β, γ)) =>
        /-
          ⟨N, M⟩ x = ⟨Id(α), Snd(γ) ∘ ⟨N, M⟩⟩ x = (x, (N x, M x (N x)) x)
          ⟨?, Snd(γ)⟩ x = (? x, Snd(γ) x ?)
          ⟨⟨N, M⟩, Snd(γ)⟩
          ⟨⟨N, M⟩, Snd(γ)⟩ x = ((N x, M x (N x)), Snd(γ) x (N x, M x (N x)))
          = (..., M x (N x))


          ⟨⟨N, M⟩, Snd(γ)⟩
          (M N) = ⟨Id(α), ⟨
        -/

        .some (DCC (Sndc(#(sorry)) ∘ ⟨sorry
      | _ => .none
    | _ => .none

/-
TODO:
- always initialize env. with unit ∗
-/
