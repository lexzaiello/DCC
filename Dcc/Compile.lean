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
    match M'.infer, N'.infer with
    -- Need to handle nondependent case as well
    | .some ⟨DCC (Π(f_α₁, Λ(Sort m, f_α', Π(f_β, f_γ))) env), ⟨ht₁⟩⟩,
      .some ⟨DCC (Π(f_α₂, Nβ) env), ⟨ht₂⟩⟩ =>
      let elim_sort ← match (DCC (Π(f_α₁, Λ(Sort m, f_α', Π(f_β, f_γ))) env)).infer with
        | DCC Sort n => .some <| DCC Sort n
        | _ => .none
      let α  := (DCC (f_α₁ env)).reduce
      let Mβ := DCC Λ(Sort m, f_α', Π(f_β, f_γ))

      let pair_MN := DCC ⟦m, α, Mβ, Nβ⟧⟨M', N'⟩

      let t_pair_MN ← match pair_MN.infer with
        | DCC (Π(Id(_a), b) _c) => .some b
        | _ => .none

      -- App x (M x, N x)
      -- f_β is the type of (N x), dictated by x
      -- a function of App's environment, which is x
      -- f_γ is determined by x, and (N x)
      let app_MN := DCC App'(f_β, f_γ)

      -- dup_env x = App x (M x, N x)
      let dup_env := DCC ⟦m, α, `(Sort m, App(m, elim_sort, f_β, f_γ)), t_pair_MN⟧⟨app_MN, pair_MN⟩

      match (← inner_app.infer).fst, (← inner_pair.infer).fst with
      | DCC (Π(_a, inner_app_β) _ax), DCC (Π(_pa, inner_pair_β) _pαx) =>
      -- λ M N --> App ∘ ⟨[M], [N]⟩
      -- (M' x) : Π(f_β, f_γ) x
      -- App(f_β, f_γ) x (M' x, N' x)
      -- f_β x is the second argument accepted by M
      .some <| DCC ⟦m, f_β, f_γ, ⟧⟨inner_app, ⟩
    sorry

/-
Keep coming back to Subst.

reworking Subst with {f, g}?

{f, g} (x, y) = (f x, g y)

Subst(x, y) env = (x env) (y env)

Subst(f, g) (Γ := ⟦β⟧(x, y))
= (f x, g y)

If we leave context inside a couple for App,

we can avoid duplication? Yes. Match is pretty much perfect for this.
Maybe we can remove some other things with match as well.

App (env, (x, y)) = x y

env : δ
App(f_α, f_β) : (Π(Id(Sort n), `(Sort n, ...))
  Coup(Σ(Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(δ, Π(f_α, f_β)))))
  ⟨Id(t_env), { f_β Id(t_env),
    -- snd type here can depend on fst
    Snd(Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(δ, Π(f_α, f_β)))) }⟩
  )

⟨Id(t_env), { f_β Id(t_env),
    -- snd type here can depend on fst
    Snd(Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(δ, Π(f_α, f_β)))) }⟩ (env, (f, x))
    = (env, (f_β env, x : α))

App ∘ { f_β Id(t_env),
    -- snd type here can depend on fst
    Snd(Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(δ, Π(f_α, f_β)))) }

{ π₁, π₂ }

can this replace Subst(x, Fst) = x env (Fst(β) env)

Yes. {

App(f_α, f_β) : (Π(Id(Sort n), `(Sort n, ...))
  Coup(Σ(Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(δ, Π(f_α, f_β)))))
  ⟨Id(t_env), { f_β ∘ Id(t_env),
    -- snd type here can depend on fst
    Snd(Λ(δ, Π(f_α, f_β), f_α ∘ Fstc(δ, Π(f_α, f_β)))) }⟩
  )

It would be super cool if we could distinguish term arguments in size
from type arguments.
Type arguments should not affect global size.

e.g.,

Subst(x, y) env = x env (y env)

Then we can just use Subst.

TyArity x 1
→ TyArity (Subst(x, y)) 1

TyArity f 0
→ Size f m
→ Size x n
→ Size (f x) (m + n)

then we can generalize Subst.

match is nice, but doesn't really solve the general problem.
Subst is the best.
-/
