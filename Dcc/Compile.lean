import Dcc.Ast
import Dcc.Types
import Dcc.Judge
import Lean
import Qq
open Qq

inductive LExpr where
  | idx    : ℕ     → LExpr
  | lam    : LExpr → LExpr → LExpr
  | forE   : LExpr → LExpr → LExpr
  | app    : LExpr → LExpr → LExpr
  | sort   : Level → LExpr
  | bot    : LExpr
  | top    : LExpr
  | tintro : LExpr
  | sigma  : LExpr → LExpr → LExpr
deriving Repr

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

      dbg_trace M'
      dbg_trace (← M'.infer).fst.reduce_all
      dbg_trace (DCC (f_β x_α)).reduce_all

      match (DCC (f_β x_α)).reduce_all with
      | DCC (Π(_f_β, γ)) =>
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

declare_syntax_cat lexpr

syntax "∗"                       : lexpr
syntax "⊤"                       : lexpr
syntax "⊥"                       : lexpr
syntax "Sort" term               : lexpr
syntax "v" ident                 : lexpr
syntax num                       : lexpr
syntax "#(" term ")"             : lexpr
syntax "λ" ":" lexpr "=>" lexpr  : lexpr
syntax lexpr "→" lexpr           : lexpr
syntax "∀" ":" lexpr "," lexpr   : lexpr
syntax "Σ" ":" lexpr "," lexpr   : lexpr
syntax:30 ident                  : lexpr
syntax "(" lexpr+ ")"            : lexpr

syntax "DLCC" lexpr : term

macro_rules
  | `(DLCC $α:lexpr → $β:lexpr) => `(DLCC ∀ : $α:lexpr, $β:lexpr)
  | `(DLCC ∗) => `(LExpr.tintro)
  | `(DLCC ⊤) => `(LExpr.top)
  | `(DLCC ⊥) => `(LExpr.bot)
  | `(DLCC Sort $m:term) => `(LExpr.sort $m)
  | `(DLCC v $idt:ident) => `(LExpr.idx $idt)
  | `(DLCC $n:num) =>
    let n' := Lean.Syntax.mkNatLit n.getNat
    `(LExpr.idx $n')
  | `(DLCC λ :$α:lexpr => $x:lexpr) =>
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

def LExpr.abstract (bdy : LExpr) (ctx : Ctx) : Option Expr :=
  match bdy with
  | .idx n => mk_lookup ctx n
  | DLCC Σ : α, β => do
    let α' ← α.abstract ctx
    let β' ← β.abstract (DCC Coup(α'))
    .some (DCC Σ(β'))
  | DLCC (λ : α => bdy) => do
    -- how to append context?
    /-
      α may depend on env, so we abstract it
      then we can infer to see if it depends on the environment. e.g.,
      λ (α : Sort m) → λ (y : α) → y
    -/
    let α' ← α.abstract ctx
    let inner ← bdy.abstract (DCC Coup(α'))
    .some (DCC Λ(ctx, α', inner))
  | DLCC (∀ : α, β) => do
    let α' ← α.abstract ctx
    let β' ← β.abstract (DCC Coup(α'))

    .some (DCC (Π(α', Λ(ctx, α', β'))))
  | DLCC (M N) => do
    let M' ← M.abstract ctx
    let N' ← N.abstract ctx

    match (← M'.infer).fst with
    | DCC (Π(f_α, f_β) x_α) =>
      let α := (DCC (f_α x_α)).reduce_all

      dbg_trace M'
      dbg_trace (← M'.infer).fst.reduce_all
      dbg_trace (DCC (f_β x_α)).reduce_all

      match (DCC (f_β x_α)).reduce_all with
      | DCC (Π(_f_β, γ)) =>
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

        .some (DCC Subst(Snd(γ), Sndc(Σ(γ))) ∘ ⟨Id(α), `(α, ⟨N', M'⟩)⟩)
      | _ => .none
    | _ => .none
  | DLCC ∗ => DCC (`(ctx, ∗))
  | DLCC ⊤ => DCC (`(ctx, ⊤))
  | DLCC ⊥ => DCC (`(ctx, ⊥))
  | DLCC Sort m => DCC (`(ctx, Sort m))

def LExpr.cc (root : LExpr) : Option Expr :=
  match root with
  | DLCC ((λ :α => bdy) x) => do
    let ctx₀ := Ctx.empty
    let f' ← (DLCC (λ :α => bdy)).abstract ctx₀
    let x' ← x.cc
    .some (DCC (f' ∗ x'))
  | DLCC (M N) => do
    let M' ← M.cc
    let N' ← N.cc
    .some (DCC (M' N'))
  | DLCC ∗ => .some (DCC ∗)
  | DLCC ⊤ => .some (DCC ⊤)
  | DLCC ⊥ => .some (DCC ⊥)
  | DLCC Sort m => .some (DCC Sort m)
  | e => (·.app .tintro) <$> abstract e Ctx.empty

#eval Lean.Expr.cc' q(λ (x : Sort 1) => x)

#eval (do Sigma.fst <$> (← (Lean.Expr.cc' q((λ (α : Sort 0) => λ (x : α) => x) True True.intro))).infer)

#eval (DLCC ((λ : (Sort 1) => 0) (Sort 0))).cc
#eval (do Sigma.fst <$> (← (DLCC ((λ : (Sort 1) => 0) (Sort 0))).cc).infer)
#eval (DLCC ((λ : (Sort 1) => λ : 0 => 0))).cc
#eval (DLCC ((λ : (Sort 0) => λ : 0 => 0) ⊤ ∗)).cc
#eval (do Sigma.fst <$> (← (DLCC ((λ : (Sort 0) => λ : 0 => 0) ⊤ ∗)).cc).infer)
#eval (DLCC ((λ : (Sort 2) => λ : 0 => 0))).cc
#eval Sigma.fst <$> (DCC Sndc(Sndc(`(⊤, Sort 2)))).infer
#eval Sigma.fst <$> (DCC Sndc(`(⊤, Sort 2))).infer
#eval Sigma.fst <$> (DCC Λ(Coup(`(⊤, Sort 2)), Sndc(`(⊤, Sort 2)), Sndc(Sndc(`(⊤, Sort 2))))).infer
#eval Sigma.fst <$> (DCC Sndc(Sndc(`(⊤, Sort 2)))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC `(⊤, Sndc(`(⊤, Sort 2)))).infer
--#eval (do Sigma.fst <$> (← (DLCC (λ : (Sort 2) => λ : 0 => 0)).cc).infer)

/-
TODO Σ-terms compile
-/

/-
This does not pass judgment.
`(Coup(Π(`(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))), Sort 0)

I think the issue is that we need to curry the environment first.
-/

-- Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))
#eval (DLCC (λ : ((Sort 0) → Sort 0) => λ : (Sort 0) => (1 0))).cc

#eval (DCC Subst(`(⊤, Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))),
           Fst(`(⊤, Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0))))))).infer.isSome
#eval (DCC Fstc(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), Sort 0))).infer.isSome

#eval Sigma.fst <$> (DCC Fstc(`(Coup(Π(`(⊤, Sort 0), Λ(⊤, `(⊤, Sort 0), `(Coup(`(⊤, Sort 0)), Sort 0)))), Sort 0))).infer

/-
No easy way to extract the nested Π.
we could look at the input type and extract a "fake" witness.

we could also do this through η-reduction.
move the logic into f_α and f_β.

We could also pair our LCC exprs with lean exprs, or just write them in Lean altogether.
-/
