import Dcc.Judge
import Dcc.Tactic.Debug

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
  | .lam _ bty bdy _     => max (shared_in depth bty) (shared_in depth.succ bdy)
  | .forallE _ bty bdy _ => max (shared_in depth bty) (shared_in depth.succ bdy)
  | .proj _ _ strt => shared_in depth strt
  | .letE _ ty val bdy _ => max (max (shared_in depth ty) (shared_in depth val)) (shared_in depth bdy)
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

def Expr.deref : Expr → Expr
  | DCC !(Γ) => Γ
  | Γ => Γ

/-
TODO: better logic for detecting duplication. Maybe some kind of user marker.

-/

def wrap_shares (n : ℕ) (e : Expr) : Expr :=
  (List.replicate n (DCC !(#(·)))).foldr id e

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
  | .app (.const ``Shared _us) (.const ``True.intro []) => DCC (*(∗))
  | .app (.const ``Shared _us) (.const ``True []) => DCC (*(⊤))
  | .app (.const ``Shared _us) (.const ``False []) => DCC (*(⊥))
  | .app (.app (.const ``Shared.share _us) _α) (.const ``True.intro []) => DCC (&(∗))
  | .app (.app (.const ``Shared.share _us) _α) (.const ``False []) => DCC (&(⊥))
  | .app (.app (.const ``Shared.share _us) _α) (.const ``True []) => DCC (&(⊤))
  | .app (.app (.const ``Shared.share _us) _α) (.sort .zero) => DCC &(Sort 0)
  | .app (.app (.const ``Shared _us) _α) (.sort .zero) => DCC *(Sort 0)
  | .app (.app (.const ``Shared.share _us) _α) (.sort (.succ m)) => do
    match ← (cc (.app (.app (.const ``Shared.share _us) _α) (.sort m))) with
    | DCC &(Sort n)
    | DCC Sort n => pure (DCC &(Sort (n + 1)))
    | _ => .none
  | .app (.const ``Shared _us) (.sort (.succ m)) => do
    match ← cc (.app (.const ``Shared _us) (.sort m)) with
    | DCC *(Sort n)
    | DCC Sort n => pure (DCC *(Sort (n + 1)))
    | _ => .none
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

-- thank you to gemini for writing this
def map_lam_bvars (e : Lean.Expr) (myTransform : Lean.Expr → Lean.Expr) : Lean.MetaM Lean.Expr := do
  Lean.Meta.lambdaTelescope e fun fvars body => do
    if fvars.size == 0 then
      return e
    let targetFVar := fvars[0]!
    let newBody ← Lean.Meta.transform body (pre := fun subExpr => do
      if subExpr == targetFVar then
        let modifiedExpr := myTransform subExpr
        return .done modifiedExpr
      else
        return .continue
    )

    Lean.Meta.mkLambdaFVars fvars newBody

def wrap_share_auto (e : Lean.Expr) : Lean.Meta.MetaM Lean.Expr := do
  match e with
  | .proj a b strt => return .proj a b (← wrap_share_auto strt)
  | .letE a ty val bdy b =>
    return .letE a (← wrap_share_auto ty) (← wrap_share_auto val) (← wrap_share_auto bdy) b
  | .lam a bty bdy b =>
    match shared_in 0 bdy with
    | 0 => return .lam a bty (← wrap_share_auto bdy) b
    | _n =>
      let lv ← Lean.Meta.getLevel bty
      let bty' := (Lean.Expr.app (.const ``Shared [lv]) bty)
      let bdy' ← wrap_share_auto bdy
      let lam ← map_lam_bvars (.lam a bty bdy' b) (.app (Lean.Expr.app (.const ``Shared.deref [lv]) bty) ·)
      match lam with
      | .lam a _ bdy b => return .lam a bty' bdy b
      | e => return e
      /-Lean.Meta.lambdaTelescope (.lam a bty bdy' b) (fun fvars bdy => do
        let fvars' := (fvars.map (.app (Lean.Expr.app (.const ``Shared.deref [lv]) bty) ·))
        Lean.Meta.mkLambdaFVars fvars' bdy)-/
  | .forallE a bty bdy b =>
    return .forallE a bty (← wrap_share_auto bdy) b
  | .app M N =>
    let M' ← wrap_share_auto M
    let N' ← wrap_share_auto N
    match ← Lean.Meta.inferType M' with
    | .forallE _ (.app (.const ``Shared us) α) _ _ =>
      return .app M' (.app (.app (.const ``Shared.share us) α) N')
    | _ => return .app M' N'
  | e => return e

open Qq in
def Lean.Expr.cc' {u : Lean.Level} {α : Q(Sort u)} (root : Q($α)) : Option _root_.Expr :=
  cc root

def Lean.Expr.ccM (root : Lean.Expr) : Lean.MetaM (Option _root_.Expr) :=
  cc <$> (wrap_share_auto root)

open Qq in
#eval Lean.Expr.cc' q(λ (x : Sort 1) => x)

open Qq in
#eval (do Sigma.fst <$> (← (Lean.Expr.cc' q((λ (α : Sort 0) => λ (x : α) => x) True True.intro))).infer)

elab "dcc_compile'" tm:term : term => do
  let e_tm ← Lean.Elab.Term.elabTerm tm .none
  let dcc_tm ← Lean.Expr.ccM e_tm
  match dcc_tm with
  | .some tm => return Lean.toExpr tm
  | .none => throwErrorAt tm "could not compile"

macro "dcc_infer'" tm:term : term =>
  `(term| do Sigma.fst <$> (dcc_compile' $tm).infer)

syntax "dcc_compile" term : term
syntax "dcc_infer" term   : term

open Qq in
macro_rules
  | `(dcc_compile $tm:term) => `((Lean.Expr.cc' q($tm:term)))
  | `(dcc_infer $tm:term) => `((do Sigma.fst <$> (← (Lean.Expr.cc' q($tm:term))).infer))

#eval Std.format <| dcc_compile' (fun (α : Sort 0) (x : α) => x) True True.intro
#eval Std.format <| dcc_infer' (fun (α : Sort 0) (x : α) => x) True True.intro

#eval Std.format <| dcc_compile' (fun (x : Sort 0) => (fun (x : Sort 0) => x) x)
#eval Std.format <| dcc_infer' ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))
#eval Std.format <| dcc_compile' ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))

#eval Std.format <| dcc_compile (fun (α : Sort 0) (x : α) => x) True True.intro
#time #eval dcc_infer   (fun (α : Sort 0) (x : α) => x) True True.intro
#eval Std.format <| dcc_compile (fun (x : *(Sort 0)) => (fun (x : Sort 0) => x) x.deref)
#time #eval Std.format <| dcc_infer (((fun (x : *(Sort 1)) => (fun (x : Sort 1) => x) ↑(x))) &(Sort 0))
