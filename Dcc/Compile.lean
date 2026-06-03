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
      (DCC ((#(·) ∘' Fstc(β)) ∘' !(Coup(β)))) <$> cc_var (DCC (a x_α)).reduce_all n
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
    return DCC !(x')
  | .app (.app (.const ``Shared.share _us) _α) x => do
    let x' ← cc x
    return DCC &(x')
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

def wrap_shares (n : ℕ) (u : Lean.Level) (e : Lean.Expr) : Lean.Expr :=
  (List.replicate n (Lean.Expr.const ``Shared [u])).foldr .app e

def n_times_shared (e : Lean.Expr) : (Option Lean.Level) × ℕ × Lean.Expr :=
  match e with
  | (.app (.const ``Shared [l]) α) =>
    let (_l, n, e) := (n_times_shared α)
    (.some l, n.succ, e)
  | e => (.none, .zero, e)

def share_n_times (n : ℕ) (lvl : Lean.Level) (α e : Lean.Expr) : Lean.Expr :=
  Prod.snd <| (List.replicate n (Lean.Expr.const ``Shared.share [lvl])).foldr (init := (α, e))
    (f := fun e ((α, x): Lean.Expr × Lean.Expr) =>
      ((.app (Lean.Expr.const ``Shared [lvl]) α), (.app (Lean.Expr.app e α) x)))

def deref_n_times (n : ℕ) (lvl : Lean.Level) (base_ty e : Lean.Expr) : Lean.Expr :=
  match n with
  | 0 => e
  | n' + 1 =>
    let inner_ty := wrap_shares n' lvl base_ty
    let e' := Lean.Expr.app (Lean.Expr.app (.const ``Shared.deref [lvl]) inner_ty) e
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
    match M' with
    | .lam _ α _ _ =>
      let ⟨lvl, n_shared, α⟩ := n_times_shared α
      match lvl with
      | .some lv =>
        let N'' := share_n_times n_shared lv α N'
        return .app M' N''
      | _ => return .app M' N'
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
  let e_tm' ← Lean.instantiateExprMVars =<< wrap_share_auto e_tm
  match cc e_tm' with
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
#eval Std.format <| dcc_infer' ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))
#eval Std.format <| dcc_compile' ((fun (α : Sort 1) (x : α) => (fun (x : α) => x) x) (Sort 0))
#eval Std.format <| dcc_compile' ((fun (α : Sort 1) (x : α) => (fun (x : α) => x) x) (Sort 0))
#eval Std.format <| dcc_compile' ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))

#eval Std.format <| dcc_compile (fun (α : Sort 0) (x : α) => x) True True.intro
#time #eval dcc_infer   (fun (α : Sort 0) (x : α) => x) True True.intro
#eval Std.format <| dcc_compile (fun (x : *(Sort 0)) => (fun (x : Sort 0) => x) x.deref)
#time #eval Std.format <| dcc_infer (((fun (x : *(Sort 1)) => (fun (x : Sort 1) => x) ↑(x))) &(Sort 0))

#eval (Std.format ∘ Sigma.fst) <$> (DCC *(Coup(`(!(⊤), Sort 1)))).infer
#eval (Std.format ∘ Sigma.fst) <$> (DCC Sndc(`(!(⊤), Sort 1))).infer

/-
pppneed eta rule for this:
`(Coup(`(!(⊤), Sort 1)), Sort 1) ∘' *(Coup(`(!(⊤), Sort 1)))
-/

/-dcc_trace ((!Λ(⊤, `(!(⊤), Sort 1),
     !Λ(Coup(`(!(⊤), Sort 1)), (Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))),
        (Eval(Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))),
                ((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))) ∘'
                   Fstc((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))))),
                Λ(Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))),
                  ((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))) ∘'
                     Fstc((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))))),
                  Sndc(((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))) ∘'
                          Fstc((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))))))) ∘
           ⟦Λ(Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))),
                `(Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))),
                  Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))))),
                (((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))) ∘'
                      Fstc((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))))) ∘'
                   Fstc(`(Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))),
                          Coup((Sndc(`(!(⊤), Sort 1)) ∘'
                                  *(Coup(`(!(⊤),
                                          Sort 1)))))))))⟧⟨Id(Coup((Sndc(`(!(⊤), Sort 1)) ∘'
                                                     *(Coup(`(!(⊤), Sort 1)))))),
                                          Λ(Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))),
                                            `(Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))),
                                              Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))))),
                                            (Sndc((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))) ∘'
                                               Fstc(`(Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1))))),
                                                      Coup((Sndc(`(!(⊤), Sort 1)) ∘' *(Coup(`(!(⊤), Sort 1)))))))))⟩)))
    &(∗))
   &(Sort 0))-/

dcc_trace Eval(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))),
    ((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))∘'Fstc((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1)))))),
    Λ(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))),
      ((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))∘'Fstc((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1)))))),
      Sndc(((Sndc(`(!(⊤),
                    Sort
                      1))∘'*(Coup(`(!(⊤),
                      Sort
                        1))))∘'Fstc((Sndc(`(!(⊤),
                      Sort
                        1))∘'*(Coup(`(!(⊤),
                        Sort
                          1)))))))))∘⟦Λ(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))),
      `(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))),
        Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1)))))),
      (((Sndc(`(!(⊤),
                      Sort
                        1))∘'*(Coup(`(!(⊤),
                        Sort
                          1))))∘'Fstc((Sndc(`(!(⊤),
                        Sort
                          1))∘'*(Coup(`(!(⊤),
                          Sort
                            1))))))∘'Fstc(`(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))),
              Coup((Sndc(`(!(⊤),
                        Sort
                          1))∘'*(Coup(`(!(⊤),
                          Sort 1)))))))))⟧⟨Id(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1)))))),
    Λ(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))),
      `(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))),
        Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1)))))),
      (Sndc((Sndc(`(!(⊤),
                    Sort
                      1))∘'*(Coup(`(!(⊤),
                      Sort
                        1)))))∘'Fstc(`(Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1))))),
              Coup((Sndc(`(!(⊤), Sort 1))∘'*(Coup(`(!(⊤), Sort 1)))))))))⟩
