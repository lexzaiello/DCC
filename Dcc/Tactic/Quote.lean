import Dcc.Ast
import Dcc.Judge2
import Lean
import Lean.Meta.Basic
import Qq
import Mathlib.Util.Qq
import Qq.MetaM

open Qq
open Lean.Meta

/-
Display DCC terms as lean expressions.
-/

def level_from_nat (n : ℕ) : Lean.Level :=
  match n with
  | .zero => .zero
  | .succ n => (level_from_nat n).succ

inductive Level' where
  | zero : Level'
  | succ : Level' → Level'
  | imax : Level' → Level' → Level'
  | max  : Level' → Level' → Level'
deriving DecidableEq

@[inline]
abbrev level'_from_nat (n : ℕ) : Level' :=
  match n with
  | .zero => .zero
  | .succ n => (level'_from_nat n).succ

def Level.to_level' (l : Level) : Level' :=
  match l with
  | .zero => .zero
  | .succ n => .succ (Level.to_level' n)

def Level'.to_level (l : Level') : Lean.Level :=
  match l with
  | .zero => .zero
  | .succ n => .succ n.to_level
  | .imax m n => .imax m.to_level n.to_level
  | .max m n => .max m.to_level n.to_level

theorem Level'.to_level_assoc : (Level'.to_level u).succ = (Level'.to_level u.succ) := by
  induction u
  any_goals (simp [to_level])

theorem Level'.inj₂ {u₂ : Lean.Level} (h : Level'.to_level (Level'.succ u₁) =
  u₂.succ) : u₁.to_level = u₂ := by
  simp [Level'.to_level] at *
  exact h

theorem Level'.inj {u₂ : Lean.Level} (h : Level'.to_level (Level'.succ u₁).succ =
  u₂.succ.succ) : (Level'.succ u₁).to_level = u₂.succ := by
  simp [Level'.to_level] at *
  exact h

theorem Level'.inj' {u₂ : Lean.Level} (h : Level'.to_level u₁ =
  u₂) : (Level'.succ u₁).to_level = u₂.succ := by
  simp [Level'.to_level] at *
  exact h

-- (u_fst₁.to_level.succ.max u_snd₁.to_level.succ).max u_α₁.to_level = (u_α₁.max (u_fst₁.succ.max u_snd₁.succ)).to_level
/-theorem Level'.comm : (Lean.Level.max (Lean.Level.max (Level'.to_level x) (Level'.to_level y)) (Level'.to_level z))
  = (Level'.max z (Level'.max x y)).to_level := by
  unfold Level'.to_level
  split
  case h_1 =>
    split
    case h_1 =>
      split
      case h_1 =>
        unfold Level'.to_level
        sorry-/

def Level'.to_level_expr (l : Level') : ((u : Lean.Level) × Q(Sort $u)) :=
  match l with
  | .zero => ⟨(Level'.succ .zero).to_level, q(Sort 0)⟩
  | .succ n => ⟨_, q(Sort $(n.to_level))⟩
  | .imax m n => ⟨_, q(Sort (imax $(m.to_level) $(n.to_level)))⟩
  | .max m n => ⟨_, q(Sort (max $(m.to_level) $(n.to_level)))⟩

/-def Level.imax (l₁ l₂ : Level) : Level :=
  match l₁, l₂ with
  | _, .zero => .zero
  | m, .succ n => max m (.succ n)-/

namespace Expr

def get_domain (e : Expr) : Option Expr :=
  match e.infer₂ with
  | .some ⟨DCC (Π(f_α, _f_β) env), _⟩ =>
    .some (reduce_all₂ (DCC (f_α env)))
  | _ => .none

def get_codomain (e : Expr) : Option Expr :=
  match e.infer₂ with
  | .some ⟨DCC (Π(_f_α, f_β) env), _⟩ =>
    .some (reduce_all₂ (DCC (f_β env)))
  | _ => .none

def get_codomain_arrow (e : Expr) : Option Expr :=
  match e.infer₂ with
  | .some ⟨DCC (Π(_f_α, f_β) env), _⟩ =>
    match (reduce_all₂ (DCC (f_β env))) with
    | (DCC `(_a, β)) => .some β
    | _ => .none
  | _ => .none

mutual

partial def get_fn_ty_arrow (e : Expr) : MetaM ((u v : Level') × (u' v' : Lean.Level)
  × (α : Q(Sort u')) × (β : Q(Sort v')) × Q($α → $β) × (PLift (u' = u.to_level)) × (PLift (v' = v.to_level))) := do
  match e.read_arrow with
  | .some ⟨α, β, _m, _⟩ =>
    match ← α.to_lean, ← β.to_lean with
    | ⟨u, u', τ_α, α, heq⟩, ⟨v, v', τ_β, β, heq₂⟩ =>
      match ← e.to_lean with
      | ⟨uv, uv', τ_f, f, heq⟩ =>
        let some α' ← checkTypeQ α q(Sort $(u.to_level))
          | throwError m!"invalid domain: {e}"
        let some β' ← checkTypeQ β q(Sort $(v.to_level))
          | throwError m!"invalid codomain: {e}"
        let some f' ← checkTypeQ f q($α' → $β')
          | throwError m!"function is not well-typed: {e}"
        return ⟨u, v, u.to_level, v.to_level, α', β', f', ⟨rfl⟩, ⟨rfl⟩⟩
  | _ => throwError m!"function is not an arrow: {e}"

partial def get_fn_ty (e : Expr) : MetaM ((u v : Level')
  × (α : Q(Sort $(u.to_level))) × (β : Q($α → Sort $(v.to_level))) × Q(∀ (x : $α), $β x)) := do
  match e.get_domain, e.get_codomain with
  | .some dom, .some cod =>
    match ← dom.to_lean with
    | ⟨u, u', τ_α, α, heq⟩ =>
      match ← cod.get_fn_ty, ← e.to_lean with
      | ⟨u₂, v, α₂, _β, β⟩, ⟨uv, uv', τ_f, f, heq⟩ =>
        if heq : u₂ = u then
          if heq₂ : uv = (u.imax v) then
            match ← isDefEqQ α α₂ with
            | .defEq heq =>
              let some α' ← checkTypeQ α q(Sort $(u.to_level))
                | throwError m!"invalid domain: {e}"
              let some β' ← checkTypeQ β q($α' → Sort $(v.to_level))
                | throwError m!"invalid codomain: {e}"
              let some f' ← checkTypeQ f q(∀ (x : $α'), $β' x)
                | throwError m!"couldn't quote function: {e}"
              return ⟨u, v, α', β', f'⟩
            | .notDefEq =>
              throwError m!"not well-typed (domain and codomain domain mismatch): {e}"
          else throwError m!"not well-typed (domain and codomain universe level mismatch): {e}"
        else throwError m!"not well-typed (domain and codomain universe level mismatch): {e}"
  | _, .none | .none, _ => throwError m!"not well-typed (no domain or codomain): {e}"

partial def to_lean (e : Expr) : MetaM ((u : Level') × (u' : Lean.Level) ×
  (α : Q(Sort $u')) × Q($α) × (PLift (u' = u.to_level))):= do
  match heq₀ : e with
  | (DCC ⊤)                   => return ⟨.succ .zero, (Level'.succ .zero).to_level, q(Prop), q(True), ⟨rfl⟩⟩
  | (DCC ⊥)                   => return ⟨.succ .zero, (Level'.succ .zero).to_level, q(Prop), q(False), ⟨rfl⟩⟩
  | (DCC ∗)                   => return ⟨.zero, Level'.zero.to_level, q(True), q(True.intro), ⟨rfl⟩⟩
  | (DCC !<f>)                =>
    match ← f.get_fn_ty with
    | ⟨.succ u, .succ v, α, β, f'⟩ =>
      return ⟨Level'.imax (.succ u) (.succ v), (Level'.imax (.succ u) (.succ v)).to_level, q(∀ (x : Shared $α), Bang ($β x.deref)), q(fun (x : Shared $α) => Shared.map $f' x), ⟨rfl⟩⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC $<f>)                =>
    match ← f.get_fn_ty with
    | ⟨.succ u, .succ v, α, β, f'⟩ =>
      return ⟨Level'.imax (.succ u) (.succ v), (Level'.imax (.succ u) (.succ v)).to_level, q(∀ (x : Shared $α), Shared ($β x.deref)), q(fun (x : Shared $α) => Shared.fmap $f' x), ⟨rfl⟩⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC &(x))                =>
    match ← x.to_lean with
    | ⟨.succ u, .succ u', α, x', heq⟩ =>
      by
        cases heq
        exact pure <| ⟨.succ u, u'.succ, q(Shared $α), q(Shared.share $x'), ⟨by simp_all⟩⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC *(α))                =>
    match ← α.to_lean with
    | ⟨.succ (.succ u), .succ (.succ u'), τ_α, α', heq⟩ =>
      match τ_α with
      | ~q(Type u') =>
        by
          cases heq
          rename_i match_eq
          exact pure ⟨.succ u, _, q(Shared.{u'} $α' → $α'), q(fun (x : Shared $α') => Shared.deref.{u'} x), ⟨by
            rename_i h
            simp [Level'.to_level] at h
            rw [h]
            simp [Level'.to_level_assoc]⟩⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC !(α))                =>
    match ← α.to_lean with
    | ⟨.succ (.succ u), .succ (.succ u'), τ_α, α', heq⟩ =>
      match τ_α with
      | ~q(Type u') =>
        by
          cases heq
          rename_i match_eq
          exact pure ⟨.succ (.succ u), _, q(Type u'), q(Shared $α'), ⟨by
            rename_i h
            simp [Level'.to_level] at h
            rw [h]
            simp [Level'.to_level_assoc]⟩⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC Eval(α, β, x))       =>
    match ← α.to_lean with
    | ⟨.succ (.succ u), .succ (.succ u'), τ_α, α', ⟨heq⟩⟩ =>
      match τ_α with
      | ~q(Type u') =>
        let ⟨.max (.succ u_α) (.succ u_β), .max u_α' (.succ u_β'), τ_β, β', heqa₀⟩ ← β.to_lean
          | throwError m!"Eval second arg {β} is not well-typed in: {(DCC Eval(α, β, x))}"
        match τ_β with
        | ~q(∀ (x : ($α : (Sort u_α'))), Sort u_β') =>
          if heq₁ : u_α = u then
            match ← isDefEqQ α' α with
            | .defEq heq₂ =>
              match ← x.to_lean with
              | ⟨.imax (.imax (.succ (.succ u₂)) (.succ (.succ u_β₂))) (.succ (.succ u'₂)),
                .imax (.imax (.succ (.succ u₂a)) (.succ (.succ u_β₂a))) (.succ (.succ u'₂a)), τ_x, x', ⟨heq₃⟩⟩ =>
                if heq : u₂ = u then
                  if heqa : u_β₂ = u_β then
                    have α' : Q(Type u') := α'
                    have β' : Q($α' → Type u_β') := β'
                    match τ_x with
                    | ~q(∀ (x : ($α' : Type (u₂a + 1))) (y : ($β' : $α' → Type (u_β₂a + 1)) x),
                      ($γ : ∀ (x : $α') (y : $β' x), Type (u'₂a + 1)) x y) =>
                      .pure ⟨.imax (.imax (.succ (.succ u₂)) (.succ (.succ u_β₂))) (.succ (.succ u'₂)),
                        .imax (.imax (.succ (.succ u₂a)) (.succ (.succ u_β₂a))) (.succ (.succ u'₂a)),
                        τ_x, q(fun (x : $α') (y : $β' x) => $x' x y), ⟨by simp_all⟩⟩
                    | _ => throwError m!"Eval body {x} is not uncurryable in: {e}"
                  else throwError m!"Eval body {x} is not uncurryable in: {e}"
                else throwError m!"Eval body {x} is not uncurryable in: {e}"
              | _ => throwError m!"Eval body {β} is not uncurryable in: {e}"
            | _ => throwError m!"Eval body {α} is not uncurryable in: {e}"
          else throwError m!"Eval body {α} is not uncurryable in: {e}"
        | _ => throwError m!"Eval body {β} is not uncurryable in: {e}"
    | _ => throwError m!"Eval param {α} is not uncurryable in: {e}"
  | (DCC `(β, x))             =>
    match ← β.to_lean, ← x.to_lean with
    | ⟨.succ (.succ u), .succ (.succ u'), τ_β, β', ⟨heq₁⟩⟩, ⟨.succ (.succ v), .succ (.succ v'), τ_x, x', ⟨heq₂⟩⟩ =>
      by
        cases heq₁; cases heq₂
        exact .pure ⟨.imax (.succ (.succ u)) (.succ (.succ v)),
          Lean.Level.imax (Level'.succ (.succ u)).to_level (Level'.succ (.succ v)).to_level , q($τ_β → $τ_x), q(fun (y : $τ_β) => $x'), ⟨by
          unfold Level'.to_level
          rw [Level'.to_level_assoc, Level'.to_level_assoc]⟩⟩
    | _, _ => throwError m!"Quotation points are not well-typed: `({β}, {x})"
  | (DCC Id(α))               =>
    match ← α.to_lean with
    | ⟨.succ (.succ u), .succ (.succ u'), τ_α, α', heq⟩ =>
      match τ_α with
      | ~q(Type u') =>
        by
          cases heq
          rename_i match_eq
          exact pure ⟨.succ u, _, q($α' → $α'), q(fun (x : $α') => x), ⟨by
            rename_i h
            simp [Level'.to_level] at h
            rw [h]
            simp [Level'.to_level_assoc]⟩⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC Sort m)              =>
    let m₀  := (level'_from_nat m)
    let m'  := m₀.to_level
    let s₁  := Lean.Expr.sort m'.succ
    let s₂ := Lean.Expr.sort m'
    let some s₁' ← checkTypeQ s₁ q(Type (m' + 1))
      | throwError m!"not a valid sort: {e}"
    let some s₂' ← checkTypeQ s₂ q(Type m')
      | throwError m!"not a valid sort: {e}"
    pure <| ⟨m₀.succ.succ, m'.succ.succ, s₁, s₂, ⟨by
      simp_all [Level'.to_level]
      rfl⟩⟩
  | (DCC Fstc(β))             =>
    match ← β.to_lean with
    | ⟨.max (.succ (.succ u)) (.succ u_α) , .max (.succ (.succ u')) (.succ u_α'), τ_β, β', ⟨heq⟩⟩ =>
      match τ_β with
      | ~q(∀ (x : ($α : Type u_α')), Type u') =>
        pure ⟨(.max u.succ u_α.succ), (Lean.Level.max u'.succ u_α'.succ),
          q(∀ (x : Σ a : $α, $β' a), $α), q(fun (x : Σ a : $α, $β' a) => Sigma.fst x)
          , ⟨by
            cases heq
            simp [Level'.to_level]⟩⟩
      | _ => throwError m!"not a well-typed projection (Fst) index: {β}"
    | _ => throwError m!"not a valid projection (Fst) index: {β}"
  | (DCC Sndc(β))             =>
    match ← β.to_lean with
    | ⟨.max (.succ (.succ u)) (.succ u_α) , .max (.succ (.succ u')) (.succ u_α'), τ_β, β', ⟨heq⟩⟩ =>
      match τ_β with
      | ~q(∀ (x : ($α : Type u_α')), Type u') =>
        pure ⟨(.max u.succ u_α.succ), (Lean.Level.max u'.succ u_α'.succ),
          q(∀ (x : Σ a : $α, $β' a), $β' (Sigma.fst x)), q(fun (x : Σ a : $α, $β' a) => Sigma.snd x)
          , ⟨by
            cases heq
            simp [Level'.to_level]⟩⟩
      | _ => throwError m!"not a well-typed projection (Fst) index: {β}"
    | _ => throwError m!"not a valid projection (Fst) index: {β}"
  | (DCC Λ(α, β, e))          =>
    -- switch τ_α to Sort u'?
    match ← α.to_lean with
    | ⟨.succ (.succ u), .succ (.succ u'), τ_α, α', ⟨heq⟩⟩ =>
      match τ_α with
      | ~q(Type u') =>
        let ⟨.max (.succ u_α) (.succ u_β), .max (.succ u_α') (.succ u_β'), τ_β, β', ⟨heqb⟩⟩ ← β.to_lean
          | throwError m!"Eval second arg {β} is not well-typed in: {(DCC Λ(α, β, e))}"
        match τ_β with
        | ~q(∀ (x : ($α : (Type u_α'))), Sort u_β') =>
          match ← isLevelDefEqQ u' u_α' with
          | .defEq h =>
            match ← isDefEqQ α' α with
            | .defEq heq₂ =>
              --let u_β' := u_β.to_level
              --let u_β' := (Level'.succ u_β).to_level
              let ⟨.imax u_e₁ u_e₂, .imax u_e₁' u_e₂', τ_x, e', ⟨heq₃⟩⟩ ← e.to_lean
                | throwError m!"this should not be reachable (curry)"
              have β' : Q($α' → Type u_β') := β'
              let t_sigma : Q(Type (max u' u_β')) := q(Σ (a : $α), $β' a)
              let γ : Q((Σ (a : $α'), $β' a) → Sort u_e₂') ← mkFreshExprMVarQ q($t_sigma → Sort u_e₂')
              let expected_τ_x : Q(Sort (imax (max (u_β' + 1) (u' + 1)) u_e₂')) :=
                q(∀ (x : (Σ (a : $α'), $β' a)), $γ x)
              let lv_expected := (Level'.imax u_e₁ u_e₂).to_level
              let some expected_τ_x ← checkTypeQ q(Sort lv_expected) expected_τ_x
                | throwError m!"this should not be reachable (curry)"
              let e'' : Q(∀ (x : (Σ (a : $α'), $β' a)), $γ x) := e'
              let u_all := Level'.imax (Level'.max u u_β) u_e₂
              let γ_inst ← instantiateMVarsQ γ (α := q((Σ (a : $α'), $β' a) → Sort u_e₂'))
              pure ⟨Level'.imax (.succ u) (Level'.imax (Level'.succ u_β) u_e₂),
                Lean.Level.imax (.succ u') (Lean.Level.imax (Lean.Level.succ u_β') u_e₂'),
                q(∀ (x : $α') (y : $β' x), $γ (Sigma.mk x y)),
                q(fun (x : $α') (y : $β' x) => ($e'' (Sigma.mk x y))) , ⟨by
                  simp [Level'.to_level]
                  have ha := Level'.inj₂ (Level'.inj heq.symm)
                  simp [Level'.to_level] at heqb
                  simp [Level'.to_level] at heq₃
                  have hc := heq₃.right
                  simp [ha.symm, heqb.right, hc]⟩⟩
            | _ => throwError m!"Eval body {α} is not curryable in: {e}"
          | _ => throwError m!"Eval body {α} is not curryable in: {e}"
        | _ => throwError m!"Eval body {α} is not curryable in: {e}"
    | _ => throwError m!"Eval param {α} is not curryable in: {e}"
  | (DCC !Λ(α, β, e))          =>
    -- switch τ_α to Sort u'?
    match ← α.to_lean with
    | ⟨.succ (.succ u), .succ (.succ u'), τ_α, α', ⟨heq⟩⟩ =>
      match τ_α with
      | ~q(Type u') =>
        match ← get_fn_ty_arrow β with
        | ⟨.succ (.succ u_α), .succ (.succ u_β), .succ (.succ u_α'), .succ (.succ u_β'), α'', β_cod, β', ⟨heqa⟩, ⟨heqb⟩⟩  =>
          if heq₁ : u_α = u then
            match ← isDefEqQ α' α'' with
            | .defEq heq₂ =>
              --let u_β' := u_β.to_level
              --let u_β' := (Level'.succ u_β).to_level
              match β_cod with
              | ~q(Type u_β') =>
                let ⟨.imax u_e₁ u_e₂, .imax u_e₁' u_e₂', τ_x, e', ⟨heq₃⟩⟩ ← e.to_lean
                  | throwError m!"this should not be reachable (curry)"
                let t_sigma : Q(Type (max u' u_β')) := q(Σ (a : $α'), $β' a)
                let γ : Q((Shared (Σ (a : $α'), $β' a)) → Sort u_e₂') ← mkFreshExprMVarQ q(Shared $t_sigma → Sort u_e₂')
                let expected_τ_x : Q(Sort (imax (max (u_β' + 1) (u' + 1)) u_e₂')) :=
                  q(∀ (x : (Shared (Σ (a : $α'), $β' a))), $γ x)
                let lv_expected := (Level'.imax u_e₁ u_e₂).to_level
                let some expected_τ_x ← checkTypeQ q(Sort lv_expected) expected_τ_x
                  | throwError m!"this should not be reachable (curry)"
                let e'' : Q(∀ (x : (Shared (Σ (a : $α'), $β' a))), $γ x) := e'
                let u_all := Level'.imax (Level'.max u u_β) u_e₂
                let γ_inst ← instantiateMVarsQ γ (α := q((Σ (a : $α'), $β' a) → Sort u_e₂'))
                pure ⟨Level'.imax (.succ u) (Level'.imax (Level'.succ u_β) u_e₂),
                  Lean.Level.imax (.succ u') (Lean.Level.imax (Lean.Level.succ u_β') u_e₂'),
                  q(∀ (x : Shared $α') (y : Shared ($β' x.deref)), $γ (Shared.share (Sigma.mk (Shared.deref x) (Shared.deref y)))),
                  q(fun (x : Shared $α') (y : Shared ($β' x.deref)) => ($e'' (Shared.share (Sigma.mk (Shared.deref x) (Shared.deref y))))) , ⟨by
                    simp [Level'.to_level]
                    have ha := Level'.inj₂ (Level'.inj heq.symm)
                    have hb := Level'.inj₂ (Level'.inj heqb.symm)
                    simp [Level'.to_level] at heq₃
                    have hc := heq₃.right
                    exact ⟨ha.symm, hb.symm, hc⟩⟩⟩
              | _ => throwError m!"Eval body {β} is not curryable in: {e}"
            | _ => throwError m!"Eval body {α} is not curryable in: {e}"
          else throwError m!"Eval body {α} is not curryable in: {e}"
        | _ => throwError m!"Eval body {α} is not curryable in: {e}"
    | _ => throwError m!"Eval param {α} is not curryable in: {e}"
  | (DCC Π(α, β))             =>
    let ⟨.imax (.succ u_δ₁) (.succ u_α₁), .imax (.succ u_δ₁') (.succ u_α₁')
      , ~q($δ → Sort u_α₁'), f_α', ⟨heqb⟩⟩ ← to_lean α
      | throwError m!"Π domain function {α} is not well-typed at {(DCC Π(α, β))}"
    let ⟨.imax (.succ _a) (.imax (.succ _b)  (.succ u_β₂))
      , .imax (.succ _a₂) (.imax (.succ _b₂) (.succ u_β₂'))
      , τ_f_β', f_β', ⟨heqc⟩⟩ ← to_lean β
      | throwError m!"Π domain function {β} is not well-typed at {(DCC Π(α, β))}"
    let some f_β'' ← checkTypeQ f_β' q(∀ (env : $δ) (α : $f_α' env), Sort u_β₂')
      | throwError m!"Π domain function {β} is not well-typed at {(DCC Π(α, β))}"
    pure ⟨.max (.succ u_δ₁) (.succ (.imax u_α₁ u_β₂))
      , _
      , q($δ → Sort (imax u_α₁' u_β₂'))
      , q(fun (env : $δ) => (∀ (x : $f_α' env), $f_β'' env x))
      , ⟨by
        simp [Level'.to_level] at heqb
        simp [Level'.to_level] at heqc
        simp [Level'.to_level, heqb.left, heqb.right, heqc.right.right]⟩⟩
  | (DCC ⟦β⟧⟨a, b⟩)           =>
    let ⟨.max (.succ u_α₁) (.max (.succ u_fst₁) (.succ u_snd₁))
       , .max (.succ u_α₁') (.max (.succ u_fst₁') (.succ u_snd₁'))
       , τ_b', b', ⟨heqa⟩⟩ ← to_lean b
       | throwError m!"pair snd function {b} is not well-typed at {(DCC ⟦β⟧⟨a, b⟩)}"
    let ⟨.imax u_α₂  u_fst₂
       , .imax u_α₂' u_fst₂'
       , τ_a', a', ⟨heqb⟩⟩ ← to_lean a
       | throwError m!"pair snd function {a} is not well-typed at {(DCC ⟦β⟧⟨a, b⟩)}"
    let ⟨.imax u_α₃  u_β₃
       , .imax u_α₃' u_β₃'
       , τ_β', β', ⟨heqc⟩⟩ ← to_lean β
       | throwError m!"pair couple-image function {β} is not well-typed at {(DCC ⟦β⟧⟨a, b⟩)}"
    match τ_b' with
    | ~q(∀ (x : ($α : Sort (u_α₁' + 1)))
      (y : (($f_β x) : Sort (u_fst₁' + 1))), (($γ x y) : Sort (u_snd₁' + 1))) =>
      let some a' ← checkTypeQ a' q(∀ (x : $α), $f_β x)
        | throwError m!"pair snd function {a} is not well-typed at {(DCC ⟦β⟧⟨a, b⟩)}"
      pure ⟨.max (.max (.succ u_fst₁) (.succ u_snd₁)) (.succ u_α₁)
          , _
          , q(∀ (x : (Shared $α)), Σ (a : ($f_β x.deref)), $γ x.deref a)
          , q(fun (x : (Shared $α)) => Sigma.mk ($a' x.deref) ($b' x.deref ($a' x.deref)))
          , ⟨by
            simp [Level'.to_level] at heqa
            simp [heqa.left, heqa.right]
            rfl⟩⟩
    | τ_β' => throwError m!"pair snd function {b} has type: {τ_β'}, but that was not expected at {(DCC ⟦β⟧⟨a, b⟩)}"
  | (DCC ⟦β⟧(a, b))           =>
    let ⟨.max (.succ u_fst₁)  (.succ u_snd₁)
       , .max (.succ u_fst₁') (.succ u_snd₁')
       , τ_β, β', ⟨heqa⟩⟩ ← to_lean β
       | throwError m!"couple snd type {β} is not well-typed at {(DCC ⟦β⟧(a, b))}"
    let ⟨.succ u_fst₂
        , .succ u_fst₂'
        , τ_a, a', ⟨heqb⟩⟩ ← to_lean a
        | throwError m!"couple fst {a} is not well-typed at {(DCC ⟦β⟧(a, b))}"
    let ⟨.succ u_snd₂
        , .succ u_snd₂'
        , τ_b, b', ⟨heqc⟩⟩ ← to_lean b
        | throwError m!"couple snd {b} is not well-typed at {(DCC ⟦β⟧(a, b))}"
    let some β' ← checkTypeQ τ_β q($τ_a → Sort (u_snd₂' + 1))
      | throwError m!"couple snd type {β} is not well-typed at {(DCC ⟦β⟧(a, b))}"
    let b' ← checkTypeQ (u := u_snd₂'.succ) a' q($β' $a')
    match b' with
    | .some b' =>
      pure ⟨(Level'.max (Level'.succ u_snd₂) (Level'.succ u_fst₂))
        , _, q(Σ (a : $τ_a), $β' a)
        , q(Sigma.mk $a' $b')
        , ⟨by
          simp [Level'.to_level] at heqa
          simp [Level'.to_level] at heqb
          simp [heqc]
          conv =>
            right
            rw [Level'.to_level, Level'.to_level]
            rfl
          simp [heqb, Level'.to_level_assoc]⟩⟩
    | .none => throwError m!"couple snd {b} is not well-typed at {(DCC ⟦β⟧(a, b))}"
  | (DCC Coup(β))             =>
    let ⟨.max (.succ u_fst₁)  (.succ u_snd₁)
       , .max (.succ u_fst₁') (.succ u_snd₁')
       , τ_β, β', ⟨heqa⟩⟩ ← to_lean β
       | throwError m!"couple snd type {β} is not well-typed at {(DCC Coup(β))}"
    match τ_β with
    | ~q(∀ (x : ($α : Sort (u_fst₁' + 1))), Sort u_snd₁') =>
      pure ⟨.max (.succ (.succ (.succ u_fst₁)))  (.succ (.succ (.succ u_snd₁)))
        , _
        , q(Type ((max u_fst₁' u_snd₁') + 1))
        , q(Type (max u_fst₁' u_snd₁'))
        , ⟨by
          simp [Level'.to_level]
          simp [Level'.to_level] at heqa
          simp [heqa.left, heqa.right]⟩⟩
    | _ =>  throwError m!"couple type type {β} is not well-typed at {(DCC Coup(β))}"
  | (DCC Σ(_f_α, f_β))             =>
    let ⟨.imax u_env₁ (.imax u_α₁ u_srt₁)
       , .imax u_env₁' (.imax u_α₁' u_srt₁')
      , τ_f_β', f_β', ⟨heqa⟩⟩ ← to_lean f_β
      | throwError m!"Σ domain function {f_β} is not well-typed at {(DCC Σ(_f_α, f_β))}"
    -- (u_env₁'.max u_srt₁'.succ.succ).max u_α₁'.succ.succ = ((u_env₁.max u_srt₁.succ.succ).imax u_α₁.succ.succ).to_level
    match τ_f_β' with
    | ~q(∀ (env : ($α : (Sort u_env₁'))) (x : (($β env) : (Sort u_α₁'))), ($cod : (Sort u_srt₁'))) =>
      pure ⟨(u_env₁.max u_srt₁.succ.succ).max u_α₁.succ.succ
        , _
        , q($α → Sort ((max u_α₁' u_srt₁') + 1))
        , q(fun (env : $α) => Sort ((max u_α₁' u_srt₁')))
        , ⟨by
          simp [Level'.to_level] at heqa
          simp_all
          simp [Level'.to_level]⟩⟩
    | _ => throwError m!"Σ domain function {f_β} is not well-typed at {(DCC Σ(_f_α, f_β))}"
  | (DCC x = y)               =>
    let ⟨srt_x, srt_x', τ_x, x', ⟨heqa⟩⟩ ← to_lean x
    let ⟨srt_y, srt_y', τ_y, y', ⟨heqb⟩⟩ ← to_lean y
    let some y' ← checkTypeQ y' τ_x
      | throwError m!"second component {y} is not well-typed in {(DCC (x = y))}"
    pure ⟨.succ .zero, .succ .zero, q(Prop), q($x' = $y'), ⟨by simp [Level'.to_level]⟩⟩
  | (DCC Eql(f_α))            =>
    let ⟨.max (.succ u_env₁) (.succ (.succ u_srt₁))
      , .max (.succ u_env₁') (.succ (.succ u_srt₁'))
      , τ_f_α', f_α', ⟨heqa⟩⟩ ← to_lean f_α
      | throwError m!"environment index {f_α} is not well-typed in {(DCC (Eql(f_α)))}"
    match τ_f_α' with
    | ~q(∀ (env : ($α : (Type u_env₁'))), Type u_srt₁') =>
      pure ⟨.max u_env₁.succ u_srt₁.succ, _
        , q(∀ (env : $α) (x : $f_α' env), Prop)
        , q(fun (env : $α) (x : $f_α' env) => x = x)
        , ⟨by
          simp [Level'.to_level] at heqa
          simp [Level'.to_level, heqa.left, heqa.right]⟩⟩
    | _ => throwError m!"environment index {f_α} is not well-typed in {(DCC (Eql(f_α)))}"
  | (DCC refl(f_α))            =>
    let ⟨.max (.succ u_env₁) (.succ (.succ u_srt₁))
      , .max (.succ u_env₁') (.succ (.succ u_srt₁'))
      , τ_f_α', f_α', ⟨heqa⟩⟩ ← to_lean f_α
      | throwError m!"environment index {f_α} is not well-typed in {(DCC (Eql(f_α)))}"
    match τ_f_α' with
    | ~q(∀ (env : ($α : (Type u_env₁'))), Type u_srt₁') =>
      pure ⟨.zero, _
        , q(∀ (env : $α) (x : $f_α' env), x = x)
        , q(fun (env : $α) (x : $f_α' env) => _root_.refl x)
        , ⟨by simp [Level'.to_level]⟩⟩
    | _ => throwError m!"environment index {f_α} is not well-typed in {(DCC (Eql(f_α)))}"
  | (DCC f ∘∘ g)
  | (DCC f ∘ g)               =>
    /-
      g : α → Σ (a : α) × β
      f : ∀ (s : Σ (a : α) × β), γ s
    -/
    let ⟨.max (.succ u_α₁) (.max (.succ u_α₁b) (.succ u_snd₁))
       , .max (.succ u_α₁') (.max (.succ u_α₁b') (.succ u_snd₁'))
      , τ_g', g', ⟨heqa⟩⟩ ← to_lean g
      | throwError m!"composition right hand {g} is not well-typed in {(DCC f ∘ g)}"
    let ⟨.max (.max (.succ u_α₂b) (.succ u_snd₂)) (.succ u_γ_out)
       , .max (.max (.succ u_α₂b') (.succ u_snd₂')) (.succ u_γ_out')
       , τ_f', f', ⟨heqb⟩⟩ ← to_lean f
       | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘ g)}"
    match τ_g' with
    | ~q(∀ (x : Shared ($α : (Type u_α₁'))), Σ (a : ($α' : Type u_α₁b')), (($β a) : (Type u_snd₁'))) =>
      let some β' ← checkTypeQ β q($α → Type u_snd₁')
        | throwError m!"composition right hand {g} is not well-typed in {(DCC f ∘ g)}"
      let g' ← checkTypeQ g' q(∀ (x : Shared ($α : (Type u_α₁'))), Σ (a : ($α : Type u_α₁')), (($β' a) : (Type u_snd₁')))
      match g' with
      | .some g' =>
        match τ_f' with
        | ~q(∀ (s : (Σ (a : ($α'' : Type u_α₂b')), ($β'' a :  Type u_snd₂'))), ($γ : Type u_γ_out')) =>
          let some γ' ← checkTypeQ γ q(∀ (s : (Σ (a : $α), $β' a)), Sort u_γ_out')
            | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘ g)}"
          let some f' ← checkTypeQ f' q(∀ (s : (Σ (a : $α), $β' a)), (($γ' s) : Sort u_γ_out'))
            | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘ g)}"
          pure ⟨.imax (.succ u_α₁) u_γ_out
            , _
            , q(∀ (x : Shared $α), $γ' ($g' x))
            , q(fun (x : Shared $α) => $f' ($g' x))
            , ⟨by
              simp [Level'.to_level] at heqa
              simp [Level'.to_level] at heqb
              simp [Level'.to_level, heqa.left, heqb.right]⟩⟩
        | _ => throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘ g)}"
      | _ => throwError m!"composition right hand {g} is not well-typed in {(DCC f ∘ g)}"
    | _ => throwError m!"composition right hand {g} is not well-typed in {(DCC f ∘ g)}"
  | (DCC f ∘' g)              =>
    let ⟨.max (.succ u_α₁) (.succ u_β₁)
       , .max (.succ u_α₁') (.succ u_β₁')
       , τ_g', g', ⟨heqa⟩⟩ ← to_lean g
       | throwError m!"composition right hand {g} is not well-typed in {(DCC f ∘' g)}"
    let ⟨.max (.succ u_β₂) (.succ u_γ₂)
       , .max (.succ u_β₂') (.succ u_γ₂')
       , τ_f', f', ⟨heqb⟩⟩ ← to_lean f
       | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
    match τ_g' with
    | ~q(∀ (x : ($α : (Type u_α₁'))), ($β : (Type u_β₁'))) =>
      match τ_f' with
      | ~q(∀ (x : $β₂), (($γ x) : Type u_γ₂')) =>
        match ← isLevelDefEqQ u_β₂' u_β₁' with
        | .defEq h =>
          let some γ' ← checkTypeQ γ q(∀ (x : ($β : Type u_β₁')), Sort u_γ₂')
            | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
          let some f' ← checkTypeQ f' q(∀ (x : ($β : (Type u_β₁'))), (($γ' x) : Sort u_γ₂'))
            | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
          pure ⟨.imax (.succ u_α₁) u_γ₂, _
            , q(∀ (x : ($α : (Type u_α₁'))), $γ' ($g' x))
            , q(fun (x : ($α : (Type u_α₁'))) => $f' ($g' x))
            , ⟨by
              simp [Level'.to_level] at heqa
              simp [Level'.to_level] at heqb
              simp [Level'.to_level, heqa.left, heqb.right]⟩⟩
        | _ => throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
      | _ => throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
    | _ => throwError m!"composition right hand {g} is not well-typed in {(DCC f ∘' g)}"
  | (DCC (f x)) =>
    let ⟨u_α₁, u_α₁', τ_x', x', ⟨heqa⟩⟩ ← to_lean x
    let ⟨.imax u_α₂ u_β₂, .imax u_α₂' u_β₂', τ_f', f', ⟨heqb⟩⟩ ← to_lean f
      | throwError m!"app function {f} is not well-typed in {(DCC (f x))}"
    match ← isLevelDefEqQ u_α₂' u_α₁' with
    | .defEq h =>
      match τ_f' with
      | ~q(∀ (x : ($τ_x'' : (Sort u_α₁'))), (($β x) : Sort u_β₂')) =>
        let some β ← checkTypeQ β q(∀ (x : ($τ_x' : (Sort u_α₁'))), Sort u_β₂')
          | throwError m!"app function {f} is not well-typed in {(DCC (f x))}"
        let some f' ← checkTypeQ f' q(∀ (x : ($τ_x' : (Sort u_α₁'))), (($β x) : Sort u_β₂'))
          | throwError m!"app function {f} is not well-typed in {(DCC (f x))}"
        pure ⟨u_β₂, _, q($β $x'), q($f' $x'), ⟨by
          simp [Level'.to_level] at heqb
          exact heqb.right⟩⟩
      | _ => throwError m!"app function {f} is not well-typed in {(DCC (f x))}"
    | _ => throwError m!"application type mismatch in {(DCC (f x))}"

end

end Expr

#check (Type 1 → Type 2 : Type ((max 1 2) + 1))

#check ∀ (s : Sigma (fun (x : Sort 1) => x)), (fun _x => Sigma (fun (x : Sort 1) => x)) s
