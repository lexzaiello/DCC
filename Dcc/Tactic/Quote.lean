import Dcc.Ast
import Dcc.Tactic.Debug
import Dcc.Judge2
import Lean
import Lean.ToExpr
import Lean.Meta.Basic
import Qq
import Mathlib.Util.Qq
import Qq.MetaM

open Qq
open Lean.Meta

/-
Display DCC terms as lean expressions.

TODO: Wrap sort types in PLift (e.g., propositions) so they can be used inside curry.
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
deriving DecidableEq, Inhabited

@[inline]
abbrev level'_from_nat (n : ℕ) : Level' :=
  match n with
  | .zero => .zero
  | .succ n => (level'_from_nat n).succ

def Level.to_level' (l : Level) : Level' :=
  match l with
  | .zero => .zero
  | .succ n => .succ (Level.to_level' n)

@[inline, reducible]
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

set_option linter.constructorNameAsVariable false
def to_lean (e : Expr) : MetaM ((u' : Lean.Level) × (α : Q(Sort $u')) × Q($α)):= do
  match e with
  | (DCC ⊤)                   => return ⟨(Lean.Level.succ .zero), q(Prop), q(True)⟩
  | (DCC ⊥)                   => return ⟨.succ .zero, q(Prop), q(False)⟩
  | (DCC ∗)                   => return ⟨.zero, q(True), q(True.intro)⟩
  | (DCC !<f>)                =>
    let ⟨.imax u' (.succ v'), τ_f', f'⟩ ← f.to_lean
      | throwError m!"Box function {f} is not well-typed at: {DCC !<f>}"
    match τ_f' with
    | ~q(∀ (x : ($α : (Sort u'))), Sort v') =>
      return ⟨.imax (.succ u') (.succ (.succ v'))
         , q(∀ (x : Shared $α), Type v'),
           q(fun (x : Shared $α) => Shared.map $f' x)⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC $<f>)                =>
    let ⟨.imax u' v', τ_f', f'⟩ ← f.to_lean
      | throwError m!"Box function {f} is not well-typed at: {DCC !<f>}"
    match τ_f' with
    | ~q(∀ (x : ($α : (Sort u'))), ($β x : Sort v')) =>
      return ⟨.imax (.succ u') (.succ v')
         , q(∀ (x : Shared $α), Shared ($β x.deref)),
           q(fun (x : Shared $α) => Shared.fmap $f' x)⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC &(x))                =>
    match ← x.to_lean with
    | ⟨u', α, x'⟩ => pure ⟨.succ u', q(Shared $α), q(Shared.share.{u'} $x')⟩
  | (DCC *(α))                =>
    match ← α.to_lean with
    | ⟨(.succ u'), τ_α, α'⟩ =>
      match τ_α with
      | ~q(Sort u') =>
        pure ⟨_, q((Shared $α') → $α'), q(fun (x : Shared $α') => x.deref)⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC !(α))                =>
    match ← α.to_lean with
    | ⟨(.succ u'), τ_α, α'⟩ =>
      match τ_α with
      | ~q(Sort u') =>
        pure ⟨.succ (.succ u'), q(Sort (u' + 1)), q(Shared $α')⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC Eval(α, β, x))       =>
    match ← α.to_lean with
    | ⟨.succ u', τ_α, α'⟩ =>
      match τ_α with
      | ~q(Sort u') =>
        let ⟨(.imax u_α' (.succ u_β')), τ_β, β'⟩ ← β.to_lean
          | throwError m!"Eval second arg {β} is not well-typed in: {(DCC Eval(α, β, x))}"
        match τ_β with
        | ~q(∀ (x : ($α : (Sort u_α'))), Sort u_β') =>
          match ← isDefEqQ α' α with
          | .defEq heq₂ =>
            match ← x.to_lean with
            | ⟨.imax u₂a (.imax u_β₂a u'₂a), τ_x, x'⟩ =>
              have α' : Q(Sort u') := α'
              have β' : Q($α' → Sort u_β') := β'
              match τ_x with
              | ~q(∀ (x : ($α' : Sort u₂a)) (y : ($β' : $α' → Sort u_β₂a) x),
                ($γ : ∀ (x : $α') (y : $β' x), Sort u'₂a) x y) =>
                .pure ⟨.imax (.max (.max 1 u₂a) u_β₂a) u'₂a,
                  q(∀ (s : (Σ' (x : $α'), $β' x)), $γ s.fst s.snd)
                  , q(fun (s : (Σ' (x : $α'),$β' x)) => $x' s.fst s.snd)⟩
              | _ => throwError m!"Eval body {x} is not uncurryable in: {e}"
            | _ => throwError m!"Eval body {β} is not uncurryable in: {e}"
          | _ => throwError m!"Eval body {α} is not uncurryable in: {e}"
        | _ => throwError m!"Eval body {β} is not uncurryable in: {e}"
    | _ => throwError m!"Eval param {α} is not uncurryable in: {e}"
  | (DCC `(β, x))             =>
    match ← β.to_lean, ← x.to_lean with
    | ⟨.succ u', τ_β, β'⟩, ⟨v', τ_x, x'⟩ =>
      match τ_β with
      | ~q(Sort u') =>
        .pure ⟨Lean.Level.imax u' v',
          q($β' → $τ_x), q(fun (y : $β') => $x')⟩
    | _, _ => throwError "invalid quotation"
  | (DCC Id(α))               =>
    let ⟨.succ u_a, τ_α, α'⟩ ← α.to_lean
      | throwError "not a valid type"
    match τ_α with
    | ~q(Sort u_a) =>
      pure ⟨.imax u_a u_a, q($α' → $α'), q(fun (x : $α') => x)⟩
    | _ => throwError "not a valid type"
  | (DCC Sort m)              =>
    let m₀  := (level'_from_nat m)
    let m'  := m₀.to_level
    let s₁  := Lean.Expr.sort m'.succ
    let s₂ := Lean.Expr.sort m'
    let some s₁' ← checkTypeQ s₁ q(Type (m' + 1))
      | throwError m!"not a valid sort: {e}"
    let some s₂' ← checkTypeQ s₂ q(Type m')
      | throwError m!"not a valid sort: {e}"
    pure <| ⟨m'.succ.succ, s₁, s₂⟩
  | (DCC Fstc(β))             =>
    match ← β.to_lean with
    | ⟨.imax u' (.succ u_α'), τ_β, β'⟩ =>
      match τ_β with
      | ~q(∀ (x : ($α : Sort u')), Sort u_α') =>
        pure ⟨Lean.Level.imax (.max (.max 1 u') u_α') u',
          q(∀ (x : Σ' a : $α, $β' a), $α), q(fun (x : Σ' a : $α, $β' a) => PSigma.fst x)⟩
      | τ_β => throwError m!"not a well-typed projection (Fst : {τ_β}) index: {β}"
    | _ => throwError m!"not a valid projection (Fst) index: {β}"
  | (DCC Sndc(β))             =>
    match ← β.to_lean with
    | ⟨.imax u' (.succ u_α'), τ_β, β'⟩ =>
      match τ_β with
      | ~q(∀ (x : ($α : Sort u')), Sort u_α') =>
        pure ⟨(Lean.Level.imax (.max (.max 1 u') u_α') u_α'),
          q(∀ (x : Σ' a : $α, $β' a), $β' (PSigma.fst x)), q(fun (x : Σ' a : $α, $β' a) => PSigma.snd x)⟩
      | _ => throwError m!"not a well-typed projection (Fst) index: {β}"
    | _ => throwError m!"not a valid projection (Fst) index: {β}"
  | (DCC Λ(α, β, x))          =>
    -- switch τ_α to Sort u'?
    match ← α.to_lean with
    | ⟨.succ u', τ_α, α'⟩ =>
      match τ_α with
      | ~q(Sort u') =>
        let ⟨.imax u_α' (.succ u_β'), τ_β, β'⟩ ← β.to_lean
          | throwError m!"Curry second arg {β} is not well-typed in: {(DCC Λ(α, β, e))}"
        match τ_β with
        | ~q(∀ (x : ($α₂ : (Sort u_α'))), Sort u_β') =>
          match ← isLevelDefEqQ u' u_α' with
          | .defEq h =>
            match ← isDefEqQ α' α₂ with
            | .defEq heq₂ =>
              --let u_β' := u_β.to_level
              --let u_β' := (Level'.succ u_β).to_level
              let ⟨u_a, _, _⟩ ← x.to_lean
              let ⟨.imax (.max (.max 1 u_α₂') u_β₂') u_e₂', τ_x, x'⟩ ← x.to_lean
                | throwError m!"this should not be reachable (curry)"
              have β' : Q($α' → Sort u_β') := β'
              match ← isLevelDefEqQ u_α₂' u_α' with
              | .defEq h =>
                match ← isLevelDefEqQ u_β₂' u_β' with
                | .defEq h₂ =>
                  match τ_x with
                  | ~q(∀ (s : Σ' (a : ($α' : (Sort u_α'))), (($β' a) : Sort u_β')), (($γ s) : Sort u_e₂')) =>
                    pure ⟨Lean.Level.imax u' (Lean.Level.imax u_β' u_e₂'),
                      q(∀ (x : $α') (y : $β' x), $γ (PSigma.mk x y)),
                      q(fun (x : $α') (y : $β' x) => ($x' (PSigma.mk x y)))⟩
                  | _ => throwError m!"Curry body {x} is not curryable in: {e}"
                | _ => throwError m!"[5] Curry param {β} is not curryable in: {e}"
              | _ => throwError m!"[4] Curry param {α} is not curryable in: {e}"
            | _ => throwError m!"[3] Curry param {α} is not curryable in: {e}"
          | _ => throwError m!"[2] Curry param {α} is not curryable in: {e}"
        | _ => throwError m!"Curry param {β} is not curryable in: {e}"
    | _ => throwError m!"Curry param {α} is not curryable in: {e}"
  | (DCC !Λ(α, β, x))          =>
    -- switch τ_α to Sort u'?
    match ← α.to_lean with
    | ⟨.succ u', τ_α, α'⟩ =>
      match τ_α with
      | ~q(Sort u') =>
        let ⟨.imax u_α' (.succ u_β'), τ_β, β'⟩ ← β.to_lean
          | throwError m!"!Curry second arg {β} is not well-typed in: {(DCC Λ(α, β, e))}"
        match τ_β with
        | ~q(∀ (x : ($α₂ : (Sort u_α'))), Sort u_β') =>
          match ← isLevelDefEqQ u' u_α' with
          | .defEq h =>
            match ← isDefEqQ α' α₂ with
            | .defEq heq₂ =>
              --let u_β' := u_β.to_level
              --let u_β' := (Level'.succ u_β).to_level
              let ⟨u_a, _, _⟩ ← x.to_lean
              let ⟨.imax (.succ (.max (.max 1 u_α₂') u_β₂')) u_e₂', τ_x, x'⟩ ← x.to_lean
                | throwError m!"this should not be reachable (curry)"
              have β' : Q($α' → Sort u_β') := β'
              match ← isLevelDefEqQ u_α₂' u_α' with
              | .defEq h =>
                match ← isLevelDefEqQ u_β₂' u_β' with
                | .defEq h₂ =>
                  match τ_x with
                  | ~q(∀ (s : Shared (Σ' (a : ($α' : (Sort u_α'))), (($β' a) : Sort u_β'))), (($γ s) : Sort u_e₂')) =>
                    pure ⟨Lean.Level.imax (.succ u') (Lean.Level.imax (Lean.Level.succ u_β') u_e₂'),
                      q(∀ (x : Shared $α') (y : Shared ($β' x.deref)), $γ (Shared.share (PSigma.mk x.deref y.deref))),
                      q(fun (x : Shared $α') (y : Shared ($β' x.deref)) => ($x' (Shared.share (PSigma.mk x.deref y.deref))))⟩
                  | _ => throwError m!"!Curry body {x} is not curryable in: {e}"
                | _ => throwError m!"!Curry body {β} is not curryable in: {e}"
              | _ => throwError m!"!Curry body {α} is not curryable in: {e}"
            | _ => throwError m!"!Curry body {α} is not curryable in: {e}"
          | _ => throwError m!"!Curry body {α} is not curryable in: {e}"
        | _ => throwError m!"!Curry body {α} is not curryable in: {e}"
    | _ => throwError m!"!Curry param {α} is not curryable in: {e}"
  | (DCC Π(α, β))             =>
    let ⟨.imax u_δ₁' (.succ u_α₁')
      , ~q($δ → Sort u_α₁'), f_α'⟩ ← to_lean α
      | throwError m!"Π domain function {α} is not well-typed at {(DCC Π(α, β))}"
    let ⟨.imax _a₂ (.imax _b₂ (.succ u_β₂'))
      , τ_f_β', f_β'⟩ ← to_lean β
      | throwError m!"[1] Π codomain function {β} is not well-typed at {(DCC Π(α, β))}"
    match τ_f_β' with
    | ~q(∀ (env : ($δ' : Sort _a₂)) (α : (($f_α' env) : Sort _b₂)), Sort u_β₂') =>
      let some f_β'' ← checkTypeQ f_β' q(∀ (env : $δ') (α : $f_α' env), Sort u_β₂')
        | throwError m!"[2] Π codomain function {β} is not well-typed at {(DCC Π(α, β))}"
      pure ⟨.imax _a₂ (.succ (.imax _b₂ u_β₂'))
        , q($δ' → Sort (imax _b₂ u_β₂'))
        , q(fun (env : $δ') => (∀ (x : $f_α' env), $f_β'' env x))⟩
    | ~q(∀ (env : ($δ' : Sort _a₂)) (_x : ($α' : Sort _b₂)), Sort u_β₂') =>
      let some f_β'' ← checkTypeQ f_β' q(∀ (env : $δ) (_x : $α'), Sort u_β₂')
        | throwError m!"[3] Π codomain function {β} is not well-typed at {(DCC Π(α, β))}"
      pure ⟨.imax u_δ₁' (.succ (.imax _b₂ u_β₂'))
        , q($δ → Sort (imax _b₂ u_β₂'))
        , q(fun (env : $δ) => (∀ (x : $α'), $f_β'' env x))⟩
    | _ => throwError m!"[4] Π codomain function {β} is not well-typed at {(DCC Π(α, β))}"
  | (DCC ⟦β⟧⟨a, b⟩)           =>
    let ⟨.imax u_α₁' (.imax u_fst₁' u_snd₁')
       , τ_b', b'⟩ ← to_lean b
       | throwError m!"pair snd function {b} is not well-typed at {(DCC ⟦β⟧⟨a, b⟩)}"
    let ⟨.imax u_α₂' u_fst₂'
       , τ_a', a'⟩ ← to_lean a
       | throwError m!"pair snd function {a} is not well-typed at {(DCC ⟦β⟧⟨a, b⟩)}"
    let ⟨.imax u_α₃' u_β₃'
       , τ_β', β'⟩ ← to_lean β
       | throwError m!"pair couple-image function {β} is not well-typed at {(DCC ⟦β⟧⟨a, b⟩)}"
    match τ_b' with
    | ~q(∀ (x : ($α : Sort u_α₁'))
      (y : (($f_β x) : Sort u_fst₁')), (($γ x y) : Sort u_snd₁')) =>
      let some a' ← checkTypeQ a' q(∀ (x : $α), $f_β x)
        | throwError m!"pair snd function {a} is not well-typed at {(DCC ⟦β⟧⟨a, b⟩)}"
      pure ⟨.imax (.succ u_α₁') (.max (.max 1 u_fst₁') u_snd₁')
          , q(∀ (x : (Shared $α)), Σ' (a : ($f_β x.deref)), $γ x.deref a)
          , q(fun (x : (Shared $α)) => PSigma.mk ($a' x.deref) ($b' x.deref ($a' x.deref)))⟩
    | τ_β' => throwError m!"pair snd function {b} has type: {τ_β'}, but that was not expected at {(DCC ⟦β⟧⟨a, b⟩)}"
  | (DCC ⟦β⟧(a, b))           =>
    let ⟨.imax _u _v
       , τ_β, β'⟩ ← to_lean β
       | throwError m!"couple snd type {β} is not well-typed at {(DCC ⟦β⟧(a, b))}"
    let ⟨u_fst₂'
        , τ_a, a'⟩ ← to_lean a
    let ⟨u_snd₂', τ_b, b'⟩ ← to_lean b
    let some β' ← checkTypeQ β' q($τ_a → (Sort u_snd₂'))
      | throwError m!"couple snd type {β} ({τ_β}) is not well-typed at with respect to fst type {τ_a} and snd type {τ_b} {(DCC ⟦β⟧(a, b))}"
    let b' ← checkTypeQ b' q($β' $a')
    match b' with
    | .some b' =>
      pure ⟨(.max (.max 1 u_fst₂') u_snd₂'),
        q(Σ' (a : $τ_a), $β' a), q(PSigma.mk $a' $b')⟩
    | .none => throwError m!"couple snd {b} is not well-typed at {(DCC ⟦β⟧(a, b))}"
  | (DCC Coup(β))             =>
    let ⟨.imax u_fst₁' (.succ u_snd₁')
       , τ_β, β'⟩ ← to_lean β
       | throwError m!"couple snd type {β} is not well-typed at {(DCC Coup(β))}"
    match τ_β with
    | ~q(∀ (x : ($α : Sort u_fst₁')), Sort u_snd₁') =>
      let β' ← checkTypeQ β' q(∀ (x : ($α : Sort u_fst₁')), Sort u_snd₁')
      pure ⟨(.succ (.max (.max 1 u_fst₁') u_snd₁'))
        , q(Sort (max (max 1 u_fst₁') u_snd₁'))
        , q(Σ' (a : $α), $β' a)⟩
    | _ =>  throwError m!"couple type type {β} is not well-typed at {(DCC Coup(β))}"
  | (DCC Σ(_f_α, f_β))             =>
    let ⟨.imax u_env₁' (.imax u_α₁' (.succ u_srt₁'))
      , τ_f_β', f_β'⟩ ← to_lean f_β
      | throwError m!"Σ domain function {f_β} is not well-typed at {(DCC Σ(_f_α, f_β))}"
    -- (u_env₁'.max u_srt₁'.succ.succ).max u_α₁'.succ.succ = ((u_env₁.max u_srt₁.succ.succ).imax u_α₁.succ.succ).to_level
    match τ_f_β' with
    | ~q(∀ (env : ($α : (Sort u_env₁'))) (x : (($f_α env) : (Sort u_α₁'))), Sort u_srt₁') =>
      pure ⟨.imax u_env₁' (.succ (.max (.max 1 u_α₁') u_srt₁'))
        , q($α → Sort (max (max 1 u_α₁') u_srt₁'))
        , q(fun (env : $α) => Σ' (a : $f_α env), ($f_β' env a))⟩
    | _ => throwError m!"Σ domain function {f_β} is not well-typed at {(DCC Σ(_f_α, f_β))}"
  | (DCC x = y)               =>
    let ⟨srt_x', τ_x, x'⟩ ← to_lean x
    let ⟨srt_y', τ_y, y'⟩ ← to_lean y
    let some y' ← checkTypeQ y' τ_x
      | throwError m!"second component {y} is not well-typed in {(DCC (x = y))}"
    pure ⟨.succ .zero, q(Prop), q($x' = $y')⟩
  | (DCC Eql(f_α))            =>
    let ⟨.max (.succ u_env₁') (.succ (.succ u_srt₁'))
      , τ_f_α', f_α'⟩ ← to_lean f_α
      | throwError m!"environment index {f_α} is not well-typed in {(DCC (Eql(f_α)))}"
    match τ_f_α' with
    | ~q(∀ (env : ($α : (Type u_env₁'))), Type u_srt₁') =>
      pure ⟨.imax (.succ u_env₁'.succ) (.succ u_srt₁'.succ)
        , q(∀ (env : Shared $α) (x : Shared ($f_α' env.deref)), Prop)
        , q(fun (env : Shared $α) (x : Shared ($f_α' env.deref)) => x.deref = x.deref)⟩
    | _ => throwError m!"environment index {f_α} is not well-typed in {(DCC (Eql(f_α)))}"
  | (DCC refl(f_α))            =>
    let ⟨.imax u_env₁' (.succ u_srt₁')
      , τ_f_α', f_α'⟩ ← to_lean f_α
      | throwError m!"environment index {f_α} is not well-typed in {(DCC (Eql(f_α)))}"
    match τ_f_α' with
    | ~q(∀ (env : ($α : (Sort u_env₁'))), Sort u_srt₁') =>
      pure ⟨.imax (.succ u_env₁') (.imax (.succ u_srt₁') .zero)
        , q(∀ (env : Shared $α) (x : Shared ($f_α' env.deref)), x.deref = x.deref)
        , q(fun (env : Shared $α) (x : Shared ($f_α' env.deref)) => Eq.refl x.deref)⟩
    | _ => throwError m!"environment index {f_α} is not well-typed in {(DCC (Eql(f_α)))}"
  | (DCC f ∘∘ g)
  | (DCC f ∘ g)               =>
    /-
      g : α → Σ (a : α) × β
      f : ∀ (s : Σ (a : α) × β), γ s
    -/
    let ⟨.imax (.succ u_α₁') (.max (.max 1 u_α₁b') u_snd₁')
      , τ_g', g'⟩ ← to_lean g
      | throwError m!"[1] composition right hand {g} is not well-typed in {(DCC f ∘ g)}"
    let ⟨.imax (.max (.max 1 u_α₂b') u_snd₂') u_γ_out'
       , τ_f', f'⟩ ← to_lean f
       | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘ g)}"
    let τ_g' : Q(Sort (imax (u_α₁' + 1) (max (max 1 u_α₁b') u_snd₁'))) ← Lean.Meta.reduceAll (← whnf τ_g')
    match τ_g' with
    | ~q(∀ (x : Shared ($α : (Sort u_α₁'))), Σ' (a : ($α' : Sort u_α₁b')), (($β a) : (Sort u_snd₁'))) =>
      let some β' ← checkTypeQ β q($α' → Sort u_snd₁')
        | throwError m!"[2] composition right hand {g} is not well-typed in {(DCC f ∘ g)}"
      let g' ← checkTypeQ g' q(∀ (x : Shared ($α : (Sort u_α₁'))), Σ' (a : ($α' : Sort u_α₁b')),
        (($β' a) : (Sort u_snd₁')))
      match g' with
      | .some g' =>
        match τ_f' with
        | ~q(∀ (s : (Σ' (a : ($α'' : Sort u_α₂b')), ($β'' a :  Sort u_snd₂'))), ($γ : Sort u_γ_out')) =>
          let some γ' ← checkTypeQ γ q(∀ (s : (Σ' (a : $α'), $β' a)), Sort u_γ_out')
            | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘ g)}"
          let some f' ← checkTypeQ f' q(∀ (s : (Σ' (a : $α'), $β' a)), (($γ' s) : Sort u_γ_out'))
            | throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘ g)}"
          pure ⟨.imax (.succ u_α₁') u_γ_out'
            , q(∀ (x : Shared $α), $γ' ($g' x))
            , q(fun (x : Shared $α) => $f' ($g' x))⟩
        | _ => throwError m!"composition left hand {f} is not well-typed in {(DCC f ∘ g)}"
      | _ => throwError m!"[3] composition right hand {g} is not well-typed in {(DCC f ∘ g)}"
    | _ =>
      if h : τ_f'.isForall then
        let dom := τ_f'.forallDomain h
        let e' := Lean.Expr.lam .anonymous dom (.app f' (.app g' (.bvar 0))) .default
        let ⟨u, τ, e'⟩ ← inferTypeQ e'
        pure ⟨u, τ, e'⟩
      else
        throwError m!"composition left hand {f} is not a function in {(DCC (f ∘ g))}"
    | _ => throwError m!"[4] composition right hand ({g} : {τ_g'}) is not well-typed in {(DCC f ∘ g)}
where ({f} : {τ_f'})"
  | (DCC f ∘' g)              =>
    let ⟨.imax u_α₁' u_β₁'
       , τ_g', g'⟩ ← to_lean g
       | throwError m!"composition right hand {g} is not well-typed in {(DCC f ∘' g)}"
    let ⟨.imax u_β₂' u_γ₂'
       , τ_f', f'⟩ ← to_lean f
       | throwError m!"[1] composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
    match τ_g' with
    | ~q(∀ (x : ($α : (Sort u_α₁'))), ($β : (Sort u_β₁'))) =>
      match τ_f' with
      | ~q(∀ (x : ($β₂ : Sort u_β₂')), (($γ x) : Sort u_γ₂')) =>
        match ← isLevelDefEqQ u_β₂' u_β₁' with
        | .defEq h =>
          let some γ' ← checkTypeQ γ q(∀ (x : ($β : Sort u_β₁')), Sort u_γ₂')
            | throwError m!"[2] composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
          let some f' ← checkTypeQ f' q(∀ (x : ($β : (Sort u_β₁'))), (($γ' x) : Sort u_γ₂'))
            | throwError m!"[3] composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
          pure ⟨.imax u_α₁' u_γ₂'
            , q(∀ (x : ($α : (Sort u_α₁'))), $γ' ($g' x))
            , q(fun (x : ($α : (Sort u_α₁'))) => $f' ($g' x))⟩
        | _ => throwError m!"[4] composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
      | _ => throwError m!"[5] composition left hand {f} is not well-typed in {(DCC f ∘' g)}"
    | _ => throwError m!"[6] composition right hand {g} is not well-typed in {(DCC f ∘' g)}"
  | (DCC (f x)) =>
    let ⟨u_α₁', τ_x', x'⟩ ← to_lean x
    let ⟨.imax u_α₂' u_β₂', τ_f', f'⟩ ← to_lean f
      | throwError m!"[1] app function {f} is not well-typed in {(DCC (f x))}"
    match ← isLevelDefEqQ u_α₂' u_α₁' with
    | .defEq h =>
      match τ_f' with
      | ~q(∀ (x : ($τ_x'' : Sort u_α₁')), (($β x) : Sort u_β₂')) =>
        let some β ← checkTypeQ β q(∀ (x : $τ_x'), Sort u_β₂')
          | throwError m!"app function {f} codomain is not well-typed in {(DCC (f x))}"
        let some f' ← checkTypeQ f' q(∀ (x : $τ_x'), (($β x) : Sort u_β₂'))
          | throwError m!"app function {f} domain is not well-typed in {(DCC (f x))}"
        let some x' ← checkTypeQ x' τ_x'
          | throwError m!"app arg {x} is not well-typed in {(DCC (f x))}"
        pure ⟨u_β₂', q($β $x'), q($f' $x')⟩
      | ~q((($τ_x') : Sort u_α₁') → ($β : Sort u_β₂')) =>
        let some f' ← checkTypeQ f' q(∀ (x : ($τ_x' : (Sort u_α₁'))), ($β : Sort u_β₂'))
          | throwError m!"app function {f} domain is not well-typed in {(DCC (f x))}"
        let some x' ← checkTypeQ x' τ_x'
          | throwError m!"app arg {x} is not well-typed in {(DCC (f x))}"
        pure ⟨u_β₂', β, q($f' $x')⟩
      | τ => throwError m!"[2] app function ({f} : {τ}) is not well-typed in {(DCC (f x))}"
    | _ => throwError m!"application type mismatch in {(DCC (f x))}
universe levels are not aligned: {u_α₂'} {u_α₁'}"

end Expr

#check (Type 1 → Type 2 : Type ((max 1 2) + 1))

#check ∀ (s : Sigma (fun (x : Sort 1) => x)), (fun _x => Sigma (fun (x : Sort 1) => x)) s

open Lean.Elab in
open Lean.Elab.Term in
elab "dcc_decompile" e:gen_dcc : term => do
  let tm ← match e with
  | `(gen_dcc| #($tm:term)) =>
    let tm₀ ← elabTerm tm none
    pure <| ((← unfoldDefinition? tm₀ (ignoreTransparency := true)) <|> (← delta? tm₀)).getD (← whnf tm₀)
  | _ =>
    elabTerm (← liftMacroM <| runDcc e) none
  let dcc_e ← decode_dcc tm
  let ⟨_u, _α, lean_e⟩ ← dcc_e.to_lean
  return lean_e

open Lean.Elab in
open Lean.Elab.Term in
open Lean.Elab.Command in
elab "dcc_show" e:gen_dcc : command => do
  liftTermElabM do
    let tm ← match e with
    | `(gen_dcc| #($tm:term)) =>
      let tm₀ ← elabTerm tm none
      pure <| ((← unfoldDefinition? tm₀ (ignoreTransparency := true)) <|> (← delta? tm₀)).getD (← whnf tm₀)
    | _ =>
      elabTerm (← liftMacroM <| runDcc e) none
    let dcc_e ← decode_dcc tm
    let ⟨_u, _α, lean_e⟩ ← dcc_e.to_lean
    Lean.logInfo m!"{lean_e}"

#check dcc_decompile (Id(Sort 0))
#check dcc_decompile (Id(Sort 0) ⊤)
dcc_show (Id(Sort 0))
#check dcc_decompile (⟦Id(Sort 1)⟧(Sort 0, ⊤))
dcc_show (⟦Id(Sort 1)⟧(Sort 0, ⊤))
dcc_show (⟦Id(Sort 1)⟧(Sort 0, ⊤))
