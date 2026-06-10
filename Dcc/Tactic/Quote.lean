import Dcc.Ast
import Dcc.Judge2
import Lean
import Qq
import Mathlib.Util.Qq

open Qq
open Lean.Meta

/-
Display DCC terms as lean expressions.
-/

inductive Level' where
  | zero : Level'
  | succ : Level' → Level'
  | imax : Level' → Level' → Level'
deriving DecidableEq

def Level.to_level' (l : Level) : Level' :=
  match l with
  | .zero => .zero
  | .succ n => .succ (Level.to_level' n)

def Level'.to_level (l : Level') : Lean.Level :=
  match l with
  | .zero => .zero
  | .succ n => .succ n.to_level
  | .imax m n => .imax m.to_level n.to_level

theorem Level'.to_level_comm : (Level'.to_level u).succ = (Level'.to_level u.succ) := by
  induction u
  any_goals (simp [to_level])

def Level'.to_level_expr (l : Level') : ((u : Lean.Level) × Q(Sort $u)) :=
  match l with
  | .zero => ⟨(Level'.succ .zero).to_level, q(Sort 0)⟩
  | .succ n => ⟨_, q(Sort $(n.to_level))⟩
  | .imax m n => ⟨_, q(Sort (imax $(m.to_level) $(n.to_level)))⟩

def Level.imax (l₁ l₂ : Level) : Level :=
  match l₁, l₂ with
  | _, .zero => .zero
  | m, .succ n => max m (.succ n)

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

partial def to_lean (e : Expr) : MetaM ((u : Level') × (u' : Lean.Level) × (α : Q(Sort $u')) × Q($α) × (PLift (u' = u.to_level))):= do
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
            simp [Level'.to_level_comm]⟩⟩
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
            simp [Level'.to_level_comm]⟩⟩
    | _ => throwError m!"Shared boxes can only live in Type: {e}"
  | (DCC Eval(α, β, x))       =>
    match ← α.to_lean with
    | ⟨.succ (.succ u), .succ (.succ u'), τ_α, α', ⟨heq⟩⟩ =>
      match τ_α with
      | ~q(Type u') =>
        match ← get_fn_ty_arrow β with
        | ⟨.succ (.succ u_α), .succ (.succ u_β), .succ (.succ u_α'), .succ (.succ u_β'), α'', β_cod, β', ⟨heqa⟩, ⟨heqb⟩⟩  =>
          if heq₁ : u_α = u then
            match ← isDefEqQ α' α'' with
            | .defEq heq₂ =>
              let u_β' := u_β.to_level
              --let u_β' := (Level'.succ u_β).to_level
              match β_cod with
              | ~q(Type u_β') =>
                match ← x.to_lean with
                | ⟨.imax (.imax (.succ (.succ u₂)) (.succ (.succ u_β₂))) (.succ (.succ u'₂)),
                  .imax (.imax (.succ (.succ u₂a)) (.succ (.succ u_β₂a))) (.succ (.succ u'₂a)), τ_x, x', ⟨heq₃⟩⟩ =>
                  if heq : u₂ = u then
                    if heqa : u_β₂ = u_β then
                        have α' : Q(Type u') := α'
                        have β_cod' : Q(Type u_β') := β_cod
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
              | _ => throwError m!"Eval body {β} is not uncurryable in: {e}"
            | _ => throwError m!"Eval body {α} is not uncurryable in: {e}"
          else throwError m!"Eval body {α} is not uncurryable in: {e}"
        | _ => throwError m!"Eval body {α} is not uncurryable in: {e}"
    | _ => throwError m!"Eval param {α} is not uncurryable in: {e}"
  | (DCC `(β, x))             => sorry
  | (DCC Id(α))               =>
    let α' := α.to_lean
    sorry
  | (DCC Sort m)              => sorry
  | (DCC Fstc(β))             => sorry
  | (DCC Sndc(β))             => sorry
  | (DCC Λ(α, β, e))          => sorry
  | (DCC !Λ(α, β, e))         => sorry
  | (DCC Π(α, β))             => sorry
  | (DCC ⟦β⟧⟨a, b⟩)           => sorry
  | (DCC ⟦β⟧(a, b))           => sorry
  | (DCC Coup(β))             => sorry
  | (DCC Σ(α, β))             => sorry
  | (DCC x = y)               => sorry
  | (DCC Eql(f_α))            => sorry
  | (DCC refl(f_α))           => sorry
  | (DCC f ∘ g)               => sorry
  | (DCC f ∘∘ g)              => sorry
  | (DCC f ∘' g)              => sorry
  | (DCC (f x))               => sorry

end

end Expr
