import Dcc.Nbe.Value
import Dcc.Nbe.Size
import Dcc.Metatheory.Value
import Dcc.Nbe.RunEvalApply

namespace Semantic

/-
For later: need this helper to extract out α in the identity η-reduction:

We already have apply and eval, so we're chilling pretty much.
We can calcuate the codomain, even.

Chilling.

Then plug this into:

| lam₃ : Apply Val(f) Val(neutral(var(level))) Val(neutral(var(level)))
    → Val.Quote level Val(f) e'

This is the identity. Plug in var 0, get out var 0, meaning it can reduce to Id(α).
Find α from domain.

Use apply defs to help with this.
Make an inductive for this + Val.domain def.
Take a nap first though.

Also lam₁ should probably just be Apply Val(f) not λ. However, that won't handle
Π.

Two approaches:

- Values are proof-carrying (potentially easier, it's by construction, but requries a bit of reworking - how does this interact with .lam? Probably fine, unless there's mutual induction from eval to apply (there is not))

  Counterpoint: all of our combinator points (type argument points which determine the domain) are already values. No need to embed.
-/

/-
Can just do mutual induction between Val.domain and Neutral.domain

Note:
- will need to write this as an inductive as well


Todo list:

5. Using new domain derivation, add η-rule for Id
  - Simultaneously abstract out the DoEta form Quote
  - Actually do this first to check if it works

1. (Easiest) Make vars type carrying (these can all be determined, even when we generate fresh variables)
2. (Easy-ish) Define Val.domain wrapper (should be somewhat blind to the structure of Neutral terms)
3. (Easy) Define NeutralTm.domain wrapper (does not require vars, easier)
  - Note: Sort, Top, Bot, etc... do not have domains. Will need to be Option at some point. that is fine.
4. (Medium) Neutral.domain (wrapper around NeutralTm + vars)
5. Update quote using domain
6. (Hard) I think we might need the "neutral" app case for Apply. Maybe? Probably not? Idk.
-/

mutual

/-
It may be prudent to make vars intrinsically typed.
Then, Neutral.domain is total, not Option
-/
inductive NeutralTm.Domain : (f : NeutralTm) → (α : Val) → Type

inductive Val.Domain : (f : Val) → (α : Val) → Type
  

end

/-
Need to handle constant values as well.

If f' does not contain the variable at all, then we are safe.
-/
inductive Val.DoEta : (level : ℕ) → (f : Val) → (f' : Neutral) → Type
  -- If the variable does not appear anywhere in the "substituted"
  -- environment, it must be a constant
  | const : Val.Domain f τ
    → Apply f Val(neutral(var((level) : τ))) v'
    → (¬ v'.contains_var level τ)
    → DoEta level f Neutral(`(τ, v'))
  | comp  : Val.Domain f τ
    → Apply f Val(neutral(var((level) : τ))) Val(neutral(f' neutral(var((level) : τ))))
    → DoEta level f Neutral(f')
  | id    : Val.Domain f τ
    → Apply f Val(neutral(var((level) : τ))) Val(neutral(var((level) : τ)))
    → DoEta level f Neutral(Id(τ))
  /-| pure  : Val.Domain f τ
    -- this is a partial application.
    -- for example, top-level Λ(α, β, x) y
    -- how does Λ(α, `(α, β), `(Coup(`(α, β)), x)) get η-reduced?
    -- e.g., to η-reduce it to `(α, `(β, y))
    -- we would need to test multiple arguments....
    -- Our highest arity term is Λ(α, β, x) with an arity of 2.
    -- so, we will need an η-rule for Λ, probably.
    → Apply f Val(neutral(var((level) : τ))) Val(λ env' n' => bdy')
  -- Λ(α, β, `(.., x)) y clearly η-reduces with the next argument,
  -- but two arguments is less clear.
  -- can we just apply two variables? The size should decrease.
  -- That seems fine. Yes.
  -- we need to know the arity here, clearly
  -- TODO: later, check this-/
  -- Λ(α, β, x) is the only combinator with an arity of 2.
  -- We apply two "fresh" variables to it,
  -- example: η-reducing: Λ(α, `(α, β), `(Coup(`(α, β)), x))
  -- apply fresh variable (0 : α)
  -- get λ ⟦(0 : α)⟧ 1 => Λ(α, `(α, β), `(Coup(`(α, β)), x))
  -- apply second variable (1 : β)
  -- get λ ⟦(1 : β), (0 : α)⟧ 0 => Λ(α, `(α, β), `(Coup(`(α, β)), x))
  -- supposing `(Coup(`(α, β)), x) ⟦`(α, β)⟧((0 : α), (1 : β)) → x'
  -- and x' is actually x, then this becomes `(α, `(β, x'))
  -- η-reducing Λ Curr is asking whether we can skip "coupling" the arguments
  -- that is, if
  -- If apply both arguments
  -- downgrading curry Λ(α, β, x) to quotation is primarily a question of downgrading a dependent type to
  -- we have a rule that already handles quotation.
  -- the main question is of whether or not the first component is used. kind of like 2-ary quote?
  -- if the first argument doesn't show up, we can quote it.
  -- however, this is already handled by quote rule, somewhat.
  -- assume x and y are opaque variables
  -- TODO: this rule is super confusing, and maybe handled by other cases already ?
  -- If curr apply gives x y z
  -- that means the "substituted" couple was fully destructured
  -- meaning, we can η-reduce to just x.
  /-| curr  : Val.Domain Val(λ env 2 => f) τ₁
    → Apply Val(λ env 2 => f) Val(neutral(var((level) : τ₁))) f'
    → Val.Domain f' τ₂
    → Apply f' Val(neutral(var((level) : τ₂))) -/
  -- Λ(α, β, x) takes a couple (y, z), but if y and z end up in term app position, that
  -- means the currying was a no-op
  | curr  : Apply β Val(neutral(var((level) : α))) βx
    → Apply x Val(neutral(⟦β⟧(neutral(var((level) : α)), neutral(var((level.succ) : βx)))))
      Val(neutral(x' neutral(var((level) : α)) neutral(var((level.succ) : βx))))
    → DoEta level Val(neutral(Λ(α, β, x))) Neutral(x')
  | curr' : Apply β Val(neutral(var((level) : α))) βx
    → Apply x Val(neutral(&(neutral(⟦β⟧(neutral(var((level) : α)), neutral(var((level.succ) : βx)))))))
      Val(neutral(x' (&(neutral(var((level) : α)))) (&(neutral(var((level.succ) : βx))))))
    → DoEta level Val(neutral(Λ(α, β, x))) Neutral(x')

/-
TODO ^ DoEta - feel like there are other cases I need to handle.
-/

theorem Val.DoEta.decreasing (h : DoEta level f f') : Val(neutral(f')).size < f.measure := by
  
  sorry

/-def 

def Val.domain (v : Val) : Option Expr :=
  match v with
  | Val(λ env n => bdy) =>
    sorry
  | Val(Π (f_α) env n, f_β) =>
    sorry
  | Neutral(-/

mutual

inductive Neutral.Quote : (level : ℕ) → (v : Neutral) → (e : Expr) → Type
  | tintro : Neutral.Quote level Neutral(∗) (DCC ∗)
  | top    : Neutral.Quote level Neutral(⊤) (DCC ⊤)
  | bot    : Neutral.Quote level Neutral(⊥) (DCC ⊥)
  | eq     : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(x = y) (DCC (x' = y'))
  | eql    : Val.Quote level α α' → Neutral.Quote level Neutral(Eql(α)) (DCC Eql(α'))
  | refl   : Val.Quote level α α' → Neutral.Quote level Neutral(refl(α)) (DCC refl(α'))
  | sort   : Neutral.Quote level Neutral(Sort m) (DCC Sort m)
  | sigma  : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(Σ(x, y)) (DCC (Σ(x', y')))
  | quot   : Val.Quote level β β' → Val.Quote level x x'
    → Neutral.Quote level Neutral(`(β, x)) (DCC `(β', x'))
  | coup   : Val.Quote level β β' → Val.Quote level x x'
    → Val.Quote level y y' → Neutral.Quote level Neutral(⟦β⟧(x, y)) (DCC ⟦β'⟧(x', y'))
  | t_coup : Val.Quote level β β' → Neutral.Quote level Neutral(Coup(β)) (DCC Coup(β'))
  | id     : Val.Quote level α α' → Neutral.Quote level Neutral(Id(α)) (DCC Id(α'))
  | fstc   : Val.Quote level α α' → Neutral.Quote level Neutral(Fstc(α)) (DCC Fstc(α'))
  | sndc   : Val.Quote level α α' → Neutral.Quote level Neutral(Sndc(α)) (DCC Sndc(α'))
  | comp'  : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(x ∘' y) (DCC (x' ∘' y'))
  | comp   : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(x ∘ y) (DCC (x' ∘ y'))
  | comp₂  : Val.Quote level x x' → Val.Quote level y y'
    → Neutral.Quote level Neutral(x ∘∘ y) (DCC (x' ∘∘ y'))
  | pair   : Val.Quote level β β' → Val.Quote level x x'
    → Val.Quote level y y' → Neutral.Quote level Neutral(⟦β⟧⟨x, y⟩) (DCC ⟦β'⟧⟨x', y'⟩)
  | curr   : Val.Quote level α α' → Val.Quote level β β'
    → Val.Quote level x x' → Neutral.Quote level Neutral(Λ(α, β, x)) (DCC Λ(α', β', x'))
  | curr'  : Val.Quote level α α' → Val.Quote level β β'
    → Val.Quote level x x' → Neutral.Quote level Neutral(!Λ(α, β, x)) (DCC !Λ(α', β', x'))
  | eval   : Val.Quote level α α' → Val.Quote level β β'
    → Val.Quote level x x' → Neutral.Quote level Neutral(Eval(α, β, x)) (DCC Eval(α', β', x'))
  | bang   : Val.Quote level x x' → Neutral.Quote level Neutral(!(x)) (DCC !(x'))
  | unbox  : Val.Quote level x x' → Neutral.Quote level Neutral(*(x)) (DCC *(x'))
  | boxed  : Val.Quote level x x' → Neutral.Quote level Neutral(&(x)) (DCC &(x'))
  | map    : Val.Quote level x x' → Neutral.Quote level Neutral(!<x>) (DCC !<x'>)
  | fmap   : Val.Quote level x x' → Neutral.Quote level Neutral($<x>) (DCC $<x'>)
  | app    : Neutral.Quote level f f' → Val.Quote level x x' → Neutral.Quote level Neutral(f x) (DCC (f' x'))

/-
Val(neutral(f' neutral(var(level))))
-/

inductive Val.Quote : (level : ℕ) → (v : Val) → (e : Expr) → Type
  | neut : Neutral.Quote level nv e → Val.Quote level Val(neutral(nv)) e
  | lam  : Val(λ env n => bdy).DoEta level f' → Neutral.Quote level.succ f' e' → Val.Quote level Val(λ env n => bdy) e'
  | pi₁  : Val.DoEta level f_α f_α' → Val.DoEta level.succ f_β f_β'
    → Neutral.Quote level f_α' f_α''
    → Neutral.Quote level.succ f_β' f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC Π(f_α'', f_β''))
  | pi₂  : Val.DoEta level f_α f_α' → Val.DoEta level.succ f_β f_β'
    → Neutral.Quote level f_α' f_α''
    → Neutral.Quote level.succ f_β' f_β''
    → Val.Quote level env env'
    → Val.Quote level Val(Π (f_α) ⟦env⟧ 0, f_β) (DCC (Π(f_α'', f_β'') env'))

/-inductive Val.Quote : (level : ℕ) → (v : Val) → (e : Expr) → Type
  | neut : Neutral.Quote level nv e → Val.Quote level Val(neutral(nv)) e
  | lam₁ : Val.Domain Val(λ env n => bdy) τ → Apply Val(λ env n => bdy) Val(neutral(var((level) : τ))) Val(neutral(f' neutral(var((level) : τ))))
    → Neutral.Quote level.succ f' e'
    → Val.Quote level Val(λ env n => bdy) e'
  -- This one is wrong. Should be quoting the raw expression. var should NOT be included in the environment
  | lam₂ : Val.Domain Val(λ env n => bdy) τ
    → Apply Val(λ env n => bdy) Val(neutral(var((level) : τ))) Val(λ env' n' => bdy')
    → Val.Quote level.succ Val(λ env' n' => bdy') e'
    → Val.Quote level Val(λ env n => bdy) e'
  /-
    We need to store context / types, so we can output Id(α).
    | lam₃ : Apply Val(λ env n => bdy) Val(neutral(var(level))) Val(neutral(var(level)))
    → Neutral.Quote level.succ f' e'
    → Val.Quote level Val(λ env n => bdy) e'-/
  | pi₁  : Val.Domain f_α τ₁
    → Apply f_α Val(neutral(var((level) : τ₁))) Val(neutral(f_α' neutral(var((level) : τ₁))))
    → Val.Domain f_β τ₂
    → Apply f_β Val(neutral(var((level) : τ₂))) Val(neutral(f_β' neutral(var((level) : τ₂))))
    → Neutral.Quote level.succ f_α' f_α''
    → Neutral.Quote level.succ.succ f_β' f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₂  : Val.Domain f_α τ₁
    → Apply f_α Val(neutral(var((level) : τ₁))) Val(λ env' n' => bdy')
    → Val.Domain f_β τ₂
    → Apply f_β Val(neutral(var((level) : τ₂))) Val(neutral(f_β' neutral(var((level) : τ₂))))
    → Val.Quote level.succ Val(λ env' n' => bdy') f_α''
    → Neutral.Quote level.succ.succ f_β' f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₃  : Val.Domain f_α τ₁
    → Apply f_α Val(neutral(var((level) : τ₁))) Val(neutral(f_α' neutral(var((level) : τ₁))))
    → Val.Domain f_β τ₂
    → Apply f_β Val(neutral(var((level) : τ₂))) Val(λ env' n' => bdy')
    → Neutral.Quote level.succ f_α' f_α''
    → Val.Quote level.succ.succ Val(λ env' n' => bdy') f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC (Π(f_α'', f_β'')))
  | pi₄ : Val.Domain f_α τ₁
    → Apply f_α Val(neutral(var((level) : τ₁))) Val(λ env'₁ n'₁ => bdy'₁)
    → Val.Domain f_β τ₂
    → Apply f_β Val(neutral(var((level) : τ₂))) Val(λ env'₂ n'₂ => bdy'₂)
    → Val.Quote level.succ Val(λ env'₁ n'₁ => bdy'₁) f_α''
    → Val.Quote level.succ.succ Val(λ env'₂ n'₂ => bdy'₂) f_β''
    → Val.Quote level Val(Π (f_α) ⟦⟧ 1, f_β) (DCC (Π(f_α'', f_β'')))
  | pi'₁ : Apply f_α env f_α₁
    → Val.Domain f_α₁ τ₁
    → Apply f_α₁ Val(neutral(var((level) : τ₁))) Val(neutral(f_α₂ neutral(var((level) : τ₁))))
    → Apply f_β env f_β₁
    → Val.Domain f_β₁ τ₂
    → Apply f_β₁ Val(neutral(var((level.succ) : τ₂))) Val(neutral(f_β₂ neutral(var((level.succ) : τ₂))))
    → Neutral.Quote level.succ f_α₂ f_α'
    → Neutral.Quote level.succ.succ f_β₂ f_β'
    → Val.Quote level env env'
    → Val.Quote level Val(Π (f_α) ⟦env⟧ 0, f_β) (DCC (Π(f_α', f_β') env'))-/

/-
Neutral case for Apply is absolutely necessary.

You can only detect eta-reducible when you get in-between a saturated reduction.

For example:
Id(α) x reduces to x.
where f := Id(α)

f is not eta-reducible.

Id(α) ∘ Id(α)
-/

end

mutual

def Neutral.quote (level : ℕ) (v : Neutral) : Option ((e : Expr) × v.Quote level e) :=
  match v with
  | Neutral(var((_v) : _τ)) => .none
  | Neutral(∗) => .some ⟨_, .tintro⟩
  | Neutral(⊤) => .some ⟨_, .top⟩
  | Neutral(⊥) => .some ⟨_, .bot⟩
  | Neutral(x = y) =>
    have h_dec₁ : x.measure < Neutral(x = y).size := by
      grind
    have h_dec₂ : y.measure < Neutral(x = y).size := by
      grind
    match x.quote level, y.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .eq h₁ h₂⟩
    | _, _ => .none
  | Neutral(Eql(α))  =>
    have h_dec₁ : α.measure < Neutral(Eql(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .eql h⟩
    | _ => .none
  | Neutral(refl(α))  =>
    have h_dec₁ : α.measure < Neutral(refl(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .refl h⟩
    | _ => .none
  | Neutral(Sort _m) => .some ⟨_, .sort⟩
  | Neutral(Σ(α, β)) =>
    have h_dec₁ : α.measure < Neutral(Σ(α, β)).size := by
      grind
    have h_dec₂ : β.measure < Neutral(Σ(α, β)).size := by
      grind
    match α.quote level, β.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .sigma h₁ h₂⟩
    | _, _ => .none
  | Neutral(`(β, x)) =>
    have h_dec₁ : β.measure < Neutral(`(β, x)).size := by
      grind
    have h_dec₂ : x.measure < Neutral(`(β, x)).size := by
      grind
    match β.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .quot h₁ h₂⟩
    | _, _ => .none
  | Neutral(⟦β⟧(x, y)) =>
    have h_dec₁ : β.measure < Neutral(⟦β⟧(x, y)).size := by
      grind
    have h_dec₂ : x.measure < Neutral(⟦β⟧(x, y)).size := by
      grind
    have h_dec₃ : y.measure < Neutral(⟦β⟧(x, y)).size := by
      grind
    match β.quote level, x.quote level, y.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .coup h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(Coup(β)) =>
    have h_dec₁ : β.measure < Neutral(Coup(β)).size := by
      grind
    match β.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .t_coup h⟩
    | _ => .none
  | Neutral(Id(α))      =>
    have h_dec₁ : α.measure < Neutral(Id(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .id h⟩
    | _ => .none
  | Neutral(Fstc(α))    =>
    have h_dec₁ : α.measure < Neutral(Fstc(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .fstc h⟩
    | _ => .none
  | Neutral(Sndc(α))    =>
    have h_dec₁ : α.measure < Neutral(Sndc(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .sndc h⟩
    | _ => .none
  | Neutral(f ∘' g) =>
    have h_dec₁ : f.measure < Neutral(f ∘' g).size := by
      grind
    have h_dec₂ : g.measure < Neutral(f ∘' g).size := by
      grind
    match f.quote level, g.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .comp' h₁ h₂⟩
    | _, _ => .none
  | Neutral(f ∘ g) =>
    have h_dec₁ : f.measure < Neutral(f ∘ g).size := by
      grind
    have h_dec₂ : g.measure < Neutral(f ∘ g).size := by
      grind
    match f.quote level, g.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .comp h₁ h₂⟩
    | _, _ => .none
  | Neutral(f ∘∘ g) =>
    have h_dec₁ : f.measure < Neutral(f ∘∘ g).size := by
      grind
    have h_dec₂ : g.measure < Neutral(f ∘∘ g).size := by
      grind
    match f.quote level, g.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .comp₂ h₁ h₂⟩
    | _, _ => .none
  | Neutral(⟦β⟧⟨x, y⟩) =>
    have h_dec₁ : β.measure < Neutral(⟦β⟧⟨x, y⟩).size := by
      grind
    have h_dec₂ : x.measure < Neutral(⟦β⟧⟨x, y⟩).size := by
      grind
    have h_dec₃ : y.measure < Neutral(⟦β⟧⟨x, y⟩).size := by
      grind
    match β.quote level, x.quote level, y.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .pair h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(Λ(α, β, x)) =>
    have h_dec₁ : α.measure < Neutral(Λ(α, β, x)).size := by
      grind
    have h_dec₂ : β.measure < Neutral(Λ(α, β, x)).size := by
      grind
    have h_dec₃ : x.measure < Neutral(Λ(α, β, x)).size := by
      grind
    match α.quote level, β.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .curr h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(!Λ(α, β, x)) =>
    have h_dec₁ : α.measure < Neutral(!Λ(α, β, x)).size := by
      grind
    have h_dec₂ : β.measure < Neutral(!Λ(α, β, x)).size := by
      grind
    have h_dec₃ : x.measure < Neutral(!Λ(α, β, x)).size := by
      grind
    match α.quote level, β.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .curr' h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(Eval(α, β, x)) =>
    have h_dec₁ : α.measure < Neutral(Eval(α, β, x)).size := by
      grind
    have h_dec₂ : β.measure < Neutral(Eval(α, β, x)).size := by
      grind
    have h_dec₃ : x.measure < Neutral(Eval(α, β, x)).size := by
      grind
    match α.quote level, β.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩, .some ⟨_, h₃⟩ =>
      .some ⟨_, .eval h₁ h₂ h₃⟩
    | _, _, _ => .none
  | Neutral(!(x))            =>
    have h_dec₁ : x.measure < Neutral(!(x)).size := by
      grind
    match x.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .bang h⟩
    | _ => .none
  | Neutral(*(α))            =>
    have h_dec₁ : α.measure < Neutral(*(α)).size := by
      grind
    match α.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .unbox h⟩
    | _ => .none
  | Neutral(&(x))            =>
    have h_dec₁ : x.measure < Neutral(&(x)).size := by
      grind
    match x.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .boxed h⟩
    | _ => .none
  | Neutral(!<x>)            =>
    have h_dec₁ : x.measure < Neutral(!<x>).size := by
      grind
    match x.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .map h⟩
    | _ => .none
  | Neutral($<x>)            =>
    have h_dec₁ : x.measure < Neutral($<x>).size := by
      grind
    match x.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .fmap h⟩
    | _ => .none
  | Neutral(f x)             =>
    have h_dec₁ : f.size < Neutral(f x).size := by
      grind
    have h_dec₂ : x.measure < Neutral(f x).size := by
      grind
    match f.quote level, x.quote level with
    | .some ⟨_, h₁⟩, .some ⟨_, h₂⟩ =>
      .some ⟨_, .app h₁ h₂⟩
    | _, _ => .none
termination_by (v.size, sizeOf v)

def Val.quote (level : ℕ) (v : Val) : Option ((e : Expr) × v.Quote level e) :=
  match v with
  | Val(neutral(neut)) =>
    have h_dec : neut.size ≤ Val(neutral(neut)).measure := by
      grind
    match neut.quote level with
    | .some ⟨_, h⟩ => .some ⟨_, .neut h⟩
    | _ => .none
  | Val(λ env n => bdy) =>
    match Val(λ env n => bdy).apply Val(neutral(var(level))) with
    | .some ⟨Val(neutral(f' neutral(var(level₂)))), h₁⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ : f'.size < (Val.neut (Neutral.tm (NeutralTm.app f' (Val.neut (Neutral.var level₂))))).measure := by
        grind
      have h_dec₃ : f'.size < Val(λ env n => bdy).measure := by
        grind
      if heq : level₂ = level then
        match f'.quote level.succ with
        | .some ⟨_, h₂⟩ =>
          heq ▸ .some ⟨_, .lam₁ (heq.symm ▸ h₁) (heq ▸ h₂)⟩
        | _ => .none
      else .none
    | .some ⟨Val(λ env' n' => bdy'), h₁⟩ =>
      have h_dec₁ : Val(λ env' n' => bdy').measure < Val(λ env n => bdy).measure + Val(neutral(var(level))).measure := h₁.decreasing
      have h_dec₂ : Val(λ env' n' => bdy').measure < Val(λ env n => bdy).measure := by
        grind
      match Val(λ env' n' => bdy').quote level.succ with
      | .some ⟨_, h₂⟩ =>
        .some ⟨_, .lam₂ h₁ h₂⟩
      | _ => .none
    | _ => .none
  | Val(Π (f_α) ⟦⟧ 1, f_β) =>
    match f_α.apply Val(neutral(var(level))), f_β.apply Val(neutral(var(level))) with
    | .some ⟨Val(neutral(f_α' neutral(var(level₂)))), h₁⟩,
      .some ⟨Val(neutral(f_β' neutral(var(level₃)))), h₂⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ : f_α'.size < Val(neutral(f_α' neutral(var(level)))).measure := by
        grind
      have h_dec₃ : f_α'.size < f_α.measure := by
        grind
      have h_dec₄ : f_α'.size < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        conv =>
          right
          simp [Val.measure]
          rfl
        grind
      have h_dec₅ := h₂.decreasing
      have h_dec₆ : f_β'.size < Val(neutral(f_β' neutral(var(level)))).measure := by
        grind
      have h_dec₇ : f_β'.size < f_β.measure := by
        grind
      have h_dec₈ : f_β'.size < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        conv =>
          right
          simp [Val.measure]
          rfl
        grind
      if heq₁ : level₂ = level then
        if heq₂ : level₃ = level then
          match f_α'.quote level.succ, f_β'.quote level.succ.succ with
          | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ => by
            cases heq₁; cases heq₂
            exact .some ⟨_, .pi₁ h₁ h₂ h₃ h₄⟩
          | _, _ => .none
        else .none
      else .none
    | .some ⟨Val(λ env' n' => bdy'), h₁⟩,
      .some ⟨Val(neutral(f_β' neutral(var(level₂)))), h₂⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ : Val(λ env' n' => bdy').measure < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        grind
      have h_dec₅ := h₂.decreasing
      have h_dec₆ : f_β'.size < Val(neutral(f_β' neutral(var(level)))).measure := by
        grind
      have h_dec₇ : f_β'.size < f_β.measure := by
        grind
      have h_dec₈ : f_β'.size < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        conv =>
          right
          simp [Val.measure]
          rfl
        grind
      if heq₁ : level₂ = level then
        match Val(λ env' n' => bdy').quote level.succ, f_β'.quote level.succ.succ with
        | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ => by
          cases heq₁
          exact .some ⟨_, .pi₂ h₁ h₂ h₃ h₄⟩
        | _, _ => .none
      else .none
    | .some ⟨Val(neutral(f_α' neutral(var(level₂)))), h₁⟩,
      .some ⟨Val(λ env' n' => bdy'), h₂⟩ =>
      have h_dec₁ := h₂.decreasing
      have h_dec₂ : Val(λ env' n' => bdy').measure < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        grind
      have h_dec₅ := h₁.decreasing
      have h_dec₆ : f_α'.size < Val(neutral(f_α' neutral(var(level)))).measure := by
        grind
      have h_dec₇ : f_α'.size < f_α.measure := by
        grind
      have h_dec₈ : f_α'.size < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        conv =>
          right
          simp [Val.measure]
          rfl
        grind
      if heq₁ : level₂ = level then
        match Val(λ env' n' => bdy').quote level.succ.succ, f_α'.quote level.succ with
        | .some ⟨_, h₄⟩, .some ⟨_, h₃⟩ => by
          cases heq₁
          exact .some ⟨_, .pi₃ h₁ h₂ h₃ h₄⟩
        | _, _ => .none
      else .none
    | .some ⟨Val(λ env'₁ n'₁ => bdy'₁), h₁⟩,
      .some ⟨Val(λ env'₂ n'₂ => bdy'₂), h₂⟩ =>
      have h_dec₁ := h₁.decreasing
      have h_dec₂ := h₂.decreasing
      have h_dec₃ : Val(λ env'₁ n'₁ => bdy'₁).measure < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        grind
      have h_dec₃ : Val(λ env'₂ n'₂ => bdy'₂).measure < Val(Π (f_α) ⟦⟧ 1, f_β).measure := by
        grind
      match Val(λ env'₁ n'₁ => bdy'₁).quote level.succ, Val(λ env'₂ n'₂ => bdy'₂).quote level.succ.succ with
      | .some ⟨_, h₃⟩, .some ⟨_, h₄⟩ => .some ⟨_, .pi₄ h₁ h₂ h₃ h₄⟩
      | _, _ => .none
    | _, _ => .none
  | Val(Π (f_α) ⟦env⟧ 0, f_β) => do
    let ⟨f_α₁, h₁⟩ ← f_α.apply env
    have h_dec₁ := h₁.decreasing
    have h_dec₁' : f_α₁.measure < Val(Π (f_α) ⟦env⟧ 0, f_β).measure := by
      grind
    let ⟨f_α₂, h₂⟩ ← f_α₁.apply Val(neutral(var(level)))
    let ⟨f_β₁, h₃⟩ ← f_β.apply env
    have h_dec₂ := h₂.decreasing
    have h_dec₃₃ := h₃.decreasing
    have h_dec₂' : f_β₁.measure < Val(Π (f_α) ⟦env⟧ 0, f_β).measure := by
      grind
    let ⟨f_β₂, h₄⟩ ← f_β₁.apply Val(neutral(var(level.succ)))
    have h_dec₃ := h₃.decreasing
    have h_dec₄ := h₄.decreasing
    match heq : f_α₂, f_β₂ with
    | Val(neutral(f_α₂' neutral(var(level₁)))), Val(neutral(f_β₂' neutral(var(level₂ + 1)))) =>
      if heq₁ : level₁ = level then
        if heq₂ : level₂ = level then
          have h_dec₅ : f_α₂'.size < (Val.pi [env] 0 f_α f_β).measure := by
            grind
          have h_dec₅ : f_β₂'.size < (Val.pi [env] 0 f_α f_β).measure := by
            grind
          let ⟨f_α', h₅⟩ ← f_α₂'.quote level.succ
          let ⟨f_β', h₆⟩ ← f_β₂'.quote level.succ.succ
          have h_env_dec : env.measure < (Val.pi [env] 0 f_α f_β).measure := by
            grind
          let ⟨env', h₇⟩ ← env.quote level
          by
            cases heq
            cases heq₁
            cases heq₂
            exact .some ⟨_, .pi'₁ h₁ h₂ h₃ h₄ h₅ h₆ h₇⟩
        else .none
      else .none
    | _, _ => .none
  | _ => .none
termination_by (v.measure, sizeOf v)

end

#check Val.quote

end Semantic

/-
Pattern mtaching in some constructors might be able to use quote / the bullet technique to do a form of extensionality.

For example, β : α → Sort n.
Currently, we just check
Reduces (f_β env) `(α, ...).

We can instead check similarly to in the Π case.

Or probably just doing reduce_nbe would get us there. tbh.
-/
