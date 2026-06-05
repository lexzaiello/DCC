import Dcc.Nbe.Value
import Dcc.Aff.Red

namespace Semantic

/-
Note: RedAff reduction will leave no apps remaining, period.
-/

/-
Notes:

- There is zero reason to have raw at all.
We don't use variables anyway.
This just introduces complexity in the decreasing size argument.
We would like to just work with Val. Then no bridging lemmas required.

We might be able to use β-reduction in some places, idk.
-/


-- Rewrites

inductive Apply : (f : Val) → (x : Val) → Val → Type
  | eql₁     : Apply Val(λ xs 2 => Eql(f_α)) Val(neutral(&(env))) Val(λ xs 1 => Eql(f_α))
  | eql₂     : Apply Val(λ env 1 => Eql(f_α)) Val(neutral(&(x))) Val(neutral(x = x))
  | unbox    : Apply Val(λ env 1 => *(α)) Val(neutral(&(x))) Val(x)
  | id       : Apply Val(λ env 1 => Id(α)) x x
  | fstc     : Apply Val(λ env 1 => Fstc(_α)) Val(neutral(⟦β⟧(a, b))) a
  | sndc     : Apply Val(λ env 1 => Sndc(_α)) Val(neutral(⟦β⟧(a, b))) b
  | curr₁    : Apply Val(λ env 2 => Λ(α, β, x)) y Val(λ y::env 1 => Λ(α, β, x))
  | curr'₁   : Apply Val(λ env 2 => !Λ(α, β, x)) Val(neutral(&(y))) Val(λ neutral(&(y))::env 1 => !Λ(α, β, x))
  | map      : Apply f x e'
    → Apply Val(λ env 1 => !<f>) Val(neutral(&(x))) Val(neutral(!(e')))
  | fmap     : Apply f x e' → Apply Val(λ env 1 => $<f>) Val(neutral(&(x))) Val(neutral(&(e')))
  -- TODO: will need size measure or use β instead, show it is a Val.
  -- we can definitely do a decreasing size. we will just need to rework Λ, probably.
  -- we can separate out our simple rewrite rule ones from our actual ones.
  | pair     : Apply M x a
    → Apply N x b
    → Apply b a c
    → Apply Val(λ env 1 => ⟦β⟧⟨M, N⟩) Val(neutral(&(x)))
      Val(neutral(⟦β⟧(a, c)))
  | eval     : Apply x y f'
    → Apply f' z e'
    → Apply Val(λ env 1 => Eval(_α, _β, x)) Val(neutral(⟦__β⟧(y, z))) e'
  | quot     : Apply Val(λ env 1 => `(β, x)) y x
  -- f ∘ g x
  -- again, need to handle second round
  -- can use β-reducer for this.
  | comp'    : Apply g x A  → Apply f A B → Apply Val(λ env 1 => f ∘' g) x B
  | comp     : Apply g x A  → Apply f A B → Apply Val(λ env 1 => f ∘ g) x B
  | comp₂    : Apply g x A  → Apply f A B → Apply Val(λ env 1 => f ∘∘ g) x B
  | curr₂    : Apply x Val(neutral(⟦β⟧(y, z))) e' → Apply Val(λ y::env 1 => Λ(α, β, x)) z e'
  | curr'₂   : Apply x Val(neutral(&(neutral(⟦β⟧(y, z))))) e'
    → Apply Val(λ neutral(&(y))::env 1 => !Λ(α, β, x)) Val(neutral(&(z))) e'
  | pi       : Apply Val(Π (f_α) env 2, f_β) x Val(Π (f_α) x::env 1, f_β)
  -- TODO: This shouldn't be possible
  --| neut     : Apply Val(neutral(f)) x Val(neutral(f x))

mutual

inductive Eval : List Val → Expr → Val → Type
  | top    : Eval env (DCC ⊤) Val(neutral(⊤))
  | tintro : Eval env (DCC ∗) Val(neutral(∗))
  | bot    : Eval env (DCC ⊥) Val(neutral(⊥))
  | sort   : Eval env (DCC Sort m) Val(neutral(Sort m))
  | map    : Eval env f f'
    → Eval env (DCC !<f>) Val(λ env 1 => !<f'>)
  | fmap   : Eval env f f' → Eval env (DCC $<f>) Val(λ env 1 => $<f'>)
  | unbox  : Eval env x x' → Eval env (DCC *(x)) Val(λ env 1 => *(x'))
  | eval   : Eval env α α' → Eval env β β' → Eval env x x' → Eval env (DCC Eval(α, β, x)) Val(λ env 1 => Eval(α', β', x'))
  | quot   : Eval env β β' → Eval env x x' → Eval env (DCC `(β, x)) Val(λ env 1 => `(β', x'))
  | id     : Eval env α α' → Eval env (DCC Id(α)) Val(λ env 1 => Id(α'))
  | fstc   : Eval env β β' → Eval env (DCC Fstc(β)) Val(λ env 1 => Fstc(β'))
  | sndc   : Eval env β β' → Eval env (DCC Sndc(β)) Val(λ env 1 => Sndc(β'))
  | curr   : Eval env α α' → Eval env β β' → Eval env x x' → Eval env (DCC Λ(α, β, x)) Val(λ env 2 => Λ(α', β', x'))
  | curr'  : Eval env α α' → Eval env β β' → Eval env x x' → Eval env (DCC !Λ(α, β, x)) Val(λ env 2 => Λ(α', β', x'))
  | pi     : Eval env f_α f_α' → Eval env f_β f_β' → Eval env (DCC Π(f_α, f_β)) Val(Π (f_α') env 1, f_β')
  | pair   : Eval env β β' → Eval env M M' → Eval env N N' → Eval env (DCC ⟦β⟧⟨M, N⟩) Val(λ env 1 => ⟦β'⟧⟨M', N'⟩)
  | eql    : Eval env f_α f_α' → Eval env (DCC Eql(f_α)) Val(λ env 2 => Eql(f_α'))
  | refl   : Eval env f_α f_α' → Eval env (DCC refl(f_α)) Val(λ env 2 => refl(f_α'))
  | comp   : Eval env f f' → Eval env g g' → Eval env (DCC f ∘ g) Val(λ env 1 => f' ∘ g')
  | comp'  : Eval env f f' → Eval env g g' → Eval env (DCC f ∘' g) Val(λ env 1 => f' ∘' g')
  | comp₂  : Eval env f f' → Eval env g g' → Eval env (DCC f ∘∘ g) Val(λ env 1 => f' ∘∘ g')
  | sigma  : Eval env α α' → Eval env β β' → Eval env (DCC Σ(α, β)) Val(λ env 1 => Σ(α', β'))
  | boxed  : Eval env x x' → Eval env (DCC &(x)) Val(neutral(&(x')))
  | bang   : Eval env x x' → Eval env (DCC !(x)) Val(neutral(!(x')))
  | coup   : Eval env β β' → Eval env a a'
    → Eval env b b' → Eval env (DCC ⟦β⟧(a, b)) Val(neutral(⟦β'⟧(a', b')))
  | t_coup : Eval env β β' → Eval env (DCC Coup(β)) Val(neutral(Coup(β')))
  | eq     : Eval env x x' → Eval env y y' → Eval env (DCC (x = y)) Val(neutral(x' = y'))
  | app    : Eval env f f' → Eval env x x' → Apply f' x' e' → Eval env (DCC (f x)) e'

end

end Semantic
