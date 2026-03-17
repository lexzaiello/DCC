import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation

/-
algorithmic approach is best. how to do it though?

aligns with how CoC does it.
substitute placeholder in, use decreasing measure to judge again.

potential issues though:
- reflexivity in RunPi. this is annoying as shit.
- we will need a function to actually STEP pi.
the size probably increases, but it's not immediately obvious.

we can just define sizeOf to only include our "root" combinators.
keep in mind, every arg call will result in a bunch of I combinators being dropped.
however, we would need to define well-typedness, maybe, to do this.

we can't run run_pi first.
for "stepping" pi, we don't really care about the intermediate values for type-checking.
we mainly care about the final codomain.

one idea:
- size = number of arguments to each Π argument
- this will decrease, since the number of arguments we're expecting goes down.
- need to make sure size only include α and β, not the pi itself (+ 1)

what we're trying to prove:
- decreasing measure for Π substitution. will probably piggy-back off existing proof, but:
  - need intermediate lemma about ReflTrans
  - switch to use TransGen
  - prove lemma, possibly, but this will be hard with reflexivity
  - we could also modify red_ty_comb? to return a proof that size is decreasing. might be nice.
  - sizeof function is super annoying. should be able to model as an inductive.
  - should probably future-proof Π
  - we could also bake Π reduction into RedTyComb, since we'll need to use it elsewhere

TODO:
- Expr.arity would be super useful for TySize
- Redefine RedTy without ¬ e.Redex
  - No longer have determinism, but we can probably prove diamond.
  - we should probably have refl cases, but then size doesn't decrease. can use arity, maybe?
  - new Π rule suggests we will need asserts for Sort m argument asserts
- Expr.TySize with Π and all Expr's defined
- Expr.RedTyComb should account for ParApps of the core combinators - not necessarily true. actually, this is
  probably necessary. how would Π handle multiple arguments then?
  think this was handled in the past by Π rebind.
  - If Expr.TySize n.succ, then it should decrease to exactly n.
- ¬ RedexTy is really annoying to work with
- Π reduction:
  RedCombTy (α x) α'
  → RedCombTy ((Π α, β) x) (Π α', (β x))
  size should decrease, but we can't easily check arity.
  we could do literally just β x. have some other step to recurse.
- test RedTy with eval function

Questions:
- why can't we have reflexivity? - decreasing measure

Π arity is kind of confusing because it will stay constant.
Note that Π only steps if we can step α. So it is α arity.

reduction should reduce arity by exactly one.
so app is more like adding arities together, or just adding one for the argument.
one combinator is always getting deleted.

TySize for base combinators = 1.
add one for each argument. combinator gets deleted eventually. reduced.
-/

def K.type (m n : Level) : Expr := (SK
  Π Sort m, Π (Π #(arg 0), Sort n), Π #((arg 0).ret 1), Π #(arg 1), #((arg 0).ret 3))

--#eval Std.format <| ((K.type 1 1).reduce_pi (SK Sort 0)).fst

def K'.type (m n : Level) : Expr :=
  (SK Π Sort m, Π Sort n, Π #((arg 0).ret 1), Π #((arg 1).ret 1), #((arg 0).ret 3))

def S.type (m n o : Level) : Expr := (SK
    Π Sort m, -- α
    Π (Π #(arg 0), Sort n), -- β
    Π (Π #((arg 0).ret 1), Π #(arg 1), Sort o), -- γ
    Π (Π #((arg 0).ret 2), Π #((arg 1).ret 1), #(arg 2)), -- x
    Π (Π #((arg 0).ret 3), #((arg 1).ret 2)), -- y
    Π #((arg 0).ret 4), -- z
      (B (S.{[m, n, o.succ]}
        (__ ∶ Sort m)
        (__ ∶ Sort n)
        (__ ∶ Sort o)) #((arg 2).ret 1))) -- γ z (y z)
-- ^ note that this is safe, since prior apps were type-checked, and def-eq here is deferred to term-level

inductive Judge : Expr → Expr → Prop
  | app   : Judge (SK Π α, β) f
    → Judge α x
    → RedPiArg x β β'
    → Judge β' (SK (f x))
  | srt   : Judge    (SK Sort m.succ) (SK Sort m)
  | k     : Judge    (K.type m n) (SK K.{[m, n]})
  | k'    : Judge    (K'.type m n) (SK K'.{[m, n]})
  | s     : Judge    (S.type m n o) (SK S.{[m, n, o]})
  | conv  {α β : Expr} : Judge α x → Expr.TyRedReflTrans α β → Judge β x

def infer (e : Expr) : Option ((t : Expr) × PLift (Judge t e)) :=
  match h_eq : e with
  | SK Sort m => .some ⟨SK Sort m.succ, ⟨.srt⟩⟩
  | SK K.{[m, n]} => .some ⟨K.type m n, ⟨.k⟩⟩
  | SK K'.{[m, n]} => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | SK S.{[m, n, o]} => .some ⟨S.type m n o, ⟨.s⟩⟩
  | SK (f x) => do
    let ⟨t_f, ⟨h_t_f⟩⟩ ← infer f
    let ⟨t_x, ⟨h_t_x⟩⟩ ← infer x
    let ⟨t_f', h_r_f⟩ := t_f.reduce_ty

    match heqf : t_f' with
    | (SK Π α, β) =>
      let ⟨α₂, hrx⟩ := t_x.reduce_ty

      if heq : α = α₂ then
        let ⟨β', h⟩ := β.reduce_pi_arg x
        .some <| ⟨β', ⟨.app (.conv h_t_f h_r_f) (by rw [heq]; exact (.conv h_t_x hrx)) h.down⟩⟩
      else
        .none
    | _ => .none
  | _ => .none

/-
Challenge: inference for Π:

we can probably do this more reliably. we're not type-checking terms.

cases:
- atomic type (e.g., Srt) as codomain. we can infer that easily.

-/

#eval (infer (SK (K'.{[2, 2]} (Sort 1) (Sort 1) (Sort 0) (Sort 0)))).map (·.fst)
