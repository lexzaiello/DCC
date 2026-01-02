/-
  An approach to dependently-typed combinators that models contexts as combinatory objects in and of themselves.
-/

import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Monad

namespace Idea

inductive Expr where
  | data      : Expr
  | tup       : Expr
  | cons      : Expr
  | nil       : Expr
  | seq       : Expr
  | k         : Expr
  | k'        : Expr
  | s         : Expr
  | i         : Expr
  | fst       : Expr
  | snd       : Expr
  | map_fst   : Expr
  | map_snd   : Expr
  | read      : Expr
  | read_y    : Expr
  | read_data : Expr
  | read_γ_s  : Expr
  | read_x_s  : Expr
  | read_y_s  : Expr
  | read_βx   : Expr
  | next      : Expr
  | app       : Expr
    → Expr
    → Expr
deriving BEq

declare_syntax_cat atom
declare_syntax_cat app
declare_syntax_cat expr

syntax "Data"                : atom
syntax ">>"                  : atom
syntax "(" app ")"           : atom
syntax "#" term              : atom
syntax ":" ident             : atom
syntax "::"                  : atom
syntax "K"                   : atom
syntax "K'"                  : atom
syntax "I"                   : atom
syntax "S"                   : atom
syntax "read"                : atom
syntax "fst"                 : atom
syntax "snd"                 : atom
syntax "nil"                 : atom
syntax "::"                  : atom
syntax "next"                : atom
syntax "map_fst"             : atom
syntax "map_snd"             : atom
syntax "read_data"           : atom
syntax "read_y"              : atom
syntax "read_γ_s"            : atom
syntax "read_x_s"            : atom
syntax "read_y_s"            : atom
syntax "read_βx"             : atom
syntax ","                   : atom

syntax atom     : app
syntax app atom : app

syntax "⟪" expr "⟫"      : term
syntax "⟪₁" atom "⟫"     : term
syntax "⟪₂" app "⟫"      : term

macro_rules
  | `(⟪₁ Data ⟫) => `(Expr.data)
  | `(⟪₁ #$e:term ⟫) => `($e)
  | `(⟪₁ :$id:ident ⟫) => `($id)
  | `(⟪₁ K ⟫) => `(Expr.k)
  | `(⟪₁ K' ⟫) => `(Expr.k')
  | `(⟪₁ I ⟫) => `(Expr.i)
  | `(⟪₁ S ⟫) => `(Expr.s)
  | `(⟪₁ map_fst ⟫) => `(Expr.map_fst)
  | `(⟪₁ map_snd ⟫) => `(Expr.map_snd)
  | `(⟪₁ fst ⟫) => `(Expr.fst)
  | `(⟪₁ snd ⟫) => `(Expr.snd)
  | `(⟪₁ read ⟫) => `(Expr.read)
  | `(⟪₁ read_γ_s ⟫) => `(Expr.read_γ_s)
  | `(⟪₁ read_x_s ⟫) => `(Expr.read_x_s)
  | `(⟪₁ read_y_s ⟫) => `(Expr.read_y_s)
  | `(⟪₁ read_βx ⟫) => `(Expr.read_βx)
  | `(⟪₁ read_data ⟫) => `(Expr.read_data)
  | `(⟪₁ read_y ⟫) => `(Expr.read_y)
  | `(⟪₁ :: ⟫) => `(Expr.cons)
  | `(⟪₁ next ⟫) => `(Expr.next)
  | `(⟪₁ >> ⟫) => `(Expr.seq)
  | `(⟪₁ nil ⟫) => `(Expr.nil)
  | `(⟪₁ , ⟫) => `(Expr.tup)
  | `(⟪₂ ($e:app) ⟫) => `(⟪₂ $e ⟫)
  | `(⟪₂ $e:atom ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₁ ($e:atom) ⟫) => `(⟪₁ $e ⟫)
  | `(⟪₁ ($e:app) ⟫) => `(⟪₂ $e ⟫)
  | `(⟪₂ ($e₁:app) $e₂:atom ⟫) => `(⟪₂ $e₁ $e₂ ⟫)
  | `(⟪₂ $e₁:app $e₂:atom ⟫) => `(Expr.app ⟪₂ $e₁ ⟫ ⟪₁ $e₂ ⟫)

def Expr.toString : Expr → String
  | ⟪₂ Data ⟫ => "Data"
  | ⟪₂ fst ⟫ => "fst"
  | ⟪₂ snd ⟫ => "snd"
  | ⟪₂ >> ⟫ => ">>"
  | ⟪₂ map_fst ⟫ => "map_fst"
  | ⟪₂ map_snd ⟫ => "map_snd"
  | ⟪₂ read_data ⟫ => "read_data"
  | ⟪₂ read_y ⟫ => "read_y"
  | ⟪₂ read_γ_s ⟫ => "read_γ_s"
  | ⟪₂ read_x_s ⟫ => "read_x_s"
  | ⟪₂ read_y_s ⟫ => "read_y_s"
  | ⟪₂ read_βx ⟫ => "read_βx"
  | ⟪₂ :: ⟫ => "::"
  | ⟪₂ nil ⟫ => "nil"
  | ⟪₂ read ⟫ => "read"
  | ⟪₂ , ⟫ => ","
  | ⟪₂ :f :x ⟫ => s!"({f.toString} {x.toString})"
  | ⟪₂ next ⟫ => "next"
  | ⟪₂ I ⟫ => "I"
  | ⟪₂ K ⟫ => "K"
  | ⟪₂ K' ⟫ => "K"
  | ⟪₂ S ⟫ => "S"

instance Expr.instToString : ToString Expr where
  toString := Expr.toString

def Expr.push_in (with_e : Expr) : Expr → Expr
  | ⟪₂ :: :x nil ⟫ => ⟪₂ :: :x (:: :with_e nil) ⟫
  | ⟪₂ nil ⟫ => ⟪₂ :: :with_e nil ⟫
  | ⟪₂ :: :x (:: :y :xs) ⟫ => ⟪₂ :: :x (:: :y (#Expr.push_in with_e xs)) ⟫
  | ⟪₂ :: :x :xs ⟫ => ⟪₂ :: :x (:: :xs :with_e) ⟫
  | e => e

def Expr.as_asserts : Expr → Option Expr
  | ⟪₂ , :Γ (, :_Δ :_Ξ) ⟫ => Γ
  | _ => .none

def Expr.as_singleton : Expr → Option Expr
  | ⟪₂ :: :x nil ⟫ => x
  | _ => .none

def Expr.list_pop : Expr → Option Expr
  | ⟪₂ :: :_x :xs ⟫ => xs
  | _ => .none

def Expr.list_head : Expr → Option Expr
  | ⟪₂ :: :x :_xs ⟫ => x
  | _ => .none

def Expr.as_list : Expr → Option (List Expr)
  | ⟪₂ :: :x :xs ⟫ => do return x :: (← xs.as_list)
  | ⟪₂ nil ⟫ => pure []
  | x => pure [x]

def Expr.as_tup_list : Expr → Option (List Expr)
  | ⟪₂ , :x :xs ⟫ => do return x :: (← xs.as_tup_list)
  | ⟪₂ nil ⟫ => pure []
  | x => pure [x]

def Expr.from_list : List Expr → Expr
  | [] => ⟪₂ nil ⟫
  | x::xs => ⟪₂ :: :x (#Expr.from_list xs) ⟫

def Expr.mk_tup : List Expr → Expr
  | [] => ⟪₂ nil ⟫
  | [x] => x
  | [x, xs] => ⟪₂ , :x :xs ⟫
  | x :: xs => ⟪₂ , :x (#Expr.mk_tup xs) ⟫

example : Expr.mk_tup [⟪₂ Data ⟫, ⟪₂ S ⟫, ⟪₂ K ⟫] = ⟪₂ ((, Data) (, S K)) ⟫ := rfl

def Expr.display_infer : Expr → Expr
  | ⟪₂ , (:: :t nil) (, nil :_Ξ) ⟫ => t
  | e => e

example : Expr.as_list ⟪₂ :: Data (:: K Data) ⟫ = [⟪₁ Data ⟫, ⟪₁ K ⟫, ⟪₁ Data ⟫] := rfl

example : Expr.push_in ⟪₂ Data ⟫ ⟪₂ :: Data K ⟫ = ⟪₂ :: Data (:: K Data) ⟫ := rfl

def step : Expr → Option Expr
  | ⟪₂ >> :f :g :Γ ⟫ => step ⟪₂ :g (:f :Γ) ⟫
  | ⟪₂ I :_α :x ⟫ => x
  | ⟪₂ K :_α :_β :x :_y ⟫ => x
  | e@⟪₂ next (:: :_x nil) ⟫ => e
  | ⟪₂ read nil ⟫ => .none
  | ⟪₂ next (:: :_x :xs) ⟫ => xs
  | ⟪₂ read (:: :x :_xs) ⟫ => x
  | ⟪₂ fst (, :a :_b) ⟫ => a
  | ⟪₂ snd (, :_a :b) ⟫ => b
  | ⟪₂ map_fst :f (, :a :b) ⟫ => do
    ⟪₂ (, (#← step ⟪₂ :f :a ⟫) :b) ⟫
  | ⟪₂ map_snd :f (, :a :b) ⟫ => do
    ⟪₂ (, :a (#← step ⟪₂ :f :b ⟫)) ⟫
  | ⟪₂ read_data (, :Γ :_Ξ) ⟫ => do
    ⟪₂ ,
      (:: (K Data (I Data) Data) (:: (K Data (I Data) Data) nil))
      (,
        (:: (read :Γ) nil)
        (:: Data nil)) ⟫
  | ⟪₂ , :a :b ⟫ => do ⟪₂ , (#(step a).getD a) (#(step b).getD b) ⟫
  | ⟪₂ read_y (, :Γ :_Ξ) ⟫ =>
    ⟪₂ (read (next :Γ)) (read (next (next :Γ))) ⟫
  | ⟪₂ read_βx :β (, :Γ :_Ξ) ⟫ =>
    let term_x := ⟪₂ >> read :Γ ⟫

    ⟪₂ :β :term_x ⟫
  | ⟪₂ :f :x ⟫ =>
    (do ⟪₂ (# ← step f) (#← step x) ⟫) <|>
    (do
    ⟪₂ (# ← (step f)) (#(step x).getD x) ⟫)
    <|> (do ⟪₂ (# (step f).getD f) (#← step x) ⟫)
  | _ => .none

def try_step_n (n : ℕ) (e : Expr) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e
    pure <| (try_step_n (n - 1) e').getD e'

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).getD e

-- Applies the Δ claims context to all handlers in the app context
-- returns all of the applied assertions, in order
def sub_context : Expr → Expr
  | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
    Expr.mk_tup <| (do (← Γ.as_list).mapM (fun f => (step ⟪₂ :f (, :Δ :Ξ) ⟫).getD f)).getD []
  | e => e

def norm_context : Expr → Expr := (try_step_n! 10 ∘ sub_context)

/-
An optimization for UX:

It can be quite annoying to create binders on the fly.
Sometimes you even need to make meta-combinators.

These are two separate issues in one package:

Issue 1:
rearranging the types in meta combinators often requires something like S,
but that's overkill.

Even if we wanted to use S, we have to manually type it, which isn't necessary,
since our Data are opaque.

Issue 2:
It can be confusing to create simple binders, especially when already underneath another binder.

For example, in K, we have β : α → Type

For this we need a meta combinator, read_α
It would be ideal if we could remove this entirely. Small goal.

read_α copies term_α and rearranges. this is issue 1, which is mechanical
read_α creates a binder by:

receiving the old context, and returning a new context tuple, where the Δ and Ξ are the terms used
in the meta combinator

This is a frequent operation.

This seems to be somewhat of a common pattern - mapping on the context.
Some kind of traversal would be interesting, although we want to be selective.

We want term_α, but we only want to insert it in the first position.
So we are "mapping" the context in the sense that we retain the Δ and Ξ,
but the Γ assertions are completely different.

This is a tuple combinator we might want to support.

map_fst
map_snd

Now, we don't need to replicate the Δ and Ξ.

Still the question of inserting term_α surgically.
-/

/-
S type:

S : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α), β x → Type)
  (x : ∀ (z : α), (y : β z), γ z y)
  (y : ∀ (z : α), β z)
  (z : α), γ z (y z)

α is also easy.
β is slightly harder, but not too hard.
γ is also slightly harder, but easy with a helper meta combinator, which are legal now
- Note that γ has a binder within, as well. this is why we need a meta combinator

- every ∀ parameter needs a meta combinator, most likely, though we can get around this later somehow

TODO HIGHEST PRIORITY: sometimes contexts have extra arguments that aren't needed
- intuition is that this is because Ξ can append types sometimes but not at other times
- I think this is because we don't append the known type for the expected

TODO: we're treating apps like list cons, but they're not the same - how will our mapping methods actually work?

TODO: Meta combinators
- γ
- x
- y

TODO: confusing how we can mismatch binders and other elements in the list

TODO: confusing how we can model an arrow without mentioning the specific argument term, extra context entry?

Another TODO later:
- remove pattern matching inside step for contexts. should use tuple accessors instead

Another potential TODO later:
- Since our contexts are just data, we can probably rearrange them however we want somehow
  with kinda "stringly" typing

BIG TODO:
- further assertions don't acutally depend on previous assertions,
- just arguments?
- when we apply something, we should be poping, somewhere.

Instead of locating assertions,
we just pop them?
we know we've got the output type once we've reached nil

x also with a meta combinator
y also with a meta combinator
z argument is very simple. easy assertion.
-/

/-
map_fst is not what we want.
types don't have access to the assertions in the context anyway.
we just want to push something to the tuple in a nice way.

pushM (f : Data → Data)

I don't think we even need this whack pushing shit.
The left elem doesn't depend on the context at all.
-/

def read_α : Expr :=
  ⟪₂ , (:: (>> fst read) (:: (K Data (I Data) Data) nil)) ⟫

def infer : Expr → Option Expr
  | ⟪₂ I ⟫ => ⟪₂ , (:: (K Data (I Data) Data) (:: (>> fst read) (:: (>> fst read) nil))) (, nil nil) ⟫
  | ⟪₂ K ⟫ =>
    let t_α := ⟪₂ K Data (I Data) Data ⟫
    let t_β := read_α
    let t_x := ⟪₂ (>> fst read) ⟫
    let t_y := ⟪₂ read_y ⟫

    ⟪₂ , (:: :t_α (:: :t_β (:: :t_x (:: :t_y (:: :t_x nil))))) (, nil nil) ⟫
  | ⟪₂ K' ⟫ =>
    ⟪₂ , (::
      (K Data (I Data) Data)
      (::
        (K Data (I Data) Data)
        (::
          (>> fst read)
          (::
            (>> fst (>> next read))
            (::
              (>> fst read)
              nil)))))
      (, nil nil) ⟫
  | ⟪₂ :: ⟫
  | ⟪₂ , ⟫ => ⟪₂ ,
    (::
      (>> snd read)
      (::
        (>> snd (>> next read))
        (::
          (K Data (I Data) Data)
          nil)))
      (, nil nil) ⟫
  | ⟪₂ map_fst ⟫
  | ⟪₂ map_snd ⟫ =>
    let assert_data_map := ⟪₂ read_data ⟫
    let assert_data_term := ⟪₂ K Data (I Data) Data ⟫
    ⟪₂ ,
      (:: :assert_data_map (:: :assert_data_term (:: :assert_data_term nil)))
      (,
        nil
        nil) ⟫
  | ⟪₂ >> ⟫ =>
    let assert_data_map := ⟪₂ read_data ⟫
    let assert_data_term := ⟪₂ K Data (I Data) Data ⟫
    ⟪₂ ,
      (:: :assert_data_map (:: :assert_data_map (:: :assert_data_term (:: :assert_data_term nil))))
      (,
        nil
        nil) ⟫
  | ⟪₂ nil ⟫ => ⟪₂ , (:: (K Data Data Data) nil) (, nil nil) ⟫
  | ⟪₂ Data ⟫ => ⟪₂ , (:: (K Data Data Data) nil) (, nil nil) ⟫
  | ⟪₂ read ⟫
  | ⟪₂ next ⟫
  | ⟪₂ read_y ⟫
  | ⟪₂ fst ⟫
  | ⟪₂ snd ⟫ => ⟪₂ , (:: (K Data (I Data) Data) (:: (K Data (I Data) Data) nil)) (, nil nil) ⟫
  | ⟪₂ :f :arg ⟫ => do
    let t_f ← infer f
    let t_arg := norm_context (← infer arg)

    match t_f with
    | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
      let Δ' := Expr.push_in arg Δ
      let Ξ' := Expr.push_in (← infer arg) Ξ

      let check_with ← Γ.list_head

      let norm_expected := norm_context (← try_step_n 10 ⟪₂ :check_with (, :Δ' :Ξ') ⟫)

      --dbg_trace s!"arg: {arg}"

      --dbg_trace s!"check: {check_with}"
      --dbg_trace s!"red: {⟪₂ :check_with (, :Δ' :Ξ') ⟫}"
      --dbg_trace try_step_n 10 ⟪₂ :check_with (, :Δ' :Ξ') ⟫
      --dbg_trace ⟪₂ (, :Δ' :Ξ') ⟫
      --dbg_trace norm_expected
      --dbg_trace t_arg

      if norm_expected == t_arg then
        let Γ' ← Γ.list_pop

        match Γ'.as_singleton with
        | .some t_out =>
          try_step_n 10 ⟪₂ :t_out (, :Δ' :Ξ') ⟫
        | _ =>
          pure ⟪₂ , :Γ' (, :Δ' :Ξ') ⟫
      else
        .none
    | _ => .none
  | _ => .none

/-
Potential tasks for today:

- Dependent S type (mildly boring, but a fun puzzle)
  - This unlocks a TON, would be epic
- Ironing out more bugs (very boring)
-/

/-
Note on map_fst for meta-combinators:
- need to truncate context for some reason?
-/

#eval Expr.display_infer <$> infer ⟪₂ Data ⟫

def t_k : Expr := ⟪₂ ((, ((:: (((K Data) (I Data)) Data)) ((:: (, ((:: ((>> fst) read)) ((:: (((K Data) (I Data)) Data)) nil)))) ((:: ((>> fst) read)) ((:: read_y) ((:: ((>> fst) read)) nil)))))) ((, nil) nil)) ⟫

#eval Expr.display_infer <$> infer ⟪₂ K ⟫

#eval Expr.display_infer <$> infer ⟪₂ (I :t_k K) Data (I Data) Data Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data ((I :t_k K) Data (I Data) Data Data) ⟫
#eval infer ⟪₂ (I :t_k K) ⟫

#eval norm_context <$> infer ⟪₂ K ⟫

#eval Expr.display_infer <$> infer ⟪₂ K' Data Data Data Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ >> read read (, I I) ⟫

#eval Expr.display_infer <$> (infer <=< infer) ⟪₂ K ⟫
#eval Expr.display_infer <$> (infer <=< infer) ⟪₂ I ⟫

#eval Expr.display_infer <$> infer ⟪₂ map_fst (I Data) (, I I) ⟫
#eval Expr.display_infer <$> infer ⟪₂ read (, K I) ⟫
#eval Expr.display_infer <$> infer ⟪₂ , K I ⟫

/-
Context truncation for tup_map meta comb.:
- not the Δ, it's the Ξ register
-/

#eval Expr.display_infer <$> infer ⟪₂ :: K I ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ K Data (I Data) Data Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data ⟫

end Idea
