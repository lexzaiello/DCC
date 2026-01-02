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
  | seq_smart : Expr
  | k         : Expr
  | k'        : Expr
  | s         : Expr
  | i         : Expr
  | fst       : Expr
  | snd       : Expr
  | both      : Expr
  | bothM     : Expr
  | push_on   : Expr
  | map_fst   : Expr
  | map_snd   : Expr
  | read      : Expr
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
syntax ">>*"                 : atom
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
syntax "push_on"             : atom
syntax "both"                : atom
syntax "bothM"               : atom
syntax "next"                : atom
syntax "map_fst"             : atom
syntax "map_snd"             : atom
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
  | `(⟪₁ both ⟫) => `(Expr.both)
  | `(⟪₁ bothM ⟫) => `(Expr.bothM)
  | `(⟪₁ :: ⟫) => `(Expr.cons)
  | `(⟪₁ push_on ⟫) => `(Expr.push_on)
  | `(⟪₁ next ⟫) => `(Expr.next)
  | `(⟪₁ >> ⟫) => `(Expr.seq)
  | `(⟪₁ >>* ⟫) => `(Expr.seq_smart)
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
  | ⟪₂ push_on ⟫ => "push_on"
  | ⟪₂ bothM ⟫ => "bothM"
  | ⟪₂ fst ⟫ => "fst"
  | ⟪₂ snd ⟫ => "snd"
  | ⟪₂ both ⟫ => "both"
  | ⟪₂ >> ⟫ => ">>"
  | ⟪₂ >>* ⟫ => ">>*"
  | ⟪₂ map_fst ⟫ => "map_fst"
  | ⟪₂ map_snd ⟫ => "map_snd"
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

def Expr.list_pretty (e : Expr) : String :=
  (e.as_list.map (·.toString)).getD e.toString

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

/-
  For rejecting a context and emitting a value.
-/
syntax "quot" : atom
macro_rules
  | `(⟪₁ quot ⟫) => `(⟪₂ K Data (I Data) ⟫)


example : Expr.as_list ⟪₂ :: Data (:: K Data) ⟫ = [⟪₁ Data ⟫, ⟪₁ K ⟫, ⟪₁ Data ⟫] := rfl

example : Expr.push_in ⟪₂ Data ⟫ ⟪₂ :: Data K ⟫ = ⟪₂ :: Data (:: K Data) ⟫ := rfl

def read_y : Expr := ⟪₂ both (>> fst (>> next read)) (>> fst (>> next (>> next read))) ⟫

def step : Expr → Option Expr
  | ⟪₂ push_on nil :a ⟫ => ⟪₂ :: :a nil ⟫
  | ⟪₂ push_on (:: :x :xs) :a ⟫ => ⟪₂ :: :a (:: :x :xs) ⟫
  | ⟪₂ push_on (, :a :b) :c ⟫ => ⟪₂ (, :c (, :a :b)) ⟫
  | ⟪₂ push_on :l :a ⟫ => ⟪₂ :: :a :l ⟫
  | ⟪₂ >> :f :g :Γ ⟫
  | ⟪₂ >>* :f :g :Γ ⟫ => step ⟪₂ :g (:f :Γ) ⟫
  | ⟪₂ I :_α :x ⟫ => x
  | ⟪₂ K :_α :_β :x :_y ⟫ => x
  | ⟪₂ both :f :g :Γ ⟫ =>
    let left := ⟪₂ :f :Γ ⟫
    let right := ⟪₂ :g :Γ ⟫

    ⟪₂ (# (step left).getD left) (# (step right).getD right) ⟫
  | ⟪₂ bothM :f :g :Γ ⟫ =>
    let left := ⟪₂ :f :Γ ⟫
    let right := ⟪₂ :g :Γ ⟫

    ⟪₂ :: (# (step left).getD left) (# (step right).getD right) ⟫
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
  | ⟪₂ , :a :b ⟫ => do ⟪₂ , (#(step a).getD a) (#(step b).getD b) ⟫
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

def read_data : Expr :=
  ⟪₂ , (:: (quot Data) (:: (quot Data) nil)) ⟫

def read_α : Expr :=
  ⟪₂ , (:: (>> fst read) (:: (quot Data) nil)) ⟫

/-
S type:

S : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α), β x → Type)
  (x : ∀ (z : α) (y : β z), γ z y)
  (y : ∀ (z : α), β z)
  (z : α), γ z (y z)
-/

namespace s

def then_quote : Expr := ⟪₂ both (quot quot) ⟫

def α : Expr := ⟪₂ quot Data ⟫

-- β : α → Type
def β : Expr := ⟪₂ >> fst (>> (:then_quote read) (>> (push_on (:: (quot Data) nil)) (push_on (, nil nil)))) ⟫

/- γ : ∀ (x : α), β x → Type
Our types are already in order
S α β x

in that order

So, we just map over them, and concatenate them cleverly,
then use push_on (:: (K Data (I Data) Data) nil) to put a Type as the final output type

if we just left α β x intact in the list, that would be close,
but we can just merge the β and x elements to form an application
read gets us the head, α,
and next gets us β, x
then, we drop everything afterwards...

>> (both read (>> next >> (both read (>> next read)))) (push_on (:: (K Data (I Data) Data) nil))

this is the general order we want,
but we need to be careful about concatenation

for α, we want to cons
we could do this in some other way outside both though.

both does an app though, so we're set.
-/

/-
Nicer quotation.
Our contexts are lists of Data → Data
sometimes we want to quote something inside a Data → Data
We can introduce notation for quotation, since it happens a lot.
Quotation is always

K Data (I Data) :x

We need to capture α and β, but quote "read" for x.
α is just normal read, and β is >> next read
x is just quot read

∀ (x : α), β x → Type

we need to read and then quote, which is really nasty.
α gets read from the current context, then quoted.

just ugly.

Δ doesn't have K's.
we could probably solve this with a map function for data,
then quote each of them respectively.

we already have mapping. is she stupid?
we can do mapping with both I think?

read is not the same as map.
we already have read and next.

I want >> to be more powerful.

-/
def γ : Expr :=
  -- reads from the context and returns the quoted value
  --let read_quot := ⟪₂ 
  let ty_end := ⟪₂ (push_on (:: (quot Data) nil)) ⟫

  let read_quote_discard_ctx := ⟪₂ quot read ⟫
  let do_on_βx := ⟪₂ >> next (>> (both ) :ty_end) ⟫
  let do_on_α := ⟪₂ :then_quote read ⟫

  -- TOOD: x is captured, instead of referring to our own context with dynamic read

  -- Create a new empty context here with push_on
  let asserts := ⟪₂ >> fst (>> (bothM :do_on_α :do_on_βx) (push_on (, nil nil))) ⟫

  asserts

#eval try_step_n 10 ⟪₂ :β (, (:: Data nil) nil) ⟫  -- this one is right. we bind a new context, just as we should for arrows

#eval try_step_n 10 ⟪₂ :γ (, (:: Data (:: (I Data) (:: Data nil))) nil) ⟫

end s

def infer : Expr → Option Expr
  | ⟪₂ I ⟫ => ⟪₂ , (:: (quot Data) (:: (>> fst read) (:: (>> fst read) nil))) (, nil nil) ⟫
  | ⟪₂ K ⟫ =>
    let t_α := ⟪₂ quot Data ⟫
    let t_β := read_α
    let t_x := ⟪₂ (>> fst read) ⟫
    let t_y := read_y

    ⟪₂ , (:: :t_α (:: :t_β (:: :t_x (:: :t_y (:: :t_x nil))))) (, nil nil) ⟫
  | ⟪₂ K' ⟫ =>
    ⟪₂ , (::
      (quot Data)
      (::
        (quot Data)
        (::
          (>> fst read)
          (::
            (>> fst (>> next read))
            (::
              (>> fst read)
              nil)))))
      (, nil nil) ⟫
  | ⟪₂ :: ⟫
  | ⟪₂ push_on ⟫
  | ⟪₂ , ⟫ => ⟪₂ ,
    (::
      (>> snd read)
      (::
        (>> snd (>> next read))
        (::
          (quot Data)
          nil)))
      (, nil nil) ⟫
  | ⟪₂ map_fst ⟫
  | ⟪₂ map_snd ⟫ =>
    let assert_data_map := read_data
    let assert_data_term := ⟪₂ quot Data ⟫
    ⟪₂ ,
      (:: :assert_data_map (:: :assert_data_term (:: :assert_data_term nil)))
      (,
        nil
        nil) ⟫
  | ⟪₂ >>* ⟫ =>
    /-
      >>* : ∀ (α : Type), (Data -> Data) -> (Data -> α) -> Data -> α,
      except α is inferred through Ξ and manipulating the type of the second argument to fetch
      α via patern matching

      Ξ is the second register we have access to. it is a list of the known types of our arguments,
      and we should have access to the Data -> α as the second argument in it. its value should look like this:

      ((, ((:: ((>> fst) read)) ((:: ((>> fst) read)) nil))) ((, ((:: Data) nil)) ((:: ((, ((:: (((K Data) (I Data)) Data)) nil)) ((, nil) nil))) nil)))
      its output type is the second element in its assertions
    -/
    let Ξ := ⟪₂ snd ⟫

    let t_arg_map_2 := ⟪₂ >> :Ξ (>> next read) ⟫

    -- this is the α, the output type of the second map
    let t_out := ⟪₂ >> fst (>> next read) ⟫

    let get_t_out := ⟪₂ >> :t_arg_map_2 :t_out ⟫

    let assert_data_map := read_data

    -- fetch the α, then push it as the output type
    let in_data := ⟪₂ quot Data ⟫
    let assert_some_data_map := ⟪₂ >> :get_t_out (>> (push_on nil) (:: :in_data)) ⟫

    -- first argument is just Data -> Data
    -- second argument is polymoprhic
    -- third argument is the datum
    -- output is the α
    ⟪₂ ,
      (:: :assert_data_map (:: :assert_some_data_map (:: (quot Data) (:: :get_t_out nil))))
      (, nil nil) ⟫
  | ⟪₂ >> ⟫
  | ⟪₂ both ⟫
  | ⟪₂ bothM ⟫ =>
    let assert_data_map := read_data
    let assert_data_term := ⟪₂ quot Data ⟫
    ⟪₂ ,
      (:: :assert_data_map (:: :assert_data_map (:: :assert_data_term (:: :assert_data_term nil))))
      (,
        nil
        nil) ⟫
  | ⟪₂ nil ⟫ => ⟪₂ , (:: (quot Data) nil) (, nil nil) ⟫
  | ⟪₂ Data ⟫ => ⟪₂ , (:: (quot Data) nil) (, nil nil) ⟫
  | ⟪₂ read ⟫
  | ⟪₂ next ⟫
  | ⟪₂ fst ⟫
  | ⟪₂ snd ⟫ => ⟪₂ , (:: (quot Data) (:: (quot Data) nil)) (, nil nil) ⟫
  | ⟪₂ :f :arg ⟫ => do
    let t_f ← infer f
    let t_arg := norm_context (← infer arg)

    match t_f with
    | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
      let Δ' := Expr.push_in arg Δ
      let Ξ' := Expr.push_in (← infer arg) Ξ

      let check_with ← Γ.list_head

      let norm_expected := norm_context (← try_step_n 10 ⟪₂ :check_with (, :Δ' :Ξ') ⟫)

      dbg_trace norm_expected
      dbg_trace t_arg

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

#eval Expr.display_infer <$> infer ⟪₂ read ⟫

#eval Expr.display_infer <$> infer ⟪₂ push_on (:: Data nil) nil ⟫
#eval Expr.display_infer <$> infer ⟪₂ Data ⟫

def t_k : Expr := ⟪₂ ((, ((:: (quot Data)) ((:: (, ((:: ((>> fst) read)) ((:: ((quot) Data)) nil)))) ((:: ((>> fst) read)) ((:: (#read_y)) ((:: ((>> fst) read)) nil)))))) ((, nil) nil)) ⟫

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

-- Context here looks like
#eval Expr.display_infer <$> infer ⟪₂ both (>> fst (>> next read)) (>> fst (>> next (>> next read))) (, (:: Data (:: (I Data) (:: Data nil))) (:: Data (:: Data (:: Data nil)))) ⟫
#eval Expr.display_infer <$> infer ⟪₂ bothM (>> fst (>> next read)) (>> fst (>> next (>> next read))) (, (:: Data (:: (I Data) (:: Data nil))) (:: Data (:: Data (:: Data nil)))) ⟫

#eval Expr.display_infer <$> infer ⟪₂ :: K I ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ quot Data Data ⟫
#eval infer ⟪₂ I Data ⟫

#eval Expr.display_infer <$> infer ⟪₂ >>* read read ⟫

end Idea
