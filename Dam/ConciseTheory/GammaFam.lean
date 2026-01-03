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
  | ⟪₂ K' ⟫ => "K'"
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
    let f' := (step f).getD f
    let x' := (step x).getD x
    ⟪₂ :f' :x' ⟫
  | _ => .none

def try_step_n (n : ℕ) (e : Expr) : Option Expr := do
  if n = 0 then
    pure e
  else
    let e' ← step e
    pure <| (try_step_n (n - 1) e').getD e'

def try_step_n! (n : ℕ) (e : Expr) : Expr := (try_step_n n e).getD e

def steal_context (from_e for_e : Expr) : Expr :=
  match from_e, for_e with
  | ⟪₂ :_Γ (, :Δ :Ξ) ⟫, ⟪₂ :Γ₂ (, nil nil) ⟫ => ⟪₂ :Γ₂ (, :Δ :Ξ) ⟫
  | _, _ => for_e

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
-/
def γ : Expr :=
  -- arguments in the first register
  let Δ := ⟪₂ fst ⟫

  -- α is the first argument in Δ. we don't do anything to it
  let α := ⟪₂ read ⟫
  let β := ⟪₂ >> next read ⟫

  -- x is a quoted operation that shouldn't run until the later context
  -- flow starts by getting our dependents, then building the new context via quotation
  -- x is the first argument in the later context
  -- it selects the Δ register, then reads
  let x := ⟪₂ >> fst read ⟫

  let mk_βx := ⟪₂ (both (both (quot both) quot) (quot :x)) ⟫

  let asserts := ⟪₂ >> :Δ (bothM (>>* :α quot) (>> (>> :β :mk_βx) (push_on (:: (quot Data) nil)))) ⟫

  ⟪₂ >> :asserts (push_on (, nil nil)) ⟫

#eval try_step_n 10 ⟪₂ :β (, (:: Data nil) nil) ⟫  -- this one is right. we bind a new context, just as we should for arrows

#eval try_step_n 10 ⟪₂ :γ (, (:: Data (:: (I Data) nil)) nil) ⟫
#eval try_step_n 10 ⟪₂ ((both (((K Data) (I Data)) (I Data))) ((>> fst) read)) (, (:: I nil) nil) ⟫

/-
x : ∀ (z : α) (y : β z), γ z y
-/
def arg_x : Expr :=
  -- arguments in the first register
  let Δ := ⟪₂ fst ⟫

  let α := ⟪₂ read ⟫
  let β := ⟪₂ >> next read ⟫
  let γ := ⟪₂ >> next (>> next read) ⟫

  -- sequence after β
  let x := ⟪₂ >> fst read ⟫
  let mk_βx := ⟪₂ (both (both (quot both) quot) (quot :x)) ⟫

  let y := ⟪₂ >> fst (>> next read) ⟫

  -- similar pattern for output, γ z y
  -- assume entire Δ in scope
  let mk_γz := ⟪₂ both (both (quot both) (>> :γ quot)) (quot :x) ⟫
  let mk_γzy := ⟪₂ both (both (quot both) :mk_γz) (quot :y) ⟫

  let asserts := ⟪₂ >> :Δ (bothM (>>* :α quot) (bothM (>> :β :mk_βx) (>> :mk_γzy (push_on nil)))) ⟫

  ⟪₂ >> :asserts (push_on (, nil nil)) ⟫

/-
For testing the x type, S's context:
- α = Data
- β = I Data
- γ = I
-/
def test_context_arg_x : Expr := ⟪₂ (, (:: Data (:: (I Data) (:: I nil))) nil) ⟫

/-
this should be:
γ = I
x : ∀ (z : Data) (y : I Data z), I z y

((:: (((K Data) (I Data)) Data)) ((:: ((both (((K Data) (I Data)) (I Data))) ((>> fst) read))) ((:: ((both ((both (((K Data) (I Data)) I)) ((>> fst) read))) ((>> fst) ((>> next) read)))) nil)))

See tests below
-/
#eval try_step_n 10 ⟪₂ ((both (((K Data) (I Data)) (I Data))) ((>> fst) read)) (, (:: I nil) nil) ⟫
#eval try_step_n 10 ⟪₂ :arg_x :test_context_arg_x ⟫
#eval try_step_n 10 ⟪₂ ((both ((both (((K Data) (I Data)) I)) ((>> fst) read))) ((>> fst) ((>> next) read))) (, (:: Data (:: Data nil)) nil) ⟫

/-
y : ∀ (z : α), β z


-/
def arg_y : Expr :=
  let Δ := ⟪₂ fst ⟫

  let α := ⟪₂ read ⟫
  let β := ⟪₂ >> next read ⟫

  let x := ⟪₂ >> fst read ⟫
  let mk_βx := ⟪₂ (both (both (quot both) quot) (quot :x)) ⟫

  let asserts := ⟪₂ >> :Δ (bothM (>>* :α quot) (>> (>> :β :mk_βx) (push_on nil))) ⟫

  ⟪₂ >> :asserts (push_on (, nil nil)) ⟫

/-
y test, pretty similar. use the same test context.
should be ∀ (x : α), β x
first arg in asserts is the data quoted, nice
second is the both thing. let's test
((, ((:: (((K Data) (I Data)) Data)) ((:: ((both (((K Data) (I Data)) (I Data))) ((>> fst) read))) nil))) ((, nil) nil))
-/
#eval try_step_n 10 ⟪₂ :arg_y :test_context_arg_x ⟫

-- Some I. epic
#eval try_step_n 10 ⟪₂ ((both (((K Data) (I Data)) (I Data))) ((>> fst) read)) (, (:: I nil) nil) ⟫

/-
z is pretty easy, since it's not even under a binder. Assume we're given (, Δ Ξ)
-/

def arg_z : Expr :=
  let Δ := ⟪₂ fst ⟫
  ⟪₂ >> :Δ read ⟫

/-
Final output:
γ z (y z)
-/
def t_out : Expr :=
  let Δ := ⟪₂ fst ⟫

  -- x is in register 4
  -- y is in register 5
  -- z is in register 6

  let start_val_args := ⟪₂ >> next (>> next next) ⟫
  let γ := ⟪₂ >> next (>> next read) ⟫
  let y := ⟪₂ >> :start_val_args (>> next read) ⟫
  let z := ⟪₂ >> :start_val_args (>> next (>> next read)) ⟫

  ⟪₂ >> :Δ (both (both :γ :z) (both :y :z)) ⟫

def full_test_context : Expr :=
  let α := ⟪₂ Data ⟫
  let β := ⟪₂ I Data ⟫
  let γ := ⟪₂ I ⟫

  let x := ⟪₂ I ⟫
  let y := ⟪₂ I Data ⟫
  let z := ⟪₂ Data ⟫

  ⟪₂ (, (:: :α (:: :β (:: :γ (:: :x (:: :y (:: :z nil)))))) nil) ⟫

#eval try_step_n 10 ⟪₂ :t_out :full_test_context ⟫

def s_rule : Expr :=
  ⟪₂ , (:: :α (:: :β (:: :γ (:: :arg_x (:: :arg_y (:: :arg_z nil)))))) (, nil nil) ⟫

end s

def infer : Expr → Option Expr
  | ⟪₂ S ⟫ => s.s_rule
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

    -- this if the type of g. it is this tuple (Γ, Δ, Ξ)
    -- we need Δ to compute values in Γ
    let t_arg_map_2 := ⟪₂ >> :Ξ (>> next read) ⟫

    -- takes ctx for g, gets its args / Δ register
    let ctx_map_2 := ⟪₂ snd ⟫

    -- this is the α, the output type of the second map
    let t_out := ⟪₂ >> fst (>> next read) ⟫

    -- we need to plug in the argument's Δ register to see its types
    -- we do this with both t_out Δ_map_2
    let get_t_out := ⟪₂ >> :t_arg_map_2 (both :t_out :ctx_map_2) ⟫

    let assert_data_map := read_data

    -- fetch the α, then push it as the output type
    let in_data := ⟪₂ Data ⟫

    -- We need to add a fake context for quotation
    let assert_some_data_map := ⟪₂ >>
      (>> :get_t_out (, :in_data))
      (>>
        quot
        (push_on (, nil nil))) ⟫

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
    let raw_t_arg ← infer arg
    let t_arg := norm_context raw_t_arg

    match t_f with
    | ⟪₂ , :Γ (, :Δ :Ξ) ⟫ =>
      let Δ' := Expr.push_in arg Δ
      let Ξ' := Expr.push_in (← infer arg) Ξ

      let check_with ← Γ.list_head

      let expected' ← try_step_n 10 ⟪₂ :check_with (, :Δ' :Ξ') ⟫
      let stolen := try_step_n! 10 <| norm_context <| steal_context raw_t_arg expected'
      let norm_expected := try_step_n! 10 <| norm_context expected'

      --dbg_trace stolen
      --dbg_trace s!"subst: {← try_step_n 10 ⟪₂ :check_with (, :Δ' :Ξ') ⟫}"
      --dbg_trace s!"check fn: {check_with}"
      --dbg_trace s!"norm expected: {norm_expected}"
      --dbg_trace s!"norm t arg: {t_arg}"
      --dbg_trace s!"raw infer arg: {← infer arg}"
      --dbg_trace s!"Δ: {Δ'}"

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

def t_i : Expr := ⟪₂ ((, ((:: (((K Data) (I Data)) Data)) ((:: ((>> fst) read)) ((:: ((>> fst) read)) nil)))) ((, nil) nil)) ⟫

#eval Expr.display_infer <$> infer ⟪₂ (>>* read (K' :t_i Data I) (, I I)) Data Data ⟫

/-
S combinator test: I combinator derivation.

S : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α), β x → Type)
  (x : ∀ (z : α) (y : β z), γ z y)
  (y : ∀ (z : α), β z)
  (z : α), γ z (y z)

I = S K K

S Data (I Data) (K' Data Data) (K' Data Data) (K' Data Data Data) Data

Check each component first.

We just need to streal the context from the actual argument,
probably.
-/
#eval Expr.display_infer <$> infer ⟪₂ S Data (I Data) (K' Data Data) ⟫

end Idea
