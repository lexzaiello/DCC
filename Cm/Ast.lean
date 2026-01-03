/-
  An approach to dependently-typed combinators that models contexts as combinatory objects in and of themselves.
-/

import Mathlib.Data.Nat.Notation

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

def Expr.any_data_as_list : Expr → Option (List Expr)
  | e@⟪₂ :: :_x :_xs ⟫ => e.as_list
  | ⟪₂ , :a :b ⟫ => do return a :: (← b.any_data_as_list)
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

example : Expr.as_list ⟪₂ :: Data (:: K Data) ⟫ = [⟪₁ Data ⟫, ⟪₁ K ⟫, ⟪₁ Data ⟫] := rfl

example : Expr.push_in ⟪₂ Data ⟫ ⟪₂ :: Data K ⟫ = ⟪₂ :: Data (:: K Data) ⟫ := rfl

syntax "quot" : atom
macro_rules
  | `(⟪₁ quot ⟫) => `(⟪₂ K Data (I Data) ⟫)
