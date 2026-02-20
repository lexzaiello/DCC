import Mathlib.Data.Nat.Notation

abbrev Level := ℕ

inductive Expr where
  | I       : Level → Expr
  | K       : Level → Level → Expr -- Dependent K
  | K'      : Level → Level → Expr -- Nondependent K
  | S       : Level → Level → Level → Expr -- Dependent S
  | mkcons  : Expr
  -- ^ (mkcons πcons πf πg f g x) = (πcons πf πg (πf f x) (πg g x))
  | judge  : Level  → Expr -- judge t is a freestanding expr
  /-
    Sorts:
  -/
  | type   : Level → Expr
  | prop   : Expr
  | sort   : Level → Expr
  | fst    : Level → Expr
  | snd    : Level → Expr
  | app    : Expr → Expr → Expr
deriving BEq

declare_syntax_cat comb
syntax:max ident (".{" level,+ "}")?    : comb
syntax:max num                          : comb
syntax "Sort" level                     : comb
syntax "Type" level                     : comb
syntax "Prop"                           : comb
syntax:max "(" comb ")"                 : comb
syntax:max "::(" (term ",")? comb,+ ")" : comb

syntax:1022 comb:1022     comb:1023     : comb
syntax:50   comb:51 " : " comb:50       : comb
syntax:40   comb:41 " → " comb:40       : comb
syntax:30   "∀" "(" comb,+ ")" "," comb : comb

