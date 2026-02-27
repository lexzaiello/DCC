import Mathlib.Data.Nat.Notation

abbrev Level := ℕ

inductive Pos where
  | head : Pos
  | tail : Pos → Pos
deriving BEq, Repr

inductive Atom where
  | Sort   : Level → Atom
  | Syntax : Atom
  | K'     : Level → Level → Atom
  | K      : Level → Level → Atom
  | S      : Level → Level → Level → Atom
  | pos    : Pos   → Atom
  | app'   : Atom
  | quot   : Atom  → Atom
deriving BEq, Repr

inductive Expr where
  | atom   : Atom → Expr
  | Pi     : Expr → Expr → Expr
  | app    : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat comb

syntax:max ident                     : comb
syntax num                           : comb
syntax "quot" comb                   : comb
syntax "tail" comb                   : comb
syntax "pos" comb                    : comb
syntax "Sort" term                   : comb
syntax:max "(" comb ")"              : comb
syntax "#" term                      : comb
syntax "Π" "(" comb ")" "," comb     : comb
syntax "K.{" term "}"                : comb
syntax "K'.{" term "}"               : comb
syntax "S.{" term "}"                : comb
syntax "$"                           : comb
syntax "Syntax"                      : comb
syntax:1022 comb:1022     comb:1023  : comb

syntax "SK(" comb ")"   : term
syntax "Pos(" comb ")"  : term
syntax "Atom(" comb ")" : term

macro_rules
  | `(SK(Π ($α:comb), $β:comb)) => `(Expr.Pi (SK($α) SK($β)))
  | `(SK($f:comb $x:comb)) => `(Expr.app SK($f:comb) SK($x:comb))
  | `(Atom(quot $c)) => `(Atom.quot Atom($c))
  | `(Atom(tail $c)) => `(Atom.pos (Pos.tail Pos($c)))
  | `(Atom(pos $c)) => `(Atom.pos Pos($c))
  | `(Pos($n:num)) =>
    match n.getNat with
    | .zero =>
      `(Pos.head)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(Pos.tail (Pos($n':num)))
  | `(Pos($n:ident)) => `($n:term)
  | `(Atom($n:num)) => `(Atom.pos Pos($n:num))
  | `(Atom(Sort $n)) => `(Atom.Sort $n)
  | `(Atom(Syntax)) => `(Atom.Syntax)
  | `(Atom(($c:comb))) => `(Atom($c:comb))
  | `(SK(($c:comb))) => `(SK($c:comb))
  | `(Atom(K.{[$m:term, $n:term]})) => `(Atom.K $m $n)
  | `(Atom(K'.{[$m:term, $n:term]})) => `(Atom.K' $m $n)
  | `(Atom(S.{[$m:term, $n:term, $o:term]})) => `(Atom.S $m $n $o)
  | `(Atom($)) => `(Atom.app')
  | `(SK($id:ident)) =>
    match id with
    | `(ident| $id) =>`($id:term)
  | `(Atom(#$t:term)) => `($t)
  | `(SK(#$t:term)) => `($t)
  | `(SK($c:comb)) => `(Expr.atom Atom($c))

