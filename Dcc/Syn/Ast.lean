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
deriving BEq, Repr

inductive Expr where
  | atom   : Atom → Expr
  | Pi     : Expr → Expr  → Expr
  | app    : Expr → Expr → Expr
deriving BEq, Repr

declare_syntax_cat comb

syntax:max ident                     : comb
syntax num                           : comb
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

syntax "SK(" comb ")"  : term
syntax "Pos(" comb ")" : term

macro_rules
  | `(Pos($n:num)) =>
    match n.getNat with
    | .zero =>
      `(Pos.head)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(Pos.tail (Pos($n':num)))
  | `(SK($n:num)) => `(Expr.atom (Atom.pos Pos($n:num)))
  | `(SK(Sort $n)) => `(Expr.atom (Atom.Sort $n))
  | `(SK(Syntax)) => `(Expr.atom (Atom.Syntax))
  | `(SK(($c:comb))) => `(SK($c:comb))
  | `(SK(Π ($α:comb), $β:comb)) => `(Expr.Pi (SK($α) SK($β)))
  | `(SK(K.{[$m:term, $n:term]})) => `(Expr.atom (Atom.K $m $n))
  | `(SK(K'.{[$m:term, $n:term]})) => `(Expr.atom (Atom.K' $m $n))
  | `(SK(S.{[$m:term, $n:term, $o:term]})) => `(Expr.atom (Atom.S $m $n $o))
  | `(SK($)) => `(Expr.atom (Atom.app'))
  | `(SK($id:ident)) =>
    match id with
    | `(ident| $id) =>`($id:term)
  | `(SK(#$t:term)) => `($t)
  | `(SK($f:comb $x:comb)) => `(Expr.app SK($f:comb) SK($x:comb))
