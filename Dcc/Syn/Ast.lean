import Mathlib.Data.Nat.Notation

abbrev Level := ℕ

inductive Pos where
  | head : Pos
  | tail : Pos → Pos
deriving BEq, Repr

def Pos.toNat : Pos → ℕ
  | .head => 0
  | .tail xs => xs.toNat.succ

instance : ToString Pos where
  toString p := toString p.toNat

inductive Atom where
  | Sort   : Level → Atom
  | Syntax : Atom
  | K'     : Level → Level → Atom
  | K      : Level → Level → Atom
  | S      : Level → Level → Level → Atom
  | id     : Atom
  | pos    : Pos   → Atom
  | app'   : Atom
  | Pi     : Atom
deriving BEq, Repr

instance : ToString Atom where
  toString e := match e with
    | .Sort m => s!"Sort {m}"
    | .Syntax => "Syntax"
    | .K' m n => s!"K'." ++ "{" ++ [m, n].toString ++ "}"
    | .K m n => s!"K." ++ "{" ++ [m, n].toString ++ "}"
    | .S m n o => s!"S." ++ "{" ++ [m, n, o].toString ++ "}"
    | .id => "id"
    | .pos p => toString p
    | .app' => "$"
    | .Pi => "Π"

inductive Expr where
  | atom   : Atom → Expr
  | app    : Expr → Expr → Expr
  | quot   : Expr → Expr
deriving BEq, Repr

def Expr.toString (e : Expr) : String :=
  match e with
  | .app (.app (.atom .app') f) g => s!"($ {f.toString} {g.toString})"
  | .atom a => ToString.toString a
  | .app f x => s!"({f.toString} {x.toString})"
  | .quot e => s!"(quot {e.toString})"

instance : ToString Expr where
  toString := Expr.toString

declare_syntax_cat comb

syntax:max ident                     : comb
syntax num                           : comb
syntax "quot" comb                   : comb
syntax "tail" comb                   : comb
syntax "pos" comb                    : comb
syntax "Sort" term                   : comb
syntax:max "(" comb ")"              : comb
syntax "#" term                      : comb
syntax:max "Π" "(" comb ")" "," comb : comb
syntax "Π"                           : comb
syntax "K.{" term "}"                : comb
syntax "K'.{" term "}"               : comb
syntax "id"                          : comb
syntax "S.{" term "}"                : comb
syntax "$"                           : comb
syntax "Syntax"                      : comb
syntax:1022 comb:1022     comb:1023  : comb

syntax "SK(" comb ")"   : term
syntax "Pos(" comb ")"  : term
syntax "Atom(" comb ")" : term

macro_rules
  | `(SK(quot $)) => `(SK(quot (#Expr.atom Atom.app')))
  | `(Atom(Π)) => `(Atom.Pi) -- Π has no evaluation rule. Syntax.
  | `(SK(quot $c)) => `(Expr.quot SK($c))
  | `(SK(tail $c)) => `(Expr.atom Atom(tail $c))
  | `(SK(pos $c)) => `(Expr.atom Atom(pos $c))
  | `(SK(Π ($α:comb), Π ($β:comb), $γ:comb)) => `(SK(Π $α (quot (Π ($β:comb), $γ:comb))))
  | `(SK(Π ($α:comb), $β:comb)) => `(SK(Π $α $β))
  | `(SK($ $f:comb $g:comb)) => `(Expr.app (Expr.app (Expr.atom Atom.app') SK($f)) SK($g))
  | `(SK($f:comb $x:comb)) => `(Expr.app SK($f:comb) SK($x:comb))
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
  | `(Atom($n:ident)) => `($n:term)
  | `(Atom($n:num)) => `(Atom.pos Pos($n:num))
  | `(Atom(Sort $n)) => `(Atom.Sort $n)
  | `(Atom(Syntax)) => `(Atom.Syntax)
  | `(Atom(($c:comb))) => `(Atom($c:comb))
  | `(SK(($c:comb))) => `(SK($c:comb))
  | `(Atom(id)) => `(Atom.id)
  | `(Atom(K.{[$m:term, $n:term]})) => `(Atom.K $m $n)
  | `(Atom(K'.{[$m:term, $n:term]})) => `(Atom.K' $m $n)
  | `(Atom(S.{[$m:term, $n:term, $o:term]})) => `(Atom.S $m $n $o)
  | `(SK($ide:ident)) => `($ide:term)
  | `(Atom(#$t:term)) => `($t)
  | `(SK(#$t:term)) => `($t)
  | `(SK($c:comb)) => `(Expr.atom Atom($c))

@[simp] def Expr.quote : Expr → Expr
  | .quot e => .quot e
  | SK(f x) => SK($ (# f.quote) (#x.quote))
  | e => .quot e

syntax comb:66 " → " comb : comb

macro_rules
  | `(SK($a:comb → $b:comb)) => `(SK(Π (quot $a), (quot $b)))

def Sort.type (m : Level) : Expr := SK(Sort m.succ)
def Syntax.sort : Level          := 1
def Syntax.type : Expr           := SK(Sort Syntax.sort)

/-
Reject one syntax, output a constant syntax
-/
def Syntax.K'      : Expr := SK(K'.{[Syntax.sort, Syntax.sort]} Syntax Syntax)
def Syntax.K'.type : Expr := SK(Syntax → Syntax → Syntax)
abbrev rtrn : Expr := Syntax.K'
