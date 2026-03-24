import Mathlib.Data.Nat.Notation
import Batteries.Data.String.Matcher
open Std (ToFormat Format)
open Std.ToFormat (format)

-- Infinite sort universe hierarchy
abbrev Level := ℕ

-- Core computational combinators. Standard. K' for downgrading a dependent type to a nondependent one.
inductive Comb where
  | K'     : Level → Level → Comb
  | K      : Level → Level → Comb
  | S      : Level → Level → Level → Comb
deriving BEq, Repr, Lean.ToExpr, DecidableEq

/-
The type combinators are seperate from the term-level combinators.
They have no types, except when inferred under a Π binder.
Note that this is BCKI.
Size is guaranteed to decrease.
Can reduce all type transformations at once.
-/
inductive TyComb where
  | next   : TyComb
  | read   : TyComb
  | comp   : TyComb
  | flip   : TyComb
deriving BEq, Repr, Lean.ToExpr, DecidableEq

inductive Expr where
  | tyhole : Expr   → Expr -- __ : τ. May not be necessary due to inference rule for BCKI. Vestigial.
  | tycomb : TyComb → Expr
  | cons   : Expr
  | Srt    : Level  → Expr
  | comb   : Comb   → Expr
  | app    : Expr   → Expr → Expr
deriving BEq, Repr, Lean.ToExpr, DecidableEq

/-
DSL:
  Type combinators:
  - K* = Expr.tycomb .next
  - B = Expr.tycomb .comp
  - I = Expr.tycomb .read
  - C = Expr.tycomb .flip

  Types:
  - Π α, β = Expr.Pi (SK α) (SK β)
  - Sort m = Expr.Srt m

  Core:
  - S.{[m, n, o]} = .comb (.S m n o)
    Where m, n, o refer to universe levels.
  - K'.{[m, n]} = .comb (.K' m n )
    Where m, n refer to universe levels.
  - K.{[m, n]} = .comb (.K m n)
    Where m, n refer to universe levels.
  - (f x_1 ... x_n) = (.app (SK f) (SK x_1)).app ...

  Utility macros (not corresponding to AST elements directly):
  - Arrow macro:
    - α → β = (Π α, K* β)
  - Arg macro:
    - (arg 0 f) = B f I
    - (arg (n + 1) f) = K* (arg n f)
    This macro allows discarding `n` arguments under a Π binder, then applying a function to the selected argument to it.
    Kind of simulates Debruijn Indices: (arg 1 I) a b = I b.
  - Ret macro:
    - (ret 0) = I
    - (ret (n + 1)) = (B K* (ret n))
    This macro is the inverse of arg. It discards `m` arguments after a "selected" argument:
    (arg 1 (ret 1)) a b c = b
-/

namespace dsl

declare_syntax_cat expr

declare_syntax_cat levels
declare_syntax_cat comb

syntax "cons" : expr

syntax "(" expr,* ")" : expr

syntax ".{" term "}" : levels

syntax "K" : comb
syntax "K'" : comb
syntax "S" : comb

syntax expr "∘" expr : expr
syntax comb levels : expr
syntax "#(" term ")" : expr
syntax "(" expr* ")" : expr
syntax "Type" term  : expr
syntax "B" : expr
syntax "C" : expr
syntax "K*" : expr
syntax "I" : expr
syntax "Sort" term : expr
syntax expr "∶" expr : expr
syntax expr "→" expr : expr
syntax ident : expr

syntax "SK" expr : term

macro_rules
  | `(SK cons) => `(Expr.cons)
  | `(SK ($a:expr, $xs:expr,*)) => `(SK (cons $a:expr ($xs:expr,*)))
  | `(SK #($t:term)) => `($t)
  | `(SK $f:expr ∘ $g:expr) => `(SK (B $f:expr $g:expr))
  | `(SK $idt:ident) => `($idt:term)
  | `(SK K.{[$m:term, $n:term]}) => `(Expr.comb (Comb.K $m:term $n:term))
  | `(SK K'.{[$m:term, $n:term]}) => `(Expr.comb (Comb.K' $m:term $n:term))
  | `(SK S.{[$m:term, $n:term, $o:term]}) => `(Expr.comb (Comb.S $m:term $n:term $o:term))
  | `(SK B) => `(Expr.tycomb (TyComb.comp))
  | `(SK C) => `(Expr.tycomb (TyComb.flip))
  | `(SK K*) => `(Expr.tycomb (TyComb.next))
  | `(SK I) => `(Expr.tycomb (TyComb.read))
  | `(SK Sort $m:term) => `(Expr.Srt $m)
  | `(SK Type $n:term) => `(Expr.Srt ($n + 1))
  | `(SK ($e:expr)) => `(SK $e)
  | `(SK ($f:expr $x:expr)) => `(Expr.app (SK $f:expr) (SK $x:expr))
  | `(SK __ ∶ $t:expr) => `(Expr.tyhole (SK $t))
  | `(SK ($f:expr $x:expr $xs:expr*)) => `(SK (($f:expr $x:expr) $xs:expr*))

end dsl

namespace Expr

def toFormat : Expr → Format
  | SK Sort m => s!"Sort {m}"
  | SK cons => "cons"
  | SK B => "B"
  | SK C => "C"
  | SK I => "I"
  | SK K* => "K*"
  | SK K'.{[m, n]} => "K'.{" ++ (format [m, n]) ++ "}"
  | SK K.{[m, n]} => "K.{" ++ (format [m, n]) ++ "}"
  | SK S.{[m, n, o]} => "S.{" ++ (format [m, n, o]) ++ "}"
  | SK (f x) => .bracket "(" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) ")"
  | SK __ ∶ t => "__ : " ++ t.toFormat

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩

/-
Bracket abstraction for types
-/

end Expr

namespace bracket

abbrev Var := String

inductive BExpr where
  | var  : Var   → BExpr
  | app  : BExpr → BExpr → BExpr
  | raw  : Expr  → BExpr
  | forE : BExpr → BExpr → BExpr → BExpr
deriving BEq

declare_syntax_cat expr'

syntax "#" term                              : expr'
syntax expr                                  : expr'
syntax ident                                 : expr'
syntax "∀" "(" expr' ":" expr' ")" "," expr' : expr'
syntax:50 expr':50 expr':51                  : expr'

syntax "SK⟦" expr' "⟧" : term

macro_rules
  | `(SK⟦#$et:term⟧) => `($et:term)
  | `(SK⟦$nm:ident⟧) =>
    let nm := Lean.Syntax.mkStrLit nm.getId.lastComponentAsString
    `(BExpr.var $nm)
  | `(SK⟦∀ ($nm:expr' : $α:expr'), $cod:expr'⟧) =>
    `(BExpr.forE SK⟦$nm⟧ SK⟦$α⟧ SK⟦$cod⟧)
  | `(SK⟦$f:expr' $x:expr'⟧) => `(BExpr.app SK⟦$f:expr'⟧ SK⟦$x:expr'⟧)
  | `(SK⟦$e:expr⟧) => `(BExpr.raw (SK $e))

open Lean

#eval SK⟦∀ (x : Sort 1), Sort 1⟧

def BExpr.mem_var (v : Var) (in_e : BExpr) : Bool :=
  match in_e with
  | SK⟦∀ (#x : #α), #bdy⟧ => x == .var v ∨ bdy.mem_var v ∨ α.mem_var v
  | SK⟦#f #x⟧ => f.mem_var v || x.mem_var v
  | .var v' => v == v'
  | .raw _e => false

abbrev Ctx := List Var

/-
abstraction algorithm:
1. bdy var = bind var, then select the head with I,
but reject all arguments in the context so far
2. var other than bind var, find its position in the context
  K* as many arguments as its index is
-/

def mk_ret (n : ℕ) : BExpr :=
  match n with
  | .zero => SK⟦I⟧
  | .succ n => SK⟦B K* #mk_ret n⟧

/-
Replace all vars with new var.
-/
def BExpr.rename (replace find : Var) (in_e : BExpr) : BExpr :=
  match in_e with
  | .var v => if v == find then .var replace else .var v
  | .app f x => .app (f.rename replace find) (x.rename replace find)
  | .forE bind ty bdy => .forE bind (ty.rename replace find) (bdy.rename replace find)
  | .raw e => .raw e

/-
Generate a fresh name from v if it is already in context.
Vars are first in first out.
-/
def Var.mk_fresh (ctx : Ctx) (v : Var) : Var :=
  let matching := ctx.filterMap (fun v' =>
    if v'.containsSubstr v then
      pure v'.length
    else .none)
  flip Option.getD v <| matching.mergeSort.reverse.head?.map (s!"{·}.1")

/-
Note: ∀ (x, binder var should only be added to context in the body
since arg not received in type
-/
def Var.mk_var (ctx : Ctx) (v : Var) : Option BExpr := do
  let idx ← ctx.findIdx? (· == v)
  let ret := mk_ret <| ctx.length - idx
  pure <| (List.replicate idx (BExpr.raw (SK K*))).foldr BExpr.app ret

/-
Ex: ∀ (x : α) (y : β x), γ

assuming in scope [
-/
def mk_app (f x : BExpr) : Option BExpr := do
  sorry

def BExpr.abstract (ctx : Ctx) (bdy : BExpr) : Option BExpr :=
  match bdy with
  | .var v => v.mk_var ctx
  | .app f x =>
    

end bracket
