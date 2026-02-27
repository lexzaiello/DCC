import Dcc.Syn.Ast
import Dcc.Syn.Step

syntax comb "→" comb : comb

macro_rules
  | `(SK($α:comb → $β:comb)) => `(SK(Π (quot $α), quot $β))

def Sort.type (m : Level) : Expr := SK(Sort m.succ)
def Syntax.sort : Level := 1
def Syntax.type : Expr           := SK(Sort Syntax.sort)

/-
SKK
α := Syntax
β := (K'.{[Syntax.sort.succ, Syntax.sort]} Syntax.type Syntax Syntax)
γ := (K'.{[Syntax.sort.succ, Syntax.sort]} (Syntax.type → Syntax.type) Syntax (K'.{[Syntax.sort.succ, Syntax.sort.succ]} Syntax.type Syntax.type Syntax))

inner K:

K.{[Syntax.sort, Syntax.sort]} Syntax (Syntax → Syntax)
-/
def Syntax.id : Expr := SK(S.{[Syntax.sort, Syntax.sort.succ, Syntax.sort.succ]}
  Syntax
  (K'.{[Syntax.sort.succ, Syntax.sort]} Syntax.type Syntax Syntax)
  (K'.{[Syntax.sort.succ, Syntax.sort]}
    (Syntax.type → Syntax.type)
    Syntax
    (K'.{[Syntax.sort.succ, Syntax.sort.succ]} Syntax.type Syntax.type Syntax))
  (K'.{[Syntax.sort, Syntax.sort]} Syntax (Syntax → Syntax))
  (K'.{[Syntax.sort, Syntax.sort]} Syntax Syntax))

/-
Note: dom should not see the current arg.
-/

def K'.type (m n : Level) : Expr :=
  SK(Π (quot (Sort m)), Π (quot (Sort n)), Π (1 Syntax.id), Π (1 Syntax.id), (3 Syntax.id))
