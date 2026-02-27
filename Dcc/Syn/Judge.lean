import Dcc.Syn.Ast
import Dcc.Syn.Step

syntax comb:66 " → " comb : comb

macro_rules
  | `(SK($a:comb → $b:comb)) => `(SK(Π (quot $a), (quot $b)))

def Sort.type (m : Level) : Expr := SK(Sort m.succ)
def Syntax.sort : Level          := 1
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
Reject one syntax, output a constant syntax
-/
def Syntax.K'      : Expr := SK(K'.{[Syntax.sort, Syntax.sort]} Syntax Syntax)
def Syntax.K'.type : Expr := SK(Syntax → Syntax → Syntax)

/-
Reject N syntaxes. Same as K'.
-/
def Syntax.K'.repeat (n : ℕ) (val : Expr) : Expr :=
  Prod.fst <| (List.replicate n (SK(Syntax.sort))).foldr
    (fun _ ⟨acc, t_acc⟩ => ⟨SK(K'.{[Syntax.sort, Syntax.sort]} t_acc Syntax acc)
      , SK(Syntax → t_acc)⟩) (Prod.mk SK(Syntax.K' val) SK(Syntax → Syntax)) (β := Expr × Expr)

abbrev rtrn : Expr := Syntax.K'

/-
Note: index zero refers to self Π binder.
-/

def K'.type (m n : Level) : Expr :=
  SK(Π (quot (Sort m)), Π (quot (Sort n)), Π (1 Syntax.id), Π (1 Syntax.id), (3 Syntax.id))

def K.type (m n : Level) : Expr :=
  SK(Π (quot (Sort m)), Π (quot (Sort n)), Π (1 Syntax.id), Π ($ (1 Syntax.id) (0 Syntax.id)), (3 Syntax.id))

def S.type (m n o : Level) : Expr :=
  SK(Π (quot (Sort m)),
     Π ($ ($ (rtrn (quot Π)) (0 Syntax.id)) (quot (Sort n))),
     -- γ type: create a new Π binder from α and β
     -- for β, bind the INNNER Π, not the S Π
     -- by creating a new Π expression:
     -- Π ($ (quot β) (1 Syntax.id)), (quot (Sort o))
     Π ($ ($ (rtrn (quot Π)) (1 Syntax.id)) ($
       ($ (rtrn (quot Π)) ($ ($ (rtrn (quot $)) (0 Syntax.id)) (rtrn (0 Syntax.id))))
       (rtrn (quot (Sort o))))),
     -- Similarly for x / f, except instead of (quot (Sort o)), do:
     -- $ ($ (quot γ) (2 Syntax.id)) (1 Syntax.id)
     Π ($ ($ (rtrn (quot Π)) (2 Syntax.id)) ($
       ($ (rtrn (quot Π)) ($ ($ (rtrn (quot $)) (1 Syntax.id)) (rtrn (0 Syntax.id))))
       ($ ($ (rtrn (quot $)) ($ ($ (rtrn (quot $)) (1 Syntax.id)) (rtrn (1 Syntax.id)))) (rtrn (0 Syntax.id))))),
     Π ($ (rtrn (quot $)) ($ (rtrn (quot Π)) (3 Syntax.id))
       ($ ($ (rtrn (quot $)) (2 Syntax.id)) (rtrn (0 Syntax.id)))),
     Π (4 Syntax.id),
       ($ ($ (3 Syntax.id) (0 Syntax.id)) (1 Syntax.id) (0 Syntax.id)))

def Pos.type : Expr :=
  SK((Syntax → Syntax) → Syntax → Syntax)

inductive SynArrow : Expr → Prop
  | pure : SynArrow SK(Syntax)
  | succ : SynArrow β → SynArrow SK(Syntax → β)

inductive Judge : Expr → Expr → Prop
  | sort : Judge SK(Sort m.succ) SK(Sort m)
  | app : Judge SK(Π (α), β) f
    → SynStep SK(α (# f.quote)) α'
    → Judge (Expr.unquote α') x
    → SynStep SK(β (# SK(f x).quote)) β'
    → Judge β' SK(f x)
  | K'   : Judge (K'.type m n) SK(K'.{[m, n]})
  | K    : Judge (K.type m n) SK(K.{[m, n]})
  | S    : Judge (S.type m n o) SK(S.{[m, n, o]})
  | quot : Judge SK(Syntax) SK(quot e)
  | syn  : Judge Syntax.type SK(Syntax)
  | pos  : Judge Pos.type (Expr.atom (Atom.pos p))
  | app' : Judge Tf f → Judge Tf x → SynArrow Tf → Judge Tf SK($ f x)

#eval toString SK(Syntax → Syntax → Syntax)

example : Judge SK(Syntax → Syntax → Syntax) Syntax.K' := by
  apply Judge.app
  apply Judge.app
  apply Judge.K'
  apply SynStep.quot
  apply Judge.syn
  apply SynStep.quot
  unfold Syntax.type
  apply SynStep.quot
  
