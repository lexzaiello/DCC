import Dcc.Syn.Ast
import Dcc.Syn.Step

syntax comb "→" comb : comb

macro_rules
  | `(SK($α:comb → $β:comb)) => `(SK(Π (#Expr.quote SK($α)), (#Expr.quote SK($β))))

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
  SK(Π (quot (Sort m)), Π (quot (Sort n)), Π (2 Syntax.id), Π (2 Syntax.id), (3 Syntax.id))

def K.type (m n : Level) : Expr :=
  SK(Π (quot (Sort m)), Π (quot (Sort n)), Π (2 Syntax.id), Π ($ (2 Syntax.id) (3 Syntax.id)), (3 Syntax.id))

def S.type (m n o : Level) : Expr :=
  SK(Π (quot (Sort m)),
     Π ($ ($ (rtrn Π) (1 Syntax.id)) (quot (Sort n))),
     -- γ type: create a new Π binder from α and β
     -- for β, bind the INNNER Π, not the S Π
     -- by creating a new Π expression:
     -- Π ($ (quot β) (1 Syntax.id)), (quot (Sort o))
     Π ($ ($ (rtrn Π) (2 Syntax.id)) ($
       ($ (rtrn Π) ($ ($ (rtrn $) (1 Syntax.id)) (rtrn (1 Syntax.id))))
       (rtrn (quot (Sort o))))),
     -- Similarly for x / f, except instead of (quot (Sort o)), do:
     -- $ ($ (quot γ) (2 Syntax.id)) (1 Syntax.id)
     Π ($ ($ (rtrn Π) (3 Syntax.id)) ($
       ($ (rtrn Π) ($ ($ (rtrn $) (2 Syntax.id)) (rtrn (1 Syntax.id))))
       ($ ($ (rtrn $) ($ ($ (rtrn $) (2 Syntax.id)) (rtrn (1 Syntax.id)))) (rtrn (0 Syntax.id))))),
     Π ($ (rtrn $) ($ (rtrn Π) (4 Syntax.id))
       ($ ($ (rtrn $) (3 Syntax.id)) (rtrn (1 Syntax.id)))),
     Π (5 Syntax.id),
       ($ ($ (3 Syntax.id) (0 Syntax.id)) (1 Syntax.id) (0 Syntax.id)))

def Pos.type : Expr :=
  SK((Syntax → Syntax) → Syntax → Syntax)

inductive SynArrow : Expr → Prop
  | pure : SynArrow SK(Syntax)
  | succ : SynArrow β → SynArrow SK(Syntax → β)

inductive SynStep : Expr → Expr → Prop
  | quot : SynStep SK((quot e) x) SK(quot e)
  | head : SynStep SK(0 f ($ qf qx)) SK(f qx)
  | tail : SynStep SK((tail xs) f ($ qf qx)) SK((pos xs) f qf)
  | app' : SynStep SK(($ f x) c) SK($ (f c) (x c))

inductive Judge : Expr → Expr → Prop
  | sort : Judge SK(Sort m.succ) SK(Sort m)
  | app : Judge SK(Π (α), β) f
    → Judge SK(α (# f.quote)) x
    → Judge β SK(f x)
  | K'   : Judge (K'.type m n) SK(K'.{[m, n]})
  | K    : Judge (K.type m n) SK(K.{[m, n]})
  | S    : Judge (S.type m n o) SK(S.{[m, n, o]})
  | quot : Judge SK(Syntax) SK(quot e)
  | syn  : Judge Syntax.type SK(Syntax)
  | pos  : Judge Pos.type (Expr.atom (Atom.pos p))
  | app' : Judge Tf f → Judge Tf x → SynArrow Tf → Judge Tf SK($ f x)
  | lsyn : Judge t e  → SynStep t t' → Judge t' e
  | rsyn : Judge t e  → SynStep t' t → Judge t' e

example : Judge SK(Syntax → Syntax → Syntax) Syntax.K' := by
  apply Judge.app
  apply Judge.app
  
