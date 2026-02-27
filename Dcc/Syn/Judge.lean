import Dcc.Syn.Ast
import Dcc.Syn.Step

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
Reject N syntaxes. Same as K'.
-/
def Syntax.K'.repeat (n : ℕ) (val : Expr) : Expr :=
  Prod.fst <| (List.replicate n (SK(Syntax.sort))).foldr
    (fun _ ⟨acc, t_acc⟩ => ⟨SK(K'.{[Syntax.sort, Syntax.sort]} t_acc Syntax acc)
      , SK(Syntax → t_acc)⟩) (Prod.mk SK(Syntax.K' val) SK(Syntax → Syntax)) (β := Expr × Expr)

/-
Note: index zero refers to self Π binder.
-/

def K'.type (m n : Level) : Expr :=
  SK(Π (quot (Sort m)), Π (quot (Sort n)), Π (1 id), Π (1 id), (3 id))

def K.type (m n : Level) : Expr :=
  SK(Π (quot (Sort m)), Π (quot (Sort n)), Π (1 id), Π ($ (1 id) (0 id)), (3 id))

def S.type (m n o : Level) : Expr :=
  SK(Π (quot (Sort m)),
     Π ($ ($ (rtrn (quot Π)) (0 id)) (quot (Sort n))),
     -- γ type: create a new Π binder from α and β
     -- for β, bind the INNNER Π, not the S Π
     -- by creating a new Π expression:
     -- Π ($ (quot β) (1 id)), (quot (Sort o))
     Π ($ ($ (rtrn (quot Π)) (1 id)) ($
       ($ (rtrn (quot Π)) ($ ($ (rtrn (quot $)) (0 id)) (rtrn (0 id))))
       (rtrn (quot (Sort o))))),
     -- Similarly for x / f, except instead of (quot (Sort o)), do:
     -- $ ($ (quot γ) (2 id)) (1 id)
     Π ($ ($ (rtrn (quot Π)) (2 id)) ($
       ($ (rtrn (quot Π)) ($ ($ (rtrn (quot $)) (1 id)) (rtrn (0 id))))
       ($ ($ (rtrn (quot $)) ($ ($ (rtrn (quot $)) (1 id)) (rtrn (1 id)))) (rtrn (0 id))))),
     Π ($ (rtrn (quot $)) ($ (rtrn (quot Π)) (3 id))
       ($ ($ (rtrn (quot $)) (2 id)) (rtrn (0 id)))),
     Π (4 id),
       ($ ($ (3 id) (0 id)) (1 id) (0 id)))

def Pos.type : Expr :=
  SK((Syntax → Syntax) → Syntax → Syntax)

inductive SynArrow : Expr → Prop
  | pure : SynArrow SK(Syntax)
  | succ : SynArrow β → SynArrow SK(Syntax → β)

inductive Unquote : Expr → Expr → Prop
  | quot : Unquote SK(quot e) e
  | app  : Unquote f f'
    → Unquote x x'
    → Unquote SK($ f x) SK(f' x')

inductive StepUnquote : Expr → Expr → Prop
  | mk : SynStep e e' → Unquote e' e'' → StepUnquote e e''

inductive TyDefEq : Expr → Expr → Expr → Prop
  | quot : TyDefEq e α β
    → TyDefEq e SK(quot α) SK(quot β)
  | pi   : TyDefEq f α α'
    → TyDefEq SK($ f x) β β'
    → TyDefEq f SK(Π (α), β) SK(Π (α'), β')
  | step : SynStep SK(t e) t'
    → TyDefEq e t t'
  | refl : TyDefEq a e e

inductive Judge : Expr → Expr → Prop
  | sort : Judge SK(Sort m.succ) SK(Sort m)
  | app  : Judge SK(Π (α), β) f
    → StepUnquote SK(α (# f.quote)) t_x
    → Judge t_x x
    → StepUnquote SK(β (# SK(f x).quote)) t
    → Judge t SK(f x)
  | K'   : Judge (K'.type m n) SK(K'.{[m, n]})
  | K    : Judge (K.type m n) SK(K.{[m, n]})
  | S    : Judge (S.type m n o) SK(S.{[m, n, o]})
  | quot : Judge SK(Syntax) SK(quot e)
  | syn  : Judge Syntax.type SK(Syntax)
  | pos  : Judge Pos.type (Expr.atom (Atom.pos p))
  | app' : Judge Tf f → Judge Tf x → SynArrow Tf → Judge Tf SK($ f x)
  | deq  : Judge t f
    → TyDefEq f.quote t t'
    → Judge t' f

@[simp] theorem unquote_quot : Unquote SK(quot e) e := Unquote.quot
@[simp] theorem unquote_app : Unquote f f' → Unquote x x' → Unquote SK($ f x) SK(f' x') := Unquote.app
@[simp] theorem step_unquote : SynStep e e' → Unquote e' e'' → StepUnquote e e'' := StepUnquote.mk
@[simp] theorem step_unquote₁ : SynStep e SK(quot e') → StepUnquote e e' :=
  (StepUnquote.mk · Unquote.quot)

example : Judge SK(Syntax → Syntax → Syntax) Syntax.K' := by
  apply Judge.deq
  apply Judge.app
  apply Judge.app
  apply Judge.K'
  apply StepUnquote.mk
  apply SynStep.quot
  apply Unquote.quot
  apply Judge.syn
  apply StepUnquote.mk
  apply SynStep.quot
  apply Unquote.quot
  apply StepUnquote.mk
  apply SynStep.quot
  apply Unquote.quot
  apply Judge.syn
  apply StepUnquote.mk
  apply SynStep.quot
  apply Unquote.quot
  apply TyDefEq.pi
  apply TyDefEq.step
  apply SynStep.tail
  apply SynStep.head
  apply SynStep.id
  apply TyDefEq.quot
  apply TyDefEq.pi
  apply TyDefEq.step
  apply SynStep.tail
  apply SynStep.head
  apply SynStep.id
  apply TyDefEq.step
  apply SynStep.tail
  apply SynStep.tail
  apply SynStep.tail
  apply SynStep.head
  apply SynStep.id
  exact SK(pos 0)
  exact SK(pos 0)
