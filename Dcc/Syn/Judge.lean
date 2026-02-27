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
  SK(Π (quot (Sort m)), Π ($ ($ (quot Π) (0 id)) (quot (Sort n))), Π (1 id), Π ($ (1 id) (0 id)), (3 id))

def S.type (m n o : Level) : Expr :=
  SK(Π (quot (Sort m)),
     Π ($ ($ (quot Π) (0 id)) (quot (Sort n))),
     -- γ type: create a new Π binder from α and β
     -- for β, bind the INNNER Π, not the S Π
     -- by creating a new Π expression:
     -- Π ($ (quot β) (1 id)), (quot (Sort o))
     Π ($ ($ (quot Π) (1 id)) ($
       ($ (quot Π) ($ ($ (quot $) (0 id)) (rtrn (0 id))))
       (quot (Sort o)))),
     -- Similarly for x / f, except instead of (quot (Sort o)), do:
     -- $ ($ (quot γ) (2 id)) (1 id)
     Π ($ ($ (quot Π) (2 id)) ($
       ($ (quot Π) ($ ($ (quot $) (1 id)) (0 id)))
       ($ ($ (quot $) ($ ($ (quot $) (1 id)) (1 id))) (0 id)))),
     Π ($ (quot $) ($ (quot Π) (3 id))
       ($ ($ (quot $) (2 id)) (0 id))),
     Π (4 id),
       ($ ($ (3 id) (0 id)) (1 id) (0 id)))

def Pos.type : Expr :=
  SK((Syntax → Syntax) → Syntax → Syntax)

inductive SynArrow : Expr → Prop
  | pure : SynArrow SK(Syntax)
  | succ : SynArrow β → SynArrow SK(Syntax → β)

inductive Unquote : Expr → Expr → Prop
  | refl : Unquote e e
  | quot : Unquote e e'
    → Unquote SK(quot e) e'
  | app  : Unquote f f'
    → Unquote x x'
    → Unquote SK($ f x) SK(f' x')

inductive TyDefEq : Expr → Expr → Expr → Prop
  | unquote : Unquote t t'
    → TyDefEq e t' t''
    → TyDefEq e t t''
  | quote   : Unquote t t'
    → TyDefEq e t t''
    → TyDefEq e t' t''
  | congq   : TyDefEq e t t'
    → TyDefEq e SK(quot t) SK(quot t')
  | pi      : TyDefEq f SK(α (#f.quote)) α'
    → TyDefEq SK(f x) SK(β (# SK(f x).quote)) β'
    → TyDefEq f SK(Π (α), β) SK(Π (α'), β')
  | step    : SynStep t t'
    → TyDefEq e t' t''
    → TyDefEq e t t''
  | refl    : TyDefEq a t t

inductive Judge : Expr → Expr → Prop
  | sort : Judge SK(Sort m.succ) SK(Sort m)
  | app  : Judge SK(Π (α), β) f
    → Judge SK(α (# f.quote)) x
    → Judge SK(β (# SK(f x).quote)) SK(f x)
  | K'   : Judge (K'.type m n) SK(K'.{[m, n]})
  | K    : Judge (K.type m n) SK(K.{[m, n]})
  | S    : Judge (S.type m n o) SK(S.{[m, n, o]})
  | quot : Judge SK(Syntax) SK(quot e)
  | syn  : Judge Syntax.type SK(Syntax)
  | pos  : Judge Pos.type (Expr.atom (Atom.pos p))
  | app' : Judge Tf f → Judge Tf x → SynArrow Tf → Judge Tf SK($ f x)
  | deq  : Judge t f  → TyDefEq f t t' → Judge t' f
  | deq' : Judge t' f → TyDefEq f t t' → Judge t f

theorem K'.partial_app (α β : Expr) (m n : Level) (h_t_α : Judge SK(Sort m) α) (h_t_β : Judge SK(Sort n) β) : Judge SK(α → β → α) SK(K'.{[m, n]} α β) := by
  apply Judge.deq
  apply Judge.app
  apply Judge.deq
  apply Judge.app
  apply Judge.deq
  apply Judge.K'
  apply TyDefEq.refl
  apply Judge.deq'
  exact h_t_α
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.unquote
  apply Unquote.quot
  apply Unquote.refl
  apply TyDefEq.refl
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.unquote
  apply Unquote.quot
  apply Unquote.refl
  apply TyDefEq.refl
  apply Judge.deq'
  assumption
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.unquote
  apply Unquote.quot
  apply Unquote.refl
  apply TyDefEq.refl
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.unquote
  apply Unquote.quot
  apply Unquote.refl
  apply TyDefEq.pi
  apply TyDefEq.step
  apply SynStep.tail
  apply SynStep.head
  apply SynStep.id
  apply TyDefEq.refl
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.unquote
  apply Unquote.quot
  apply Unquote.refl
  apply TyDefEq.quote
  apply Unquote.quot
  apply Unquote.refl
  apply TyDefEq.congq
  apply TyDefEq.pi
  apply TyDefEq.step
  apply SynStep.tail
  apply SynStep.head
  apply SynStep.id
  apply TyDefEq.refl
  apply TyDefEq.step
  repeat apply SynStep.tail
  apply SynStep.head
  apply SynStep.id
  apply TyDefEq.refl
  exact SK(pos 0)
  exact SK(pos 0)

/-
(K Syntax (K' Syntax.type Syntax Syntax) (quot (Sort 0)) (quot (Sort 0))) : Syntax
-/
example : Judge SK(Syntax) SK(K.{[Syntax.sort, Syntax.sort]} Syntax
  (K'.{[Syntax.sort.succ, Syntax.sort]} Syntax.type Syntax Syntax)
  (quot (Sort 0))
  (quot (Sort 0))) := by
  apply Judge.deq
  apply Judge.app
  apply Judge.app
  apply Judge.app
  apply Judge.app
  apply Judge.K
  apply StepUnquote.mk
  apply SynStep.quot
  apply Unquote.quot
  apply Unquote.refl
  apply Judge.syn
  apply StepUnquote.mk
  apply SynStep.quot
  apply Unquote.quot
  apply Unquote.refl
  apply StepUnquote.mk
  apply SynStep.app'
  apply SynStep.app'
  apply SynStep.quot
  apply SynStep.head
  apply SynStep.id
  apply SynStep.quot
  apply Unquote.app
  apply Unquote.app
  repeat (apply Unquote.quot; apply Unquote.refl)
  apply Judge.app
  apply K'.partial_app
  apply Judge.sort
  apply Judge.syn
  apply StepUnquote.mk
  apply SynStep.quot
  apply Unquote.quot
  apply Unquote.refl
  apply Judge.syn
  apply StepUnquote.mk
  apply SynStep.quot
  apply Unquote.quot
  
  sorry
