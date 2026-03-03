import Dcc.Syn.Ast
import Dcc.Syn.Step
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate

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

inductive TyDefEq : Expr → Expr → Expr → Prop
  | app'     : TyDefEq e f f'
    → TyDefEq e x x'
    → TyDefEq e SK($ f x) SK(f' x')
  | pi       : TyDefEq f SK(α (quot f)) α'
    → TyDefEq SK(f (pos 0)) SK(β (quot (f (pos 0)))) β'
    → TyDefEq f SK(Π (α), β) SK(Π (α'), β')
  | step     : SynStep t t'
    → TyDefEq e t' t''
    → TyDefEq e t t''
  | refl     : TyDefEq a t t
  | quoted   : TyDefEq e t t'
    → TyDefEq e SK(quot t) t'
  | symm     : TyDefEq e t t'
    → TyDefEq e t' t

inductive Judge : Expr → Expr → Prop
  | sort    : Judge SK(Sort m.succ) SK(Sort m)
  | app     : Judge SK(Π (α), β) f → Judge SK(α (quot f)) x → Judge SK(β (quot (f x))) SK(f x)
  | K'      : Judge (K'.type m n) SK(K'.{[m, n]})
  | K       : Judge (K.type m n) SK(K.{[m, n]})
  | S       : Judge (S.type m n o) SK(S.{[m, n, o]})
  | quot    : Judge SK(Syntax) SK(quot e)
  | syn     : Judge Syntax.type SK(Syntax)
  | pos     : Judge Pos.type (Expr.atom (Atom.pos p))
  | app'    : Judge Tf f → Judge Tf x → SynArrow Tf → Judge Tf SK($ f x)
  | deq     : Judge t f  → TyDefEq f t t' → Judge t' f

@[simp] theorem simp_quoted (h_t : Judge t e) : Judge SK(quot t) e := Judge.deq h_t (TyDefEq.unquoted TyDefEq.refl)
@[simp] theorem simp_quoted_app (h_t : Judge SK(quot t) e) : Judge SK((quot t) x) e := by
  apply Judge.deq
  exact h_t
  apply TyDefEq.symm
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.refl
@[simp] theorem simp_quoted_app' : Judge t e → Judge SK((quot t) x) e := simp_quoted_app ∘ simp_quoted
@[simp] theorem simp_defeq_quot : TyDefEq e SK((quot a) b) SK(quot a) := by
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.refl

@[simp] theorem K'.partial_app.extracted_1_1
  {spine : Expr}
  {t_α α : Expr} :
  TyDefEq α (t_α.quot.app spine) t_α := by
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.quoted
  apply TyDefEq.refl
@[simp] theorem K'.partial_app.extracted_1_2
  {spine : Expr}
  {t_α α : Expr} :
  TyDefEq α (t_α.quot.app spine) t_α.quot := by
  apply TyDefEq.symm
  apply TyDefEq.quoted
  apply TyDefEq.symm
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.quoted
  apply TyDefEq.refl

@[simp] theorem simp_step_id_head :
  SynStep SK((0 id) (quot (a b))) SK(quot b) := by
  apply SynStep.head
  apply SynStep.id

syntax "n_pos" num : tactic
syntax "n_sub" num : tactic
syntax "app_n" num term : tactic
syntax "quot_app" : tactic

macro_rules
  | `(tactic| n_pos $n:num) =>
    `(tactic| (iterate $n (apply SynStep.tail)); apply SynStep.head; apply SynStep.id)
  | `(tactic| app_n $n:num $judge_spine:term) =>
    `(tactic| ((iterate $n (apply Judge.deq; apply Judge.app)); apply $judge_spine; apply Judge.deq))
  | `(tactic| quot_app) =>
    `(tactic| apply TyDefEq.step; apply SynStep.quot; apply TyDefEq.quoted; apply TyDefEq.refl)

theorem K'.partial_app (α β : Expr) (m n : Level) (h_t_α : Judge SK(Sort m) α) (h_t_β : Judge SK(Sort n) β) : Judge SK(α → β → α) SK(K'.{[m, n]} α β) := by
  app_n 2 Judge.K'
  exact h_t_α
  apply TyDefEq.symm
  simp
  quot_app
  apply Judge.deq
  exact h_t_β
  apply TyDefEq.symm
  simp
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.quoted
  apply TyDefEq.pi
  apply TyDefEq.step
  n_pos 1
  apply TyDefEq.refl
  apply TyDefEq.symm
  apply TyDefEq.quoted
  apply TyDefEq.symm
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.quoted
  apply TyDefEq.pi
  apply TyDefEq.step
  n_pos 1
  apply TyDefEq.refl
  apply TyDefEq.symm
  apply TyDefEq.quoted
  apply TyDefEq.symm
  apply TyDefEq.step
  n_pos 3
  apply TyDefEq.quoted
  apply TyDefEq.refl

/-
(K Syntax (K' Syntax.type Syntax Syntax) (quot (Sort 0)) (quot (Sort 0))) : Syntax
-/
example : Judge SK(Syntax) SK(K.{[Syntax.sort, Syntax.sort]} Syntax
  (K'.{[Syntax.sort.succ, Syntax.sort]} Syntax.type Syntax Syntax)
  (quot (Sort 0))
  (quot (Sort 0))) := by
  app_n 4 Judge.K
  exact Judge.syn
  apply TyDefEq.symm
  quot_app
  quot_app
  apply Judge.deq
  apply Judge.app
  apply K'.partial_app
  exact Judge.sort
  exact Judge.syn
  apply Judge.deq
  exact Judge.syn
  apply TyDefEq.symm
  quot_app
  apply TyDefEq.symm
  apply TyDefEq.step
  apply SynStep.app'
  apply SynStep.app'
  apply SynStep.quot
  n_pos 0
  apply SynStep.quot
  apply TyDefEq.symm
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.quoted
  apply TyDefEq.symm
  apply TyDefEq.app'
  apply TyDefEq.app'
  apply TyDefEq.quoted
  apply TyDefEq.refl
  apply TyDefEq.refl
  apply TyDefEq.refl
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.quoted
  apply TyDefEq.refl
  apply Judge.deq
  apply Judge.quot
  apply TyDefEq.symm
  apply TyDefEq.step
  apply SynStep.tail
  apply SynStep.head
  apply SynStep.id
  apply TyDefEq.quoted
  apply TyDefEq.refl
  apply TyDefEq.step
  apply SynStep.quot
  apply TyDefEq.quoted
  apply TyDefEq.refl
  apply Judge.deq
  apply Judge.quot
  apply TyDefEq.symm
  apply TyDefEq.step
  

  sorry
