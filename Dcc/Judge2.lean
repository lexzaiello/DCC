import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

def assoc : Expr :=
  (SK (App ∘ ⟨App ∘ ⟨comp ∘ pair, pair⟩, id⟩))

def assoc_couple : Expr :=
  (SK (⟨id, ⟨id, id⟩⟩ ∘ assoc))

#eval Std.format <| (SK ((⟨App ∘ ⟨comp ∘ pair, pair⟩, id⟩ ((Sort 0, Sort 1), Sort 2)))).reduce
#eval Std.format <| (SK (#(assoc) ((Sort 0, Sort 1), Sort 2))).reduce

/-
K' : (Sort m,
  Λ(⟨quot Sort n
  -- α in scope, then Sort n, then β
  -- grab α and β
  , Λ(⟨id
    -- β, then α, then x in scope
    -- make (β, α), then done
    -- Λ(id) ∘ snd β 
    , quot ∘ Λ(⟨id, quot⟩)⟩)⟩)
-/

/-
β : α → Type
map Sort n and α to (flip ∘ ⟨quot Sort n, id⟩)

mk_t_β = (flip ∘ ⟨quot Sort n, id⟩)

with (α → Type) and β in scope

receive in scope α and x
with α and β in scope, we want to capture β
Λ(assoc)
want to make (α, Λ(

Λ(β) gets in scope

α and x

we want to flip this.

assoc can do this nicely.

assoc β α x = ⟨β, ⟨α x⟩⟩

then we can do

⟨β, id⟩ ∘ flip ⟨α, x⟩

= ⟨β, id⟩ (x, α)

(β x, α)

(Λ(flip) id) β = ⟨β, id⟩



K : (Sort m, ⟨(flip ∘ ⟨quot Sort n, id⟩), Λ(⟨fst, (Λ((((Λ(App ∘ flip) (flip ∘ Λ(⟨id, quot⟩))) ∘ flip) id)⟩)⟩)⟩)

(α, Λ(

mk_t_x 

 Λ(
K : (Sort m, Λ(⟨(quot Sort n)
-/

def K.type (m n : Level) : Expr :=
  let α_ty := (SK Sort m)
  -- make α → Sort n from scope: Sort m, α. get rid of Sort m first
  let β_ty := (SK (quot (flip ∘ (Λ(id) (quot Sort n)))))
  -- with (α → Sort n), β in scope
  -- make x : α type with fst ∘ fst
  -- (y : β x) will have in scope β, α, and x
  --
  let x_βx_ty := (SK Λ(⟨
    fst, -- (x : α)
    -- β in scope here, then α, then x. want to make (y : β x), and quot α at the end
    -- can do this with ⟨β, quot (quot α)⟩
    
    Λ(Λ(
  sorry

def K'.type (m n : Level) : Expr :=
  SK (Sort m,
  Λ(⟨(quot Sort n)
  -- α in scope, then Sort n, then β
  -- grab α and β
  , Λ(⟨id
    -- β, then α, then x in scope
    -- make (β, α), then done
    -- Λ(id) ∘ snd β
    , quot ∘ Λ(⟨id, quot⟩)⟩)⟩))

def S.type (m n o : Level) : Expr :=
  sorry

inductive Judge : Expr → Expr → Prop
  | k    : Judge (K.type m n) (SK K.{[m, n]})
  | k'   : Judge (K'.type m n) (SK K'.{[m, n]})
  | s    : Judge (S.type m n o) (SK S.{[m, n, o]})
  | srt  : Judge (SK Sort m.succ) (SK Sort m)
  | app  : Judge (SK (α, β)) f
    → Judge α x
    → Judge (SK (β x)) (SK (f x))
  | coup : Judge (SK Sort 1) (SK (α, β))
  | pair : Judge (SK Sort 1) (SK ⟨α, β⟩)
  | conv  {α β : Expr} : Judge α x → α.RedTyTrans β → Expr.IsNorm β → Judge β x
