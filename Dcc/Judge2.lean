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

/-def K.type (m n : Level) : Expr :=
  SK (Sort m, ⟨(flip ∘ ⟨(quot Sort n), id⟩), Λ(⟨fst, (Λ((((Λ(App ∘ flip) (flip ∘ Λ(⟨id, quot⟩))) ∘ flip) id)⟩)⟩)⟩)-/

/-
K' type:

(Sort m,
in scope: (Sort m, α)
[]                (Sort m
[(Sort m, α)]   , ⟨(quot Sort n)
[α (Sort n, β)] , Λ(⟨id
[(Sort n, β) α] , Λ(⟨snd, quot⟩)⟩)⟩)

(Sort m, ⟨(quot Sort n), Λ(⟨id, Λ(⟨snd, quot⟩)⟩)⟩)

TODO:
- check K' type
- write K type
-/

def K'.type (m n : Level) : Expr :=
  SK (Sort m, ⟨(quot Sort n), Λ(⟨id, Λ(⟨snd, quot⟩)⟩)⟩)

/-def S.type (m n o : Level) : Expr :=
  sorry-/

inductive Judge : Expr → Expr → Prop
--  | k    : Judge (K.type m n) (SK K.{[m, n]})
  | k'   : Judge (K'.type m n) (SK K'.{[m, n]})
  --| s    : Judge (S.type m n o) (SK S.{[m, n, o]})
  | srt  : Judge (SK Sort m.succ) (SK Sort m)
  | app  : Judge (SK (α, β)) f
    → Judge α x
    → Judge (SK (β α x)) (SK (f x))
  | coup : Judge (SK Sort 1) (SK (α, β))
  | pair : Judge (SK Sort 1) (SK ⟨α, β⟩)
  | conv  {α β : Expr} : Judge α x → α.RedTyTrans β → Expr.IsNorm β → Judge β x

def Judge.convD (h_t : Judge t e) : ((t' : Expr) × (PLift (Judge t' e))) :=
  let t' := t.reduce
  let h_t' : Relation.ReflTransGen Expr.RedTy t t' := reduce_sound rfl
  let h_norm := reduce_norm (e := t) (e' := t') rfl
  let h_conv : Judge t' e := by
        rw [← Relation.reflGen_transGen] at h_t'
        match heq : h_t' with
        | .refl => exact h_t
        | .single h =>
          rename_i heq'
          exact Judge.conv h_t h (heq' ▸ h_norm)
  ⟨t', ⟨h_conv⟩⟩

def infer (e : Expr) : ((t : Expr) × (PLift (Judge t e))) :=
  match e with
  | (SK K'.{[m, n]}) => ⟨K'.type m n, ⟨.k'⟩⟩
  | (SK Sort m) => ⟨(SK Sort m.succ), ⟨.srt⟩⟩
  | (SK (α, β)) => ⟨(SK Sort 1), ⟨.coup⟩⟩
  | (SK ⟨α, β⟩) => ⟨(SK Sort 1), ⟨.pair⟩⟩
  | (SK (f x)) => do
    let t_f ← infer f
    let t_x ← infer x

    match t_f with
    | 
