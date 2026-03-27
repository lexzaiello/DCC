import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

def assoc : Expr :=
  (SK (App ∘ ⟨App ∘ ⟨(∘) ∘ pair, pair⟩, id⟩))

/-
((a, b), c)

flip ((a, b), c) = (c, (a, b))
⟨id, ⟨Λ(flip ((a, b), c) = (c, (a, b))
Λ(⟨pair, id⟩

⟨fst ∘ fst, ⟨snd ∘ fst, snd⟩⟩ ((a, b), c)
= (a, (

Λ(Λ(App∘⟨fst∘fst,⟨snd∘fst,snd⟩⟩))

App ∘ ⟨ (∘) ∘ ⟨Λ(Id), Λ(Id)⟩, Id ⟩
App ∘ ⟨(comp) ∘ ⟨Λ(Id), Λ(Id)⟩, Id⟩ ((a, b), c)
App ∘ ⟨comp ∘ ⟨Λ(Id), Λ(Id)⟩, Id ⟩
App ∘ ⟨ (∘) ∘ ⟨Λ(Id), Λ(Id)⟩, Id ⟩
-/
def assoc_couple : Expr :=
  (SK (App ∘ ⟨App ∘ ⟨(∘) ∘ pair, pair⟩, id⟩))

/-
(a, (b, c)) => ((a, b), c)

(App ∘ ⟨(Λ), id⟩ (a, (b, c))) => App (Λ(a), (b, c))
-/
def unassoc : Expr :=
  (SK App ∘ ⟨(∘) ∘ ⟨Λ(id), Λ(id)⟩, id⟩)
  --(SK flip ∘ ⟨id, flip⟩ ∘ assoc ∘ flip ∘ ⟨id, flip⟩)

#eval Std.format <| (SK ((⟨App ∘ ⟨(∘) ∘ pair, pair⟩, id⟩ ((Sort 0, Sort 1), Sort 2)))).reduce
#eval Std.format <| (SK (#(assoc) ((Sort 0, Sort 1), Sort 2))).reduce

#eval Std.format <| (SK (App ∘ ⟨App ∘ ⟨pair, id⟩, id⟩ ((Sort 0, Sort 1), Sort 2))).reduce

/-
K type:

[]                     (Sort m,
                          Λ(flip)
[((α, (quot Sort n)), β)]  (⟨fst,
[β (α, x)]                       Λ(
[(                                   _
                                   ∘ (unassoc ∘ ⟨App, flip⟩)) -- TODO: (β, (α, x)) -> ((β x), α)
[Sort m, α]               (flip ∘ ⟨(quot Sort n), id⟩))

[]                 (Sort m,
                     Λ(flip) (
[((α, Sort n), β)]     (⟨fst,
[β (                              ))) ∘
[(Sort m, α)]      (flip ∘ ⟨(quot Sort n), quot⟩))

-/
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

Λ(⟨snd, quot⟩) (Sort n, β) α = ⟨β, quot α⟩

(Sort m, ⟨(quot Sort n), Λ(⟨id, Λ(⟨snd, quot⟩)⟩)⟩)

TODO:
- check K' type
- write K type
-/

def K'.type (m n : Level) : Expr :=
  SK (Sort m, ⟨(quot Sort n), Λ(⟨id, Λ(⟨snd, quot ∘ snd⟩)⟩)⟩)

/-def S.type (m n o : Level) : Expr :=
  sorry-/

inductive Judge : Expr → Expr → Prop
--  | k    : Judge (K.type m n) (SK K.{[m, n]})
  | k'   : Judge (K'.type m n) (SK K'.{[m, n]})
  --| s    : Judge (S.type m n o) (SK S.{[m, n, o]})
  | srt  : Judge (SK Sort m.succ) (SK Sort m)
  | app  : Judge (SK (α, β)) f
    → Judge α x
    → Judge (SK (β (α, x))) (SK (f x))
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

def infer (e : Expr) : Option ((t : Expr) × (PLift (Judge t e))) :=
  match e with
  | (SK K'.{[m, n]}) => .some ⟨K'.type m n, ⟨.k'⟩⟩
  | (SK Sort m) => .some ⟨(SK Sort m.succ), ⟨.srt⟩⟩
  | (SK (_α, _β)) => .some ⟨(SK Sort 1), ⟨.coup⟩⟩
  | (SK ⟨_α, _β⟩) => .some ⟨(SK Sort 1), ⟨.pair⟩⟩
  | (SK (f x)) => do
    let ⟨_t_f, ⟨j_f⟩⟩ ← infer f
    let ⟨_t_x, ⟨j_x⟩⟩ ← infer x

    let ⟨t_f, ⟨j_f⟩⟩ := j_f.convD
    let ⟨t_x, ⟨j_x⟩⟩ := j_x.convD

    match t_f with
    | (SK (α, _β)) =>
      if heq : α = t_x then
        let h_t' := Judge.app j_f (heq ▸ j_x)
        .some (Judge.convD h_t')
      else .none
    | _ => .none
  | _ => .none -- TODO: K type, S type

#eval Std.format <| (·.fst) <$> infer (SK (K'.{[3, 2]} (Sort 2) (Sort 1) (Sort 1) (Sort 0)))
