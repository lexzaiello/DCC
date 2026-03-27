import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-

-/

/-
Combinator version of flip.

flip f x y = f y x

App ∘ flip ∘ ⟨id, f⟩

Λ(?) 

Λ(pair f) x y = (f, (x, y))

flip' f x y = f y x

(coup f) x y = (f, x)

(App ∘ flip ∘ (pair id) f x y) = f y x

(pair id) f = ⟨id, f⟩

⟨id, f⟩ x y

(Λ(App ∘ flip ∘ ⟨id, Sort 0⟩) (Sort 1) (Sort 2))

Λ ∘ (((∘) App)∘ ((∘) flip) ∘ (pair id))

⟨f, id⟩ x y = ⟨f, id⟩(x, y) = (f x, y)
-/
def flip' : Expr :=
  SK ((Λ) ∘ (((∘) (App ∘ flip)) ∘ (pair id)))

#eval Std.format <| (SK ((((Λ) ∘ (((∘) (App ∘ flip)) ∘ (pair id))) (Sort 0)) (Sort 1) (Sort 2))).reduce

#eval Std.format <| (SK (Λ(App ∘ flip ∘ ⟨id, Sort 0⟩) (Sort 1) (Sort 2))).reduce
#eval Std.format <| (SK (flip' (Sort 0) (Sort 1) (Sort 2))).reduce

/-
(f ≫ g) a = g (f a), as opposed to (f ∘ g) a = f (g a)
-/

def pipe : Expr :=
  SK (flip' (∘))

syntax:50 expr:50 "≫" expr:51 : expr

syntax "(" "≫" ")" : expr

macro_rules
  | `(SK $f:expr ≫ $g:expr) => `(SK (#(pipe) $f:expr $g:expr))
  | `(SK (≫)) => `(pipe)

def assoc : Expr :=
  (SK (App ∘ ⟨App ∘ ⟨(∘) ∘ pair, pair⟩, id⟩))

/-
App₂ f (x, y) = f x y

⟨f, id⟩ (x, y) = (f x, y)

(App ∘ ⟨f, id⟩) (x, y) = f x y

((pair ≫ id) ≫ ((∘) App)) f = ⟨f, id⟩

((pair ≫ id)
-/
def App₂ : Expr :=
  SK (((flip' pair id)) ≫ ((∘) App))

#eval Std.format <| (SK (App₂ (Sort 0) (Sort 1, Sort 2))).reduce

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

App ∘ ⟨coup ∘ (coup a), id⟩

⟨() ∘ coup

(App ∘ ⟨(Λ), id⟩ (a, (b, c))) => App (Λ(a), (b, c))
=> Λ(a) (b, c) =>
-/
def unassoc : Expr :=
  (SK App ∘ ⟨(∘) ∘ ⟨Λ(id), Λ(id)⟩, id⟩)
  --(SK flip ∘ ⟨id, flip⟩ ∘ assoc ∘ flip ∘ ⟨id, flip⟩)

#eval Std.format <| (SK ((⟨App ∘ ⟨(∘) ∘ pair, pair⟩, id⟩ ((Sort 0, Sort 1), Sort 2)))).reduce
#eval Std.format <| (SK (#(assoc) ((Sort 0, Sort 1), Sort 2))).reduce

#eval Std.format <| (SK (App ∘ ⟨App ∘ ⟨pair, id⟩, id⟩ ((Sort 0, Sort 1), Sort 2))).reduce

/-
K type:
[]                       (Sort m,
[Sort m, α]                ⟨(quot (quot Sort n)), id⟩
[((α, (quot Sort n)), β)]  ≫ ⟨fst, (((≫) flip)  ∘ (flip' pair quot))⟩)                       => (α, β ∘ fst) -- ⟨β, quot⟩ ∘ flip (α, x) = (β x, quot α)


K type:

[]           (Sort m,
[Sort m, α]  flip ∘ ⟨(quot (quot Sort n)), id⟩ => (α, quot Sort n)

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
  SK (Sort m, ⟨(quot Sort n), Λ(⟨id, Λ(⟨snd, quot ∘ fst⟩)⟩)⟩)

def K.type (m n : Level) : Expr :=
  SK (Sort m, (flip ∘ ⟨(quot (quot Sort n)), id⟩) ≫ (flip' coup
    ⟨fst, (((≫) flip)  ∘ (flip' pair quot))⟩) -- ((α, (quot (Sort n))), β)
  --  ≫ ⟨fst, (((≫) flip)  ∘ (flip' pair quot))⟩
  )

/-def S.type (m n o : Level) : Expr :=
  sorry-/

inductive Judge : Expr → Expr → Prop
--  | k    : Judge (K.type m n) (SK K.{[m, n]})
  | k    : Judge (K.type m n) (SK K.{[m, n]})
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
  | (SK K.{[m, n]}) => .some ⟨K.type m n, ⟨.k⟩⟩
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

#eval Std.format <| (·.fst) <$> infer (SK (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1)))

#eval Std.format <| (·.fst) <$> infer (SK (K'.{[3, 2]} (Sort 2) (Sort 1) (Sort 1) (Sort 0)))
#eval Std.format <| (·.fst) <$> infer (SK (K.{[3, 2]} (Sort 2)
  (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1)) (Sort 1) (Sort 0)))
