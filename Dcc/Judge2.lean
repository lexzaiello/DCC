import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-
Combinator version of flip.

flip' f x y = f y x
-/
def flip' : Expr :=
  SK ((Λ) ∘ (((∘) (App ∘ flip)) ∘ (pair id)))

/-
assoc ((a, b), c) = (a, (b, c))

App ((a, b), c) = (a, b) c

flip ((a, b), c) = (c, (b, a))
App (c, (b, a)) = c (b, a)
flip ∘ ⟨flip' coup c, id⟩ (b, a) = (a, (b, c))

((flip' pair id) ∘ (flip' coup)) c = ⟨(flip' coup c), id⟩

⟨id, ((pair id) ∘ (flip' coup))⟩ ((a, b), c)
= ((a, b), ⟨id, (flip' coup c)⟩)

App ∘ flip ∘ ⟨id, ((pair id) ∘ (flip' coup))⟩ = (⟨id, (flip' coup c)⟩, (a, b))
= ⟨id, (flip' coup c)⟩ (a, b) = (a, (b, c))
-/
def assoc : Expr :=
  SK App ∘ flip ∘ ⟨id, ((pair id) ∘ (flip' coup))⟩

#eval Std.format <| (SK (assoc ((Sort 0, Sort 1), Sort 2))).reduce

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

def K'.type (m n : Level) : Expr :=
  SK (Sort m, ⟨(quot Sort n), Λ(⟨id, Λ(⟨snd, quot ∘ fst⟩)⟩)⟩)

def K.type (m n : Level) : Expr :=
  SK (Sort m,
    (flip ∘ ⟨(quot (quot Sort n)), id⟩)
      ≫ (flip' coup ⟨fst, (((≫) flip) ∘ (flip' pair quot))⟩))

/-
S.{[m, n]} : ∀ (α : Sort m) (β : α → Sort n) (γ : ∀ (x : α) (y : β x), Sort o)
  (x : ∀ (x : α) (y : β x), γ x y)
  (y : ∀ (x : α), β x)
  (z : α), γ z (y z)

S.{[m, n]} : (Sort m,
    (flip ∘ ⟨(quot (quot Sort n)), id⟩)
    ≫ (⟨fst, (((≫) snd) ≫ (flip' pair (quot (Sort o))))⟩
[((α, ⟨β, (quot (Sort o))⟩), γ)]
[(α, (⟨β, (quot (Sort o))⟩, γ))]
    ≫ (assoc ∘ ⟨⟨id, (? fst / snd here somehow?)⟩, id⟩)
  )
-/

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
