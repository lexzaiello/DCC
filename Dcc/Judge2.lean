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

def S.type (m n o : Level) : Expr :=
  SK (Sort m,
    {snd ≫ (flip' coup (quot (Sort n))),
      {Λ(⟨snd, (((≫) snd) ∘ snd) ≫ (flip' pair (quot (Sort o)))⟩),
        {Λ(Λ(assoc ≫ (⟨snd, ⟨snd ≫ (((≫) snd) ≫ lens),
                   (Λ(Λ(snd ∘ ⟨App ∘ ⟨snd, snd⟩, snd⟩)))⟩⟩))),
          {Λ(Λ(Λ(fst ≫ fst ≫ ⟨snd, snd ≫ ((≫) snd)⟩))),
            {fst ≫ fst ≫ fst ≫ fst ≫ snd,
            Λ(Λ(Λ(Λ(Λ(⟨⟨((App ∘ ⟨App ∘ ⟨snd ≫ S.{[m, n, o.succ]}, snd⟩,
            (quot (quot (quot (Sort o))))⟩) ∘ fst), snd⟩, snd⟩)))))}}}}})

inductive Judge : Expr → Expr → Prop
  | k    : Judge (K.type m n) (SK K.{[m, n]})
  | k'   : Judge (K'.type m n) (SK K'.{[m, n]})
  | s    : Judge (S.type m n o) (SK S.{[m, n, o]})
  | srt  : Judge (SK Sort m.succ) (SK Sort m)
  | app  : Judge (SK t_f) f
    → Judge (SK (fst t_f)) x
    → Judge (SK ((snd t_f) ((fst t_f), x))) (SK (f x)) -- TODO: if can't decrease here, just use {}
  | coup : Judge (SK Sort 1) (SK (α, β))
  | pair : Judge (SK Sort 1) (SK ⟨α, β⟩)
  | conv  {α β : Expr} : Judge α x → α.RedTyTrans β → Expr.IsNorm β → Judge β x
  | conv' {α β : Expr} : Judge β x → α.RedTyTrans β → Expr.IsNorm β → Judge α x

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

    let maybe_α := (SK (fst t_f)).reduce!?

    match heq : maybe_α with
    | .some α =>
      let red_α := reduce!?_sound (e' := α) (by rw [← heq])
      let h_norm : Expr.IsNorm α := reduce!?_norm (by rw [← heq])
      if heq' : α = t_x then
          let h_t' :=
            Judge.app j_f (.conv' j_x (by rw [← heq']; exact red_α) (by rw [← heq']; exact h_norm))
          .some (Judge.convD h_t')
      else .none
    | .none => .none
  | _ => .none -- TODO: K type, S type

#eval Std.format <| (·.fst) <$> infer (SK (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1)))

#eval Std.format <| (·.fst) <$> infer (SK (K'.{[3, 2]} (Sort 2) (Sort 1) (Sort 1) (Sort 0)))
#eval Std.format <| (·.fst) <$> infer (SK (K.{[3, 2]} (Sort 2)
  (K'.{[3, 3]} (Sort 2) (Sort 2) (Sort 1)) (Sort 1) (Sort 0)))
