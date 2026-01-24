import Cm.PiE.Ast

open Expr

/-
apply just turns a list into an app.
-/

/-
For testing purposes.
This mirrors is_step_once exactly.
-/
def do_step_apply : Expr → Except Error Expr
  | ::[.nil _m n, _α, _x] => pure <| Ty n -- this can downgrade a dependent type to a nondependent type
  | ::[.id _o, _α, x] => pure x
  | ::[const _o _p, _α, _β, c, _x] => pure <| c
  | ::[both o p q, α, β, γ, ::[f, g], x] => -- TODO: not sure whether to nest ::[f, g] here, or leave flat
    pure <| ::[f$ (apply o p) ::[α, β, f, x], f$ (apply o q) ::[α, γ, g, x]]
  | ::[π o p q r, α, β, γ, δ, ::[fx, fxs], ::[x, xs]] =>
    pure <| ::[f$ (apply o q) ::[α, γ, fx, x], f$ (apply p r) ::[β, δ, fxs, xs]]
  | ::[eq o p, α, β, ::[fn_yes, fn_no], a, b] =>
    if a == b then
      pure <| f$ (apply o p) ::[α, β, fn_yes, a]
    else
      pure <| f$ (apply o p) ::[α, β, fn_no, b]
  | e => .error <| .no_rule e

def run (e : Expr) : Except Error Expr := do
  match e with
  | f$ a@(apply _m _n) ::[fα, fβ, f, x] => do
    let eval_both : Except Error Expr := do
      let f' ← run f
      let x' ← run x
      pure <| f$ a ::[fα, fβ, f', x']
    let eval_arg_first : Except Error Expr := do
      let x' ← run x
      pure <| f$ a ::[fα, fβ, f, x']
    let eval_f_first : Except Error Expr := do
      let f' ← run f
      pure <| f$ a ::[fα, fβ, f', x]
    let step_whole : Except Error Expr := do
      do_step_apply <| ::[f, x]

    eval_f_first <|> eval_both <|> eval_arg_first <|> step_whole
  | :: x xs => (do
    let x' ← run x
    let xs' ← run xs
    pure <| :: x' xs') <|> (do
    let xs' ← run xs
    pure <| :: x xs') <|> (do
    let x' ← run x
    pure <| :: x' xs)
  | e => .error <| .stuck e

def try_step_n (n : ℕ) (e : Expr) : Except Error Expr :=
  match n with
  | .zero => pure e
  | .succ n =>
    match run e with
    | .ok e' => try_step_n n e' <|> (pure e')
    | .error e => .error e

namespace hole

def π? (fx 

def quote (e : Expr) : Expr := ::[::[const' 0 0, ?, ?], e]
def quote?₁ (α e : Expr) (m : Option Level := .none) : Expr := ::[::[const' (m.getD 0) 0, α, ?], e]

def const?₀ : Expr := ::[const' 0 0, ?, ?]
def const?₁ (α : Expr) (m : Option Level := .none) : Expr := ::[const' (m.getD 0) 0, α, ?]
def quote?_n (n : ℕ) : Expr → Expr :=
  (List.replicate n const?₀).foldr (fun e acc => ::[e, acc])

def both? (f g : Expr) (α : Option Expr := .none) (m : Option Level := .none) : Expr :=
  ::[::[both' (m.getD 0) 0 0, (α.getD .hole), ?, ?], ::[f, g]]
def both?₁ (α f g : Expr) (m : Option Level := .none) : Expr := ::[::[both' (m.getD 0) 0 0, α, ?, ?], ::[f, g]]
def both?₀ (α : Option Expr := .none) (m : Option Level := .none) : Expr :=
  ::[both' (m.getD 0) 0 0
  , (α.getD .hole)
  , ? , ?]

def mkapp? (e : Expr) (α β : Option Expr := .none) (m n : Option Level := .none) : Expr :=
  f$ (apply (m.getD 0) (n.getD 0)) ::[::[α.getD .hole, β.getD .hole], e]

def id? (α : Option Expr := .none) (m : Option Level := .none) := ::[id (m.getD 0), α.getD .hole]

/-
curried n * quote
:: both (:: (quote const) id)
-/
def quote?_n₀ (n : ℕ) (α : Option Expr := .none) (m : Option Level := .none) : Expr :=
  (List.replicate n (quote const?₀)).foldr (fun e acc => both? e acc) (@id? α m)

-- for n λ binders. this expands into n * (n * const(both))
-- this "binds" n binders deep by injecting n future both's
def both?_n (n : ℕ) (f g : Expr) (α : Option Expr := .none) (m : Option Level := .none) : Expr :=
  ((List.range n).tail.map (fun n => quote?_n n both?₀)).foldr
    (fun e acc => both? e acc) (both? (f := f) (g := g) (α := α) (m := m))

example : try_step_n 200 (mkapp? ::[mkapp? ::[mkapp? ::[quote?_n 3 (Ty 0), (Ty 0)], Ty 0], Ty 0])  = (.ok (Ty 0)) := rfl

/-
  α → β
-/
def imp? (α β : Expr) : Expr := ::[quote α, quote β]

def apply.type_with_holes.mk_β (m n : Level) : Expr :=
  -- with α in scope, β : α → Type
  -- :: both (:: const (quote (quote Ty n)))
  -- this const is wrong. α : Ty m, f := (const t_α ? α)
  -- f looks fine ish.
  -- missing a both. after α is applied, we should get
  -- a future both that will pass along the (x : α)
  both?₁
    (α := (Ty m))
    (f := (quote both?₀))
    (g :=
      both?₁
        (α := (Ty m))
        (f := (const?₁ (α := (Ty m)) (m := m.succ)))
        (g := (quote <| quote <| Ty n))
        (m := m.succ))
   (m := m.succ)

-- (Ty 0) → (Ty 2)
--#eval try_step_n 200 (mkapp? ::[apply.type_with_holes.mk_β 1 2

/-
id : ∀ (l : ((α : Type) × α)), l.fst

id : :: π 
-/
def id.type_with_holes (m : Level) : Expr :=
  both?
    (f := (quote?₁ (Ty m.succ) (Ty m) (m := m.succ.succ)))
    (g := (both?₁
      (α := (Ty m))
      (f := (quote?₁ (Ty m) both?₀ (m := m.succ)))
      (g := (both?₁
        (α := (Ty m))
        (f := (const?₁ (α := Ty m) (m := m.succ)))
        (g := (const?₁ (α := Ty m) (m := m.succ)))
        (m := m.succ)))
      (m := m.succ)))

/-
const' : ∀ (α : Type) (β : Type) (x : α) (y : β x), α

-/
def const'.type_with_holes (m n : Level) : Expr :=
  sorry

example : Expr.tail! <$> try_step_n 500 (mkapp? ::[id.type_with_holes 0, Ty 0])
  >>= (fun (e : Expr) => try_step_n 500 (mkapp? ::[e, Ty 100])) = (.ok (::[Ty 0, Ty 0])) := rfl

/-
Type inference for filling in holes in expr types.
-/
/-def infer_holes : Expr → Except Error Expr
  |-/

example : try_step_n 100 (mkapp? ::[::[id 2, Ty 1], Ty 0]) = (.ok <| Ty 0) := rfl

example : try_step_n 100 (mkapp? ::[::[::[const 2 2, Ty 1, Ty 1], Ty 0], Ty 0]) = (.ok <| Ty 0) := rfl

end hole

