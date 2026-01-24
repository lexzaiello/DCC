import Cm.PiE.Ast

open Expr

/-
For testing purposes.
This mirrors is_step_once exactly.
-/
def do_step_apply : Expr → Except Error Expr
  | ::[::[.id _o, _α], x] => pure x
  | e@::[::[(const _o _p), _α, _β], _c]
  | e@::[::[(const' _o _p), _α, _β], _c] => pure e
  | ::[::[::[(const _o _p), _α, _β], c], _x]
  | ::[::[::[(const' _o _p), _α, _β], c], _x] => pure c
  | ::[::[::[(both o p q), α, β, γ], ::[f, g]], x]
  | ::[::[::[(both' o p q), α, β, γ], ::[f, g]], x] =>
    pure <| ::[@$ o p α β f x, @$ o q α γ g x]
  | ::[::[::[π o p q r, α, β, γ, δ], ::[fx, fxs]], ::[x, xs]] =>
    pure <| ::[@$ o q α γ fx x, @$ p r β δ fxs xs]
  | ::[::[::[::[eq o p, α, β], fn_yes, fn_no], a], b] =>
    if a == b then
      pure <| @$ o p α β fn_yes a
    else
      pure <| @$ o p α β fn_no b
  | e => .error <| .no_rule e

def run (e : Expr) : Except Error Expr := do
  match e with
  | @$ m n fα fβ f x => do
    let eval_both : Except Error Expr := do
      let f' ← run f
      let x' ← run x
      pure <| @$ m n fα fβ f' x'
    let eval_arg_first : Except Error Expr := do
      let x' ← run x
      pure <| @$ m n fα fβ f x'
    let eval_f_first : Except Error Expr := do
      let f' ← run f
      pure <| @$ m n fα fβ f' x
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
  | e => .error <| .no_rule e

def try_step_n (n : ℕ) (e : Expr) : Except Error Expr :=
  match n with
  | .zero => pure e
  | .succ n =>
    match run e with
    | .ok e' => try_step_n n e' <|> (pure e')
    | .error e => .error e

namespace hole

def apply?₀ : Expr := ((apply 0 0).app ?).app ?
def apply?₁ (α : Expr) (m : Option Level := .none) : Expr := ((apply (m.getD 0) 0).app α).app ?

def quote (e : Expr) : Expr := ::[::[const' 0 0, ?, ?], e]
def quote?₁ (α e : Expr) (m : Option Level := .none) : Expr := ::[::[const' (m.getD 0) 0, α, ?], e]

def const?₀ : Expr := ::[const' 0 0, ?, ?]
def const?₁ (α : Expr) (m : Option Level := .none) : Expr := ::[const' (m.getD 0) 0, α, ?]

def both? (f g : Expr) : Expr := ::[::[both' 0 0 0, ?, ?, ?], ::[f, g]]
def both?₁ (α f g : Expr) (m : Option Level := .none) : Expr := ::[::[both' (m.getD 0) 0 0, α, ?, ?], ::[f, g]]

def both?₀ : Expr := ::[both' 0 0 0, ?, ?, ?]

notation "$?"  => (fun (f x : Expr) => @$ 0 0 Expr.hole Expr.hole f x)

/-
  α → β
-/
def imp? (α β : Expr) : Expr := ::[quote α, quote β]

/-
apply : ∀ (α : Type) (β : α → Type) (f : ∀ (x : α), β x) (x : α), β x

-/
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

def apply.type_with_holes (m n : Level) : Expr :=
  -- with α in scope, β : α → Type
  let mk_β : Expr := type_with_holes.mk_β m n

  -- with α in scope, then β in scope
  -- with α in scope, make :: both (:: (quote α) (quote (apply))
  let mk_mk_f := both?₁
    (α := Ty m)
    (f := quote both?₀)
    (g := both?₁
      (α := Ty m)
      (f := const?₀)
      (g := (quote?₁
        (α := (Ty m))
        (e := quote apply?₀)
        (m := m.succ)))
      (m := m.succ))

  -- x : α. this will have α, then β, then f in scope, so we need to quote twice
  -- :: both (:: (quote const) (:: both (:: (quote const) id)))
  -- (:: both (:: (quote const) (:: both (:: (quote const) id)))) α = ::[const, ::[const, α]]
  let mk_mk_x := both?
    (f := quote const?₀)
    (g := both?
      (f := quote const?₀)
      (g := Expr.id m))

  /-
    out type = β x. this is apply ?0 ?0 t_β α β x
    so, this only disregards f.
    apply α β, then quote once
    :: both (:: (quote both) (:: both (:: (quote (quote const)) (apply ?0 ?0 t_β))))
    (:: both (:: (quote both) (:: both (:: (quote (quote const)) (apply ?0 ?0 t_β))))) α
      = :: both (:: (quote const) (apply ?0 ?0 t_β α)
    (:: both (:: (quote const) (apply ?0 ?0 t_β α)) β
      = const (apply ?0 ?0 t_β α β)
    (const (apply ?0 ?0 t_β α β)) f
      = apply ?0 ?0 t_β α β
    apply ?0 ?0 t_β α β x = β x
  -/
  let mk_mk_t_out := both?
    (f := (quote both?₀))
    (g := both?
      (f := quote <| quote <| const?₀)
      (g := .app (apply 0 0) ?))

  both?
    (f := (quote?₁
      (α := (Ty m.succ))
      (e := (Ty m))
      (m := m.succ.succ))) -- first arg, (α : Ty m)
    (g := (both?₁
      (α := Ty m)
      (f := (quote both?₀))
      (g := (both?₁
        (α := Ty m)
        (f := mk_β)
        (g := (both?₁
          (α := Ty m)
          (f := mk_mk_f)
          (g := both?₁
            (α := Ty m)
            (f := mk_mk_x)
            (g := mk_mk_t_out)
            (m := m.succ))
          (m := m.succ)))
        (m := m.succ)))))

/-
β = (K' (Ty 2) (Ty 1) (Ty 1)) (Ty 1) = (Ty 1)
β = ((K' (Ty 2) (Ty 1) (Ty 1)) (Ty 1) : (Ty 2))

β just gives us back Ty 1.
f = (::[id 2, Ty 1])
x = Ty 0

t_f = ∀ (x : Ty 0), β x

This is bringing up the question again of extensionality for
function types.

::[::[::[const'.{[3, 0]}, Ty 2, _], Ty 0], ::[const'.{[0, 0]}, _, _], Ty 2]
How do we compare this against something similar but slightly different?
This looks like [(quote Ty 0), (quote Ty 2)]. This is fine. α =

I hypothesize that this could be because we need to nest apply inside
β. The first const looks totally wrong. I don't know what's up wtiht hat.
-/

def test_reduce_apply_type : Except Error Expr := do
  let m := 1
  let t_α := Ty m.succ
  let α := Ty m
  let β := mk_quote m.succ.succ m.succ t_α α α -- discard (x : α), return α
  let f := ::[id m.succ, α]
  let x := Ty 0
  -- first argument to apply type is α, then β,
  -- then β, then f, then x
  let a₁ ← try_step_n 500 ($? (apply.type_with_holes 2 2) α)
  dbg_trace Expr.head! a₁ == (Ty 2)
  let a₂ ← try_step_n 500 ($? a₁.tail! β)
  dbg_trace Expr.head! a₂ == ::[Ty 1, Ty 2]
  -- got this for β: ::[::[::[const'.{[3, 0]}, Ty 2, _], Ty 1], ::[const'.{[0, 0]}, _, _], Ty 2]
  -- (quote (Ty 1)) → (quote Ty 2), so this is ∀ (x : (Ty 1)), (Ty 2).
  -- this seems right. probably β x = Ty 1, Ty 1 : Ty 2. fine.
  .tail! <$> try_step_n 500 ($? (apply.type_with_holes 2 2) α)
    >>= (fun e => .tail! <$> try_step_n 500 ($? e β))
    >>= (fun e => .tail! <$> try_step_n 500 ($? e f))
    >>= (fun e => .tail! <$> try_step_n 500 ($? e x))

#eval test_reduce_apply_type

/-
id : ∀ (α : Type), α → α
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

example : Expr.tail! <$> try_step_n 500 (@$ 0 0 ? ? (id.type_with_holes 0) (Ty 0))
  >>= (fun (e : Expr) => try_step_n 500 ((mk$ 0 0 ? ?) e (Ty 100))) = (.ok (::[Ty 0, Ty 0])) := rfl

/-
Type inference for filling in holes in expr types.
-/
def infer_holes : Expr → Except Error Expr
  |

end hole

example : try_step_n 100 (f$ (f$ (f$ (apply 0 0) nil) nil) ::[::[id 2, Ty 1], Ty 0]) = (.ok <| Ty 0) := rfl

example : try_step_n 100 (f$ (f$ (f$ (apply 0 0) nil) nil) ::[::[::[const 2 2, Ty 1, Ty 1], Ty 0], Ty 0]) = (.ok <| Ty 0) := rfl
