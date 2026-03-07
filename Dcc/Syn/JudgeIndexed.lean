import Dcc.Syn.AstIndexed

open Std (Format)
open Std.ToFormat (format)

/-
Another change:
dom in apps receive the entire quoted app

I really like the idea of carrying the context around.

with : Syntax
^ we can probably derive this somehow.

Need to make $ point-free, though.

the other alternative is concatenating contexts.

with (quot (f x))

what about for anonymous ($ f, x)?

e.g., (β x)

Feels like with should be nesting binders...

with (Π α, β) (quot (f x)) (quot y) = (Π α, β) (quot ((f) y))

with can let us simulate contexts without the explict book-keeping.

(unquot _) (quot β) (quot x)

TODO:
- account for offset from removing f arg
- need to change app inference rule:
  - need to only plug in (quot x), and need to do it before anything else
- point-free Syntax, different inferene rule for with app
- quote.type'

new pattern:
- $, assume point-free variants of the combinators
-/

namespace Expr

inductive red : Expr → Expr → Prop
  | I      : red ⸨(I m) α x⸩ x
  | K      : red ⸨(K m n) α β x y⸩ x
  | K'     : red ⸨(K' m n) α β x y⸩ x
  | S      : red ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi     : red ⸨(Π' α, β) x⸩ (Π' ⸨α x⸩, ⸨β x⸩) -- stepping Π does not substitute binders. we assume here we have the full app
  | head   : red ⸨(head fn) (quot ⸨f x⸩)⸩ ⸨fn (quot f)⸩
  | tail   : red ⸨(tail fn) (quot ⸨f x⸩)⸩ ⸨fn (quot x)⸩
  | app'   : red ⸨$ (f, x) e⸩ ⸨⸨f e⸩ ⸨x e⸩⸩ -- this is fine, since ($ can infer what kind of Syntax α
  | into   : red ⸨(into fn) (quot f) (quot x)⸩ ⸨fn (quot ⸨f x⸩)⸩
  | unquot : red ⸨(unquot _m) α (quot e)⸩ e
  | left   : red f f' → red ⸨f x⸩ ⸨f' x⸩
  | right  : red x x' → red ⸨f x⸩ ⸨f x'⸩

abbrev SynId := Syntax.id
abbrev SynConst := Syntax.const

abbrev Syntax.id' := Syntax.id ?_ 1
abbrev Syntax.const' := Syntax.const ?_ ?_ 1 1

def mk_arrow (α β : Expr) (m n : Level) : Expr :=
  Π' ⸨(Syntax.const (Srt m) α m.succ m) α⸩, ⸨(Syntax.const (Srt n) α n.succ m) β⸩

def mk_const_n (e α : Expr) (m : Level) (t_args : List (Level × Expr)) : Expr :=
  Prod.snd <| t_args.foldr (fun (n, t_arg) (t_acc, acc) =>
    ((mk_arrow t_acc t_arg m n), ⸨(K' m n) t_acc t_arg acc⸩)) (α, e)

def unquote_const (α β : Expr) (m n : Level) : Expr :=
  $ (⸨(K' m 1) (Syntax α) (mk_arrow α (mk_arrow β α n m) m m) ⸨(K' m n) α β⸩⸩, ⸨(unquot m) α⸩)

/-
Types for quotation combinators
-/
abbrev Syntax.type (_t : Expr) (m : Level) := (Srt m)

abbrev quot.type (α _e : Expr) := (Syntax α)

abbrev unquot.type' (m : Level) : Expr :=
  sorry

abbrev unquot.type (m : Level) := Π' (0 ⸨(Syntax.const (Srt m.succ) (Syntax (Srt m)) m.succ.succ m.succ) (Srt m)⸩)
  , Π' ?_, (1 ⸨(unquot m) (Srt m)⸩)

abbrev Pi.type : Expr → Expr := id

abbrev app'.type (_f x : Expr) (α γ : Expr) (m : Level) :=
  Π' α
   , $ (γ, 0 ⸨(unquot m) α⸩, $ (x, 0 ⸨(unquot m) α⸩))

abbrev head.type (_fn β γ : Expr) : Expr := Π' ($ (⸨(Syntax.const ?_ ?_ 1 1) β⸩, head (Syntax.id ?_ 1)))
                                             , ($ (⸨(Syntax.const ?_ ?_ 1 1) γ⸩, head (Syntax.id ?_ 1)))

abbrev tail.type (_fn β γ : Expr) : Expr := Π' ($ (⸨(Syntax.const ?_ ?_ 1 1) β⸩, tail (Syntax.id ?_ 1)))
                                             , ($ (⸨(Syntax.const ?_ ?_ 1 1) γ⸩, tail (Syntax.id ?_ 1)))
abbrev hole.type : Expr → Expr := id

abbrev Srt.type (m : Level) : Expr := (Ty m)

/-
0 f = head f
1 f = (tail (head f))
-/

/-
Types for the core combinators:
-/

abbrev α_sort (m : Level) : Expr :=
  ⸨(K' m.succ.succ m.succ) (Srt m.succ) (Syntax (Srt m)) (Srt m)⸩

abbrev α_to_sort (m n : Level) : Expr :=
  into (Π' (head (head ⸨(unquot m.succ) (Srt m)⸩))
       , ⸨(K' n.succ.succ 1) (Srt n.succ) ?_ (Srt n)⸩)

abbrev I.type (m : Level) : Expr :=
    Π' (α_sort m)
  , into (Π' (head ⸨(unquot 1) ?_⸩)
  , (head ⸨(unquot 1) ?_⸩))

abbrev K'.type (m n : Level) : Expr :=
    Π' (α_sort m)
  , into (Π' ⸨(K' n.succ.succ 1) (Srt n.succ) (Syntax ?_) (Srt n)⸩
  , into (Π' (head (head ⸨(unquot 1) ?_⸩))
  , into (Π' (head (head (tail ⸨(unquot 1) ?_⸩))), (head (head (head ⸨(unquot 1) ?_⸩))))))

abbrev K.type (m n : Level) : Expr :=
    Π' (α_sort m)
  , Π' (α_to_sort m n)
  , Π' (2 ⸨(unquot m.succ) (Srt m)⸩)
  , Π' ($ (2 ⸨(unquot n.succ) ?_⸩, 1 ⸨(unquot m) ?_⸩))
  , (3 ⸨(unquot m.succ) (Srt m)⸩)

/-abbrev S.type (m n o : Level) : Expr :=
    Π' (α_sort m)
  , Π' (β_to_sort m n)
  , Π' (Π' (2 (unquote_const (Srt m) ?_ m.succ 1))
      , Π' sorry), sorry-/

/-
Def infer / eval for prototyping:
-/

def eval (e : Expr) : Except Format Expr :=
  match e with
  | ⸨(I _m) _α x⸩ => eval x <|> pure x
  | ⸨(K _m _n) _α _β x _y⸩ => eval x <|> (pure x)
  | ⸨(K' _m _n) _α _β x _y⸩ => eval x <|> (pure x)
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => (do return ⸨(← ⸨x z⸩.eval) (← ⸨y z⸩.eval)⸩) <|>
     (do return ⸨(← ⸨x z⸩.eval) ⸨y z⸩⸩) <|>
     (do return ⸨⸨x z⸩ (← ⸨y z⸩.eval)⸩) <|>
     (do return ⸨⸨x z⸩ ⸨y z⸩⸩)
  | ⸨(into fn) (quot f) (quot x)⸩ => (eval ⸨fn (quot ⸨f x⸩)⸩) <|> pure ⸨fn (quot ⸨f x⸩)⸩
  | ⸨(Π' α, β) x⸩ => return Π' ⸨α x⸩, ⸨β x⸩
  | ⸨(head fn) (quot ⸨f _x⸩)⸩ => eval ⸨fn (quot f)⸩ <|> pure ⸨fn (quot f)⸩
  | ⸨(tail fn) (quot ⸨_f x⸩)⸩ => eval ⸨fn (quot x)⸩ <|> pure ⸨fn (quot x)⸩
  | ⸨$ (f, x) e⸩ => (do return ⸨(← ⸨f e⸩.eval) (← ⸨x e⸩.eval)⸩) <|>
     (do return ⸨(← ⸨f e⸩.eval) ⸨x e⸩⸩) <|>
     (do return ⸨⸨f e⸩ (← ⸨x e⸩.eval)⸩) <|>
     (do return ⸨⸨f e⸩ ⸨x e⸩⸩) -- this is fine, since ($ can infer what kind of Syntax α
  | ⸨⸨(unquot _m) _α⸩ (quot e)⸩ => eval e <|> (pure e)
  | ⸨f x⸩ => (do return ⸨(← f.eval) (← x.eval)⸩) <|> ((·.app x) <$> (f.eval)) <|> (f.app <$> (x.eval))
  | e => .error <| "stuck: " ++ (format e)

def norm (e : Expr) (gas : ℕ := 100) : Expr :=
  match gas with
    | .zero => e
    | .succ n => norm ((eval e).toOption.getD e) n

partial def infer (e : Expr) : Except Format Expr := do
  let not_type (t : Expr) := Except.error <| "not a type: " ++ (format t)
  let not_fn (t : Expr) := Except.error <| "not a function type: " ++ (format t)
  let mismatch (expected actual : Expr) := .error <| (format expected) ++ " ≠ " ++ (format actual)

  let rec defeq (t₁ : Expr) (t₂ : Expr) (gas : ℕ := 100) : Except Format Expr :=
    match gas, t₁, t₂ with
    | .zero , _, _ => .error "out of gas"
    | .succ n, (Π' α₁, β₁), (Π' α₂, β₂) => do
      let _ ← defeq α₁ α₂ n

      defeq β₁ β₂ n
    | _, (Syntax ?_), t@(Syntax _α) => pure t
    | _, t₁, t₂ =>
      let t₁' := norm t₁ gas
      let t₂' := norm t₂ gas

      if t₁ == t₂ ∨ t₁' == t₂' then
        pure t₁
      else
        mismatch t₁ t₂

  match e with
  | K' m n => return K'.type m n
  | I m    => return I.type m
  | Srt m  => return Srt.type m
  | quot e => (quot.type · e) <$> infer e
  | Syntax t => do match ← norm <$> infer t with
    | (Srt m) => return Syntax.type t m
    | t => not_type t
  | app f x => do match ← (norm ⸨· (quot x)⸩) <$> infer f, ← norm <$> infer x with
    | Π' α, β, α₂ =>
      let _ ← defeq α α₂
      return norm β
    | t, _ => not_fn t
  | t => .error <| "not well-typed: " ++ (format t)

#eval infer (quot (Srt 1))
#eval infer ⸨(I 2) (Srt 1) (Srt 0)⸩
#eval infer ⸨(SynConst (Srt 1) (Srt 1) 2 2) (quot (Srt 0)) (quot (Srt 0))⸩
#eval infer ⸨(K' 2 2) (Srt 1) (Srt 1) (Srt 0) (Srt 0)⸩
#eval infer ⸨(K 3 2) (Srt 2) ⸨(I 3) (Srt 2)⸩ (Srt 1) (Srt 0)⸩

end Expr
