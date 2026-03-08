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
  | unquot : red ⸨(unquot α) (quot e)⸩ e
  | left   : red f f' → red ⸨f x⸩ ⸨f' x⸩
  | right  : red x x' → red ⸨f x⸩ ⸨f x'⸩

abbrev SynId := Syntax.id
abbrev SynConst := Syntax.const

abbrev Syntax.id' := Syntax.id ?_ 1
abbrev Syntax.const' := Syntax.const ?_ ?_ 1 1

abbrev unquot? := (unquot ?_)

def mk_arrow (α β : Expr) : Expr :=
  ⸨(into (Π' (head (head unquot?)), (head (tail unquot?)))) (quot ⸨α β⸩)⸩

syntax term "~>" term : term
macro_rules
  | `($α ~> $β) => `(mk_arrow $α $β)

/-
Types for quotation combinators
-/
abbrev Syntax.type (_t : Expr) (m : Level) := (Srt m)

abbrev quot.type (α _e : Expr) := (Syntax α)

abbrev Pi.type : Expr → Expr := id

abbrev app'.type (_f x : Expr) (α γ : Expr) :=
  Π' α
   , $ (γ, 0 (unquot α), $ (x, 0 (unquot α)))

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
  ⸨(K' m.succ.succ m.succ) (Srt m.succ) (Syntax ?_) (Srt m)⸩

abbrev α_to_sort (m n : Level) : Expr :=
  into (Π' (head (head (unquot (Srt m))))
       , ⸨(K' n.succ.succ 1) (Srt n.succ) ?_ (Srt n)⸩)

abbrev I.type (m : Level) : Expr :=
    Π' (α_sort m)
  , into (Π' (head unquot?)
  , (head unquot?))

abbrev K'.type (m n : Level) : Expr :=
    Π' (α_sort m)
  , into (Π' ⸨(K' n.succ.succ 1) (Srt n.succ) (Syntax ?_) (Srt n)⸩
  , into (Π' (head (head unquot?))
  , into (Π' (head (head (tail unquot?))), (head (head (head unquot?))))))

abbrev K.type (m n : Level) : Expr :=
    Π' (α_sort m)
  , into (Π' (α_to_sort m n)
  , into (Π' (head (head unquot?))
  , into (Π' ($ ((head (head (tail unquot?))), (head (tail unquot?))))
  , (head (head (head unquot?))))))

abbrev γ (o : Level) : Expr :=
    into (Π' (head (head (head unquot?)))
  , into (Π' $ (head (head (head (tail unquot?))), head (tail unquot?))
  , ⸨(K' o.succ.succ 1) (Srt o.succ) (Syntax ?_) (Srt o)⸩))

abbrev x : Expr :=
    into (Π' (head (head (head (head unquot?))))
  , into (Π' $ (head (head (head (head (tail unquot?)))), head (tail unquot?))
  , $ (head (head (tail unquot?)), head (head (tail unquot?))
          , ($ ((head (tail unquot?)), tail unquot?)))))

abbrev y : Expr :=
    into (Π' (head (head (head (head (head unquot?)))))
  , $ (head (head (head (head (head (tail unquot?))))), head (tail unquot?)))

abbrev S.type (m n o : Level) : Expr :=
    Π' (α_sort m)
  , into (Π' (α_to_sort m n)
  , into (Π' (γ o)
  , into (Π' x
  , into (Π' y
  , into (Π' (head (head (head (head (tail unquot?)))))
  , $ (head (head (tail unquot?)), (tail unquot?)
          , ($ ((head (tail unquot?)), tail unquot?))))))))

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
  | ⸨(into fn) (quot f) (quot x)⸩ =>
    (eval ⸨fn (quot ⸨f x⸩)⸩) <|> pure ⸨fn (quot ⸨f x⸩)⸩
  | ⸨(Π' α, β) x⸩ => return Π' ⸨α x⸩, ⸨β x⸩
  | ⸨(head fn) (quot ⸨f _x⸩)⸩ => eval ⸨fn (quot f)⸩ <|> pure ⸨fn (quot f)⸩
  | ⸨(tail fn) (quot ⸨_f x⸩)⸩ => eval ⸨fn (quot x)⸩ <|> pure ⸨fn (quot x)⸩
  | ⸨$ (f, x) e⸩ => (do return ⸨(← ⸨f e⸩.eval) (← ⸨x e⸩.eval)⸩) <|>
     (do return ⸨(← ⸨f e⸩.eval) ⸨x e⸩⸩) <|>
     (do return ⸨⸨f e⸩ (← ⸨x e⸩.eval)⸩) <|>
     (do return ⸨⸨f e⸩ ⸨x e⸩⸩) -- this is fine, since ($ can infer what kind of Syntax α
  | ⸨(unquot _α) (quot e)⸩ => eval e <|> (pure e)
  | ⸨f x⸩ => (do return ⸨(← f.eval) (← x.eval)⸩) <|> ((·.app x) <$> (f.eval)) <|> (f.app <$> (x.eval))
  | e => .error <| "stuck: " ++ (format e)

def norm (e : Expr) (gas : ℕ := 100) : Expr :=
  match gas with
    | .zero => e
    | .succ n => norm ((eval e).toOption.getD e) n

partial def infer (e : Expr) : Except Format Expr := do
  let not_type (t : Expr) := Except.error <| "not a type: " ++ (format t)
  let not_fn (t f app : Expr) := Except.error <| "not a function type: " ++ (format t) ++ .line ++ "for: " ++ (format f) ++ .line ++ "in app: " ++ (format app)
  let mismatch (expected actual : Expr) := .error <| (format expected) ++ " ≠ " ++ (format actual)

  let rec defeq (t₁ : Expr) (t₂ : Expr) (gas : ℕ := 100) : Except Format Expr :=
    match gas, norm t₁, norm t₂ with
    | _, ?_, t₁ | _, t₁, ?_ => pure t₁
    | .succ n, t₁@⸨(into _f) _a⸩, t₂
    | .succ n, t₁, t₂@⸨(into _f) _a⸩ =>
      defeq (norm ⸨t₁ (quot ?_)⸩) (norm ⸨t₂ (quot ?_)⸩) n
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
  | Π' _α, β => infer ⸨β (quot ?_)⸩
  | S m n o => return S.type m n o
  | K' m n => return K'.type m n
  | K m n => return K.type m n
  | I m    => return I.type m
  | Srt m  => return Srt.type m
  | head fn => infer fn
  | tail fn => infer fn
  | unquot α => pure (Syntax α ~> α)
  | ?_ => return ?_
  | into f => do match ← (norm ⸨· (quot ⸨?_ ?_⸩)⸩) <$> infer f with
    | t' => return (Syntax ?_ ~> (Syntax ?_ ~> t'))
  | ⸨(into f) (quot a)⸩ => do match ← (norm ⸨· (quot ⸨a ?_⸩)⸩) <$> infer f with
    | t' => return (Syntax ?_ ~> t')
  | quot e => (quot.type · e) <$> infer e <|> (pure (quot.type ?_ e))
  | Syntax t => do match ← norm <$> infer t with
    | (Srt m) => return Syntax.type t m
    | t => not_type t
  | app f x => do match ← (norm ⸨· (quot x)⸩) <$> infer f, ← norm <$> infer x with
    | Π' α, β, α₂ =>
      let _ ← defeq α α₂
      return norm β
    | t, _ => not_fn t f (app f x)
  | t => .error <| "not well-typed: " ++ (format t)

def mk_I (α : Expr) (m : Level) : Expr :=
  let α := α
  let y := ⸨(K' 2 m) (Srt 1) α (Srt 0)⸩
  let x := ⸨(K' m 2) α (Srt 1)⸩

  let β := ⸨(K' 3 m) (Srt 2) α (Srt 1)⸩
  dbg_trace format ((Srt 2) ~> (Srt m.succ))
  let γ := ⸨(K' m.succ.succ m) ((Srt 2) ~> (Srt m.succ)) α ⸨(K' m.succ 2) (Srt m) (Srt 1) α⸩⸩

  ⸨(S m 2 m) α β γ x y⸩

#eval infer ⸨(into (Π' (head (head (unquot ?_))), (head (tail (unquot ?_))))) (quot ⸨(Srt 2) (Srt 3)⸩)⸩
#eval infer (⸨(unquot (Srt 1)) (quot (Srt 0))⸩)
#eval infer <| mk_I (Srt 1) 2

#eval infer (quot (Srt 1))
#eval infer ⸨(I 2) (Srt 1) (Srt 0)⸩
#eval infer ⸨(SynConst (Srt 1) (Srt 1) 2 2) (quot (Srt 0)) (quot (Srt 0))⸩
#eval infer ⸨(K' 2 2) (Srt 1) (Srt 1) (Srt 0) (Srt 0)⸩
#eval infer ⸨(K 3 2) (Srt 2) ⸨(I 3) (Srt 2)⸩ (Srt 1) (Srt 0)⸩

#eval infer (head (tail (unquot ?_)))

#eval format <$> infer (Srt 0 ~> Srt 0)

end Expr
