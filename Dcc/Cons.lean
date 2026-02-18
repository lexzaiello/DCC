import Mathlib.Data.Nat.Notation
import Init.Meta.Defs

/-
This version of the SK project uses cons substitution / composition.

::[f, g] x = ::[f(x), g(f(x))].

We also use judgment objects (∶ T x). Judgment objects are freestanding expressions
through T. (∶ T) : Expr.

Function applications are represented
by substitution lists producing type judgments for each argument applied.
We also produce a judgment for the entire application.

f : α → β ≃ ::[(∶ α), ::[snd, f, (∶ β)]]

See this is what I would like: a spot marker that says "this is the next spot to insert
into."

::[_, b] x = ::[x, b]

There is literally no reason we couldn't do this. We would just have to be really smart about it.

We're basically pushing every substitution we're going to need, then popping them off.

All we have to do is make _ typed.

we have _ and we have un _.

In our macro, we will assume everything is prefixed by un_ unless otherwise specified.

_ is extremely powerful.

Our macros will prefix everything else by un_, at least up until the _. After the _, everything stays the same.

_ = hole.

_ x = x.

This is literally just the identity combinator.

::[consta, _] x = ::[un_ consta, x]

seal / hole.

::[seal consta, hole] x = ::[consta, x]

hole x = x
seal consta = consta.

the OTHER thing we could do is change cons entirely to be cons / uncons.

uncons just passes the argument down the chain until we hit the next cons.

By combining these two, you can mimick substitution.

Can we avoid the judgment object using this system?

Plug is REALLY REALLY nice.

__ x = x
(plug x) y = x

I will also leave uncons for now.

We should compare plug and hole against different kinds of cons.

we could have different shapes of cons.

| subst  : IsStep ⸨::(f, g) x⸩ ::(⸨f x⸩, ⸨g ⸨f x⸩⸩)
| chain  : IsStep ⸨::[f, g] x⸩ ::(f, ⸨g x⸩)
| app    : IsStep ⸨

hole and plug feel really really elegant.

My question is, how can we encode a universal shape cons?

we get a (mk_cons head tail) as an argument, and we get f and g as arguments.
Then use S and K to bootstrap the list?

Then, make this into a reduction rule?

This implies, unfortunately, that cons is a combinator.

(cons πf πg f g) x = cons πf πg

What if we want to swap the cons part itself?

Also we can make πf and πg fixed.
This will give us our types in validjudgment.

(cons πcons πf πg) f g x = (πcons πf πg x) (πf f x) (πg g x)

First question: can we derive ::(f, g) x = ::(f(x), g(x))?

::(πc, πf, πg){f, g}

Can we derive debruijn indices with ::(πc, πf, πg){f, g}?

For this one, we compose. Assume 0 indicates that the head and
tail positions get substituted.

mk_debruijn 0 f g = ::(mkcons, I α, I β){f, g}

debruijn index 1 or anything greater than zero is just nesting K's.
mk_debruijn n.succ f g = ::(mk_debruijn n, K' t_f α f, I β){f, g}

We still haven't exactly figured out what the type of lists will be.
We will figure it out, I think.
-/

abbrev Level := ℕ

inductive Expr where
  | I      : Level → Expr
  | K      : Level → Level → Expr -- Dependent K
  | K'     : Level → Level → Expr -- Nondependent K
  | S      : Level → Level → Level → Expr -- Dependent S
  | mkcons : Expr -- (mkcons πcons πf πg) f g x = πcons πf πg ⸨πf f x⸩ ⸨πg g x⸩
  | cons   : Expr  → Expr  → Expr -- not a combinator. just a freestanding expr.
  | uncons : Expr  → Expr  → Expr -- not a combinator. just a freestanding expr.
  -- uncons is the opposite of cons. it does not substitute into its components,
  -- but rather passes the value on to the next cons.
  -- TODO: will probably remove these in favor of mkcons
  | plug   : Expr → Expr -- (plug x) y = x
  | hole   : Expr -- __ x = x
  | judge  : Expr  → Expr -- judge t is a freestanding expr
  | type   : Level → Expr
  | prop   : Expr
  | sort   : Level → Expr
  | fst    : Expr
  | snd    : Expr
  | app    : Expr → Expr → Expr

open Expr

syntax "⸨" term+ "⸩"                          : term
syntax "::(" term,+ ")"                       : term
syntax "::[" term,+ "]"                       : term
syntax "::(" term "," term "," term ")" "{" term,+ "}" : term
syntax "(" term "∶" term ")"                  : term
syntax "∶" term                               : term
syntax "#" term                               : term
-- ^ for making judgments: (x : (α : Ty m))

notation "Π'" => Expr.Pi
notation "Ty" => Expr.type
notation "Srt" => Expr.sort
notation "Prp" => Expr.prop
notation "__" => Expr.hole

macro_rules
  | `(#$n) => `(($n : Nat))
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f $x)
  | `(⸨ $f $x:term $args:term*⸩) => `(⸨ (Expr.app $f $x) $args*⸩)
  | `(::[ $x:term ]) => `($x)
  | `(::[ $x:term, $xs:term,* ]) => `(Expr.uncons $x ::[$xs,*])
  | `(::( $x:term )) => `($x)
  | `(::( $x:term, $xs:term,* )) => `(Expr.cons $x ::($xs,*))
  | `(::($_πcons, $_πf, $_πg){$x:term}) => `($x)
  | `(::($πcons, $πf, $πg){$x:term, $xs:term,*}) =>
    `(⸨Expr.mkcons $πcons $πf $πg $x ::($πcons, $πf, $πg){$xs,*}⸩)
  | `(($x ∶ $α)) => `(⸨(judge $α) $x⸩)
  | `(∶ $α) => `(judge $α)

def mk_arrow (f α β : Expr) : Expr :=
  ::[(∶ α), ::[snd, f, (∶ β)]]

/-
Note: this assumes f composes with g.
It also assumes that the tail has already been debruijn-ified.

This also assumes that the head will compose with the tail.
That is, that the tail will then receive the head.
This is an implicit context.

So, given α and β for f, 
-/
def mk_debruijn (t_f t_g α : Expr) (m n o : Level) (idx : ℕ) : Expr :=
  match idx with
  | 0 => ⸨mkcons mkcons ⸨(I m) t_f⸩ ⸨(I n) t_g⸩⸩
  | .succ idx => ⸨mkcons (mk_debruijn t_f t_g α m n o idx) ⸨(K' m o) t_f α⸩ ⸨(I n) t_f⸩⸩

syntax "::{" (term "∶" term),+ "}" : term

macro_rules
  | `(::{$e ∶ $_α}) => `($e)
  | `(::{#$idx ∶ ($α ∶ Ty $m), $g ∶ ($tg ∶ Ty $n), $[$ks:term ∶ $vs:term],* }) =>
    `(⸨(mk_debruijn (mk_arrow ⸨(I $m) $α⸩ $α $α) $tg $α $m $n $m $(Lean.quote idx))
      ⸨(I $m) $α⸩
      ($tail ∶ ($tg ∶ Ty $n))⸩)
  | `(::{#$idx ∶ ($α ∶ Ty $m), $[$ks:term ∶ $vs:term],* }) =>
    `(⸨(mk_debruijn (mk_arrow ⸨(I $m) $α⸩ $α $α) $tg $α $m $n $m $(Lean.quote idx))
      ⸨(I $m) $α⸩
      ($tail ∶ ($tg ∶ Ty $n))⸩)
    sorry

notation "__" => ⸨(I 0) Prp⸩

inductive IsStep : Expr → Expr → Prop
  | subst  : IsStep ⸨::(f, g) x⸩ ::(⸨f x⸩, ⸨g ⸨f x⸩⸩)
  | chain  : IsStep ⸨::[f, g] x⸩ ::(f, ⸨g x⸩)
  | mkcons : IsStep ⸨::(πc, πf, πg){f, g} x⸩ ⸨πc πf πg ⸨πf f x⸩ ⸨πg g x⸩⸩
  | plug   : IsStep ⸨(plug x) y⸩ x
  | i      : IsStep ⸨(I m) α x⸩ x
  | k      : IsStep ⸨(K m n) α β x y⸩ x
  | k'     : IsStep ⸨(K' m n) α β x y⸩ x
  | s      : IsStep ⸨(S m n o) α β γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | fst    : IsStep ⸨fst ::(f, g)⸩ f
  | snd    : IsStep ⸨snd ::(f, g)⸩ g
  | fstj   : IsStep ⸨fst (f ∶ (α ∶ Ty m))⸩ f
  | sndj   : IsStep ⸨snd (f ∶ (α ∶ Ty m))⸩ α
  | left   : IsStep f f' → IsStep ⸨f x⸩ ⸨f' x⸩
  | right  : IsStep x x' → IsStep ⸨f x⸩ ⸨f x'⸩

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | symm    : DefEq e e'  → DefEq e' e
  | step    : IsStep e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⸨f x⸩ ⸨f' x⸩
  | right   : DefEq x x'  → DefEq ⸨f x⸩ ⸨f x'⸩
  | cons    : DefEq x x'  → DefEq xs xs' → DefEq ::[x, xs] ::[x', xs']
  | judge   : DefEq α β   → DefEq (x ∶ α) (x ∶ β)
  | srt     : DefEq (Srt m) (Ty (m.succ))
  | prp     : DefEq (Srt 0) Prp

example : DefEq ::((#0 ∶ (Prp ∶ Ty 0)), (⸨(I 1) (Ty 0)⸩ ∶ ((mk_arrow (Ty 0) (Ty 0)) ∶ (Ty 1)))) = sorry := by
  rfl

/-
S m n o : ∀ (α : Type m) (β : α → Type n) (γ : ∀ (x : α), β x → Type o)
  (f : ∀ (x : α) (y : β x), γ x y)
  (g : ∀ (x : α), β x)
  (z : α), γ x (g x)

snd (∶ (Ty m) α) = α
S m n o : ::((∶ (Ty m)), ::(::(
-/
def S.type (m n o : Level) : Expr :=
  
  sorry


inductive ValidJudgment : Expr → Expr → Prop
  | ty    : ValidJudgment (Ty m.succ) (Ty m)
  | prp   : ValidJudgment (Ty 0) Prp
  | app   : ValidJudgment t f
    → ValidJudgment ⸨fst ⸨fst ⸨t x⸩⸩⸩ x
     -- ^ (∷ (∶ P f) (∶ Q g)), P is a predicate. the predicate that x is typed at...
      -- Q will just produce a type
    → ValidJudgment ⸨snd ⸨t x⸩⸩ ⸨f x⸩
  | defeq : ValidJudgment α x
    → DefEq α β
    → ValidJudgment β x

syntax "defeq" ident,*        : tactic
syntax "step" ident,*         : tactic
syntax "judge" ident,*        : tactic

macro_rules
  | `(tactic| defeq $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `DefEq name.getId.toString)
      `(tactic| apply $nm))))

    `(tactic| $[$nms];*)
  | `(tactic| step $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `IsStep name.getId.toString)
      `(tactic| apply $nm))))

    `(tactic| $[$nms];*)
  | `(tactic| judge $fn:ident,*) => do
    let nms : Array (Lean.TSyntax `tactic) ← (Array.mk <$> (fn.getElems.toList.mapM (fun name =>
      let nm := Lean.mkIdent (Lean.Name.mkStr `ValidJudgment name.getId.toString)
      `(tactic| apply $nm))))

    `(tactic| $[$nms];*)
