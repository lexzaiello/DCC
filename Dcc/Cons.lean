import Mathlib.Data.Nat.Notation
import Init.Meta.Defs

open Std Format

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

declare_syntax_cat expr

syntax "__"                                   : expr
syntax ident                                  : expr
syntax ident "[" term,* "]"                   : expr
syntax "(" expr+ ")"                          : expr
syntax "::[" expr,+ "]"                       : expr
syntax "::(" expr,* ")"                       : expr
syntax "::(" expr,* ")" "{" expr,+ "}" : expr
syntax "∶" expr                               : expr
syntax "#" term                               : expr
-- ^ for making judgments: (x : (α : Ty m))
-- ^ for mimicking variables
syntax "Π'"       : expr
syntax "Ty" term  : expr
syntax "Srt" term : expr
syntax "Prp"      : expr

declare_syntax_cat judgment
syntax expr "∶" expr    : judgment
syntax "(" judgment ")" : judgment

syntax "snd(" expr ")" : expr
syntax "fst(" expr ")" : expr

declare_syntax_cat substitution

syntax expr "⟦" judgment ":=" "*" "⟧"  : substitution
syntax expr "⟦" judgment ":=" expr "⟧" : substitution
syntax "(" substitution ")"    : substitution
syntax substitution "∶" judgment   : substitution

syntax "j(" judgment ")" : expr
syntax "s(" substitution ")" : expr

syntax "⟪" expr "⟫" : term
syntax "s{{" substitution "}}" : term
syntax "j{{" judgment "}}" : term

macro_rules
  | `(⟪j($j:judgment)⟫) => `(j{{$j}})
  | `(⟪s($s:substitution)⟫) => `(s{{$s}})
  | `(s{{($s:substitution)}}) => `(s{{$s}})
  | `(⟪$comb:ident[$univ:term,*]⟫) => `($comb $univ*)
  | `(⟪$id:ident⟫) => `($id)
  | `(⟪#$e:term⟫) => `($e)
  | `(⟪($e:expr)⟫) => `(⟪$e:expr⟫)
  | `(⟪ ($f:expr $args:expr*) ⟫) => do
    let mut res ← `(⟪$f⟫)
    for arg in args do
      res ← `(Expr.app $res ⟪$arg⟫)
    return res
  | `(⟪::[ $x:expr ]⟫) => `(⟪$x⟫)
  | `(⟪::[ $x:expr, $xs:expr,* ]⟫) => `(Expr.uncons ⟪$x⟫ ⟪::[$xs,*]⟫)
  | `(⟪::($πcons:expr, $πf:expr, $πg:expr)⟫) => `(⟪(Expr.mkcons $πcons $πf $πg)⟫)
  | `(⟪::($πcons:expr, $πf:expr, $πg:expr){$elems:expr,*}⟫) => do
    match elems.getElems.toList.reverse with
    | .cons x xs =>
      xs.foldrM (fun e acc => do `(expr| (::($πcons, $πf, $πg) $e ($acc:expr)))) x
        >>= (fun e => `(⟪$e⟫))
    | .nil => `(sorry)
  | `(⟪∶ $α:expr⟫) => `(judge ⟪$α⟫)
  | `(j{{($j)}}) => `(j{{$j}})
  | `(j{{$x:expr ∶ $α:expr}}) => `(⟪(∶ $α $x)⟫)
  | `(⟪snd(j($e:judgment))⟫) => `(match j{{$e}} with
    | j{{α ∶ β}} => β
    | e => e)
  | `(⟪fst(j($e:judgment))⟫) => `(match j{{$e}} with
    | j{{α ∶ β}} => α
    | e => e)
  | `(⟪fst(::[$x, $_xs])⟫) => `(⟪$x⟫)
  | `(⟪snd(::[$_x, $xs])⟫) => `(⟪$xs⟫)
  | `(⟪fst(::($_a, $_b, $_c){$x, $_xs})⟫) => `(⟪$x⟫)
  | `(⟪snd(::($_a, $_b, $_c){$_x, $xs})⟫) => `(⟪$xs⟫)
  | `(⟪Ty $m⟫) => `(Expr.type $m)
  | `(⟪Srt $m⟫) => `(Expr.sort $m)
  | `(⟪Prp⟫) => `(Expr.prop)

def mk_arrow (f α β : Expr) : Expr :=
  ⟪::[(∶ α), ::[snd, f, (∶ β)]]⟫

syntax expr "->" expr : expr

macro_rules
  | `(j{{$f:expr ∶ $α:expr -> $β:expr}}) =>
    `(j{{$f:expr ∶ (# (mk_arrow ⟪$f⟫ ⟪$α⟫ ⟪$β⟫))}})
  | `(j{{$α:expr -> Ty $m ∶ __}}) =>
    `(j{{$α:expr -> Ty $m ∶ Ty (Nat.succ $m)}})
  | `(j{{$α:expr -> Srt $m ∶ __}}) =>
    `(j{{$α:expr -> Srt $m ∶ Ty $m}})
  | `(j{{$α:expr -> Prp ∶ __}}) =>
    `(j{{$α:expr -> Prp ∶ Ty 0}})
  | `(j{{$f:expr ∶ ($α:expr -> $β:expr ∶ Ty $m)}}) =>
    `(j{{$f:expr ∶ ((# (mk_arrow ⟪$f⟫ ⟪$α⟫ ⟪$β⟫)) ∶ Ty $m)}})

#eval j{{(I[0] (Ty 0)) ∶ ((Ty 0) -> (Ty 0) ∶ Ty 1)}}

/-
Note: this assumes f composes with g.
It also assumes that the tail has already been debruijn-ified.

This also assumes that the head will compose with the tail.
That is, that the tail will then receive the head.
This is an implicit context.

Note that this will always induce substitution into the tail element.
This can only handle "variables" in the head position.

Every head position must select a variable. It is then piped into the
head function.

the debruijn index 0 indicates that we reject all arguments.
the debruijn index 1 indicates that we accept the arugment.

Note: we should be able to infer α from t_f

Problem is, now we can't easily match against t_f.

we can't match α, since

we should assume α is a judgment (∶ α)

This also assumes that β is the fully substituted
type of the substituted variable.
-/
def mk_debruijn (α β γ : Expr) (m o : Level) (idx : ℕ) : Expr :=
  let n := match α with
  | ⟪((∶ _a) _b)⟫ => 0
  | ⟪Ty n⟫ => n
  | ⟪Prp⟫ => 0
  | _ => m -- TODO: fix

  let t_f := j{{mkcons ∶ (α -> β ∶ Ty n)}}
  let t_g := j{{mkcons ∶ (α -> γ ∶ Ty o)}}

  /-
    The 0th de bruijn index, we should have an expression
    of the codomain type β.
    Since further arguments won't have determined types,
    since we should not substitute further arguments,
    we will defer to Prop.
  -/

  match idx with
  | 0 => ⟪::(mkcons, (K'[m, n] α Prp), (I[o] t_g))⟫ -- should be substituted here
  -- at 0, reject the next argument, output f, then reject forever.
  | 1 => ⟪::((# (mk_debruijn α β γ m o 0)), (I[m] t_f), (I[o] t_g))⟫
  -- at 1, accept the argument, then proceed to reject.
  | .succ (.succ idx) => ⟪::((# (mk_debruijn α β γ m o (.succ idx)))
    , (K'[m, n] t_f α)
    , (I[o] t_g))⟫

syntax "::{" substitution,+ "}" : expr

#eval ⟪::(K'[1, 2], K'[3, 4], K'[5, 6]){K'[7, 8], K'[9, 10], K'[11, 12], K'[13, 14]}⟫

macro_rules
  | `(⟪::{$f:expr⟦__ ∶ ($α:expr ∶ Ty $m) := #$idx⟧ ∶ ($β:expr ∶ Ty $_n₁)
    , $g:expr⟦$_j:judgment := *⟧ ∶ ($γ:expr ∶ Ty $n₂)}⟫) =>
    `(⟪((#mk_debruijn ⟪$α⟫ ⟪$β⟫ ⟪$γ⟫ $m $n₂ $idx) $f $g)⟫)
  | `(⟪::{$f:expr⟦__ ∶ ($α:expr ∶ Ty $m) := #$idx⟧ ∶ ($β:expr ∶ Ty $_n₁)
    , $g:expr⟦$_j:judgment := #$idx₂⟧ ∶ ($γ:expr ∶ Ty $n₂), $rst,*}⟫) =>
    `(⟪((#mk_debruijn ⟪$α⟫ ⟪$β⟫ ⟪$γ⟫ $m $n₂ $idx) $f ::{$g:expr⟦$_j:judgment := #$idx₂⟧ ∶ ($γ:expr ∶ Ty $n₂), $rst,*})⟫)

def Expr.toFormat : Expr → Std.Format
  | ⟪K[m, n]⟫ => "K[" ++ (joinSep [m, n] ", ") ++"]"
  | ⟪K'[m, n]⟫ => "K'[" ++ (joinSep [m, n] ", ") ++ "]"
  | ⟪S[m, n, o]⟫ => "S[" ++ (joinSep [m, n, o] ", ") ++ "]"
  | ⟪I[m]⟫ => s!"I[{m}]"
  | ⟪::(πc, πf, πg){f, g}⟫ =>
    "::(" ++
      (.group <| .nest 2 <| joinSep [πc.toFormat, πf.toFormat, πg.toFormat] ", ")
      ++ ")"
      ++ "{" ++ (.group <| .nest 2 <| joinSep [f.toFormat, g.toFormat] ", ") ++ "}"
  | ⟪Ty m⟫ => s!"Ty {m}"
  | ⟪Srt m⟫ => s!"Srt {m}"
  | ⟪Prp⟫ => s!"Prp"
  | ⟪snd[]⟫ => "snd"
  | ⟪fst[]⟫ => "fst"
  | ⟪j(x ∶ t)⟫ => .paren <| .group <| .nest 2 <| x.toFormat ++ " ∶ " ++ t.toFormat
  | ⟪(∶ T)⟫ => s!"∶ {T.toFormat}"
  | ⟪::[x, xs]⟫ => s!"::[{x.toFormat}, {xs.toFormat}]"
  | ⟪mkcons⟫ => "mkcons"
  | ⟪(a b)⟫ => .paren <| .group <| .nest 2 <| a.toFormat ++ .line ++ b.toFormat
  | _ => ""

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨fun e => s!"{e.toFormat}"⟩

inductive IsStep : Expr → Expr → Prop
  | chain  : IsStep ⟪(::[f, g] x)⟫ ⟪::[f, (g x)]⟫
  | mkcons : IsStep ⟪(::(πc, πf, πg){f, g} x)⟫ ⟪(πc πf πg (πf f x) (πg g x))⟫
  | i      : IsStep ⟪(I[m] α x)⟫ x
  | k      : IsStep ⟪(K[m, n] α β x y)⟫ x
  | k'     : IsStep ⟪(K'[m, n] α β x y)⟫ x
  | s      : IsStep ⟪(S[m, n, o] α β γ x y z)⟫ ⟪((x z) (y z))⟫
  | fst    : IsStep ⟪(fst ::[f, g])⟫ f
  | snd    : IsStep ⟪(snd ::[f, g])⟫ g
  | fst'   : IsStep ⟪(fst ::(_a, _b, _c){f, g})⟫ f
  | snd'   : IsStep ⟪(snd ::(_a, _b, _c){f, g})⟫ g
  | fstj   : IsStep ⟪(fst ((∶ α) β))⟫ α
  | sndj   : IsStep ⟪(fst ((∶ α) β))⟫ β
  | left   : IsStep f f' → IsStep ⟪(f x)⟫ ⟪(f' x)⟫
  | right  : IsStep x x' → IsStep ⟪(f x)⟫ ⟪(f x')⟫

inductive DefEq : Expr → Expr → Prop
  | refl    : DefEq a a
  | symm    : DefEq e e'  → DefEq e' e
  | step    : IsStep e e' → DefEq e e'
  | trans   : DefEq e₁ e₂ → DefEq e₂ e₃ → DefEq e₁ e₃
  | left    : DefEq f f'  → DefEq ⟪(f x)⟫ ⟪(f' x)⟫
  | right   : DefEq x x'  → DefEq ⟪(f x)⟫ ⟪(f x')⟫
  | cons    : DefEq x x'  → DefEq xs xs' → DefEq ⟪::[x, xs]⟫ ⟪::[x', xs']⟫
  | judge   : DefEq α β   → DefEq ⟪((∶ α) x)⟫ ⟪((∶ β) x)⟫
  | srt     : DefEq ⟪Srt m⟫ ⟪Ty (m.succ)⟫
  | prp     : DefEq ⟪Srt 0⟫ ⟪Prp⟫


#eval j{{(I[1] (Ty 0)) ∶ ((Ty 0) -> (Ty 0) ∶ Ty 1)}}

#eval j{{(I[1] (Ty 0)) ∶ ((Ty 0) -> (Ty 0) ∶ Ty 1)}}

#eval ⟪::{
  (I[1] (Ty 0))⟦__ ∶ ((Ty 0) ∶ Ty 1) := #1⟧ ∶ ((Ty 0) ∶ Ty 1)
  , (I[1] (Ty 0))⟦__ ∶ ((Ty 0) ∶ Ty 1) := *⟧ ∶ ((Ty 0) ∶ Ty 1)}⟫

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
  | ty    : ValidJudgment ⟪Ty m.succ⟫ ⟪Ty m⟫
  | prp   : ValidJudgment ⟪Ty 0⟫ ⟪Prp⟫
  | app   : ValidJudgment t f
    → ValidJudgment ⟪(fst (fst (t x)))⟫ x
     -- ^ (∷ (∶ P f) (∶ Q g)), P is a predicate. the predicate that x is typed at...
      -- Q will just produce a type
    → ValidJudgment ⟪(snd (t x))⟫ ⟪(f x)⟫
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

example : ((π₁ : Expr) × (π₂ : Expr) × (DefEq ⟪(::{
  (I[1] (Ty 0))⟦__ ∶ ((Ty 0) ∶ Ty 1) := #1⟧ ∶ ((Ty 0) ∶ Ty 1)
  , (I[1] (Ty 0))⟦__ ∶ ((Ty 0) ∶ Ty 1) := *⟧ ∶ ((Ty 0) ∶ Ty 1)} Prp)⟫
  ⟪::(mkcons
    , π₁
    , π₂){Prp, Prp}⟫)) := by
  simp [mk_debruijn]
  defeq trans, step
  step mkcons
  defeq trans, left, step
  step mkcons
  
  rfl
