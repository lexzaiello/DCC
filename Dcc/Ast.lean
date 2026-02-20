import Mathlib.Data.Nat.Notation
import Init.Meta.Defs

/-
Note: the fall design pattern will probably come up a lot.
It might be good to reuse the pattern for multiple macros.

So, ∀(x : α, y : β, ...)

The list substitution mechanism is mildly secondary
to ∀ itself.

∀ just generalizes the notion of debruijn indices.
It does a mild amonut of bookkeeping to track indices.
Also nice to have utility methods readily accessible.

We might be able to simplify our implementation significantly.

we should always be popping items off the stack for book-keeping purposes.
make methods for these.

Some notes on well-typing in ∀.

Hardest parts are internal consistency:
- we should assume in ∀ that substitutions ALWAYS produce valid
judgments.

Then, we can look up the domain type in the context,
and infer the output type at that cell to be Prop.

The tail cell is not as easy to guess, though.

We had to cheat on this one last time, which I didn't like.

HOWEVER, this becomes a lot simpler if we assume that contexts produce valid Props / judgments
in EVERY cell.
Then, no biggie at all.

This is what we will do.

My other question is if we can make our debruijn encoding easier to understand.

Previous version was honestly working very well.
We ought just stick with it.

HOWEVER, this becomes even more interesting when we pair in the idea
of substituted trees.

Then, we can separate applications within the context itself.

This is convenient, and lets us glue things back together nicely.

Another approach to debruijn:

- we have all the items in the context
- we know ahead of time
- we can just build up huge nested K chains. ezpz.

My intuition is to say it's ugly but it honestly might not be.

- attempt normie debruijn
- get working on cracked out tree substitution ideas
- another idea is a "lazy" plan of how you would substitute,
but without actually doing it

- the other insight is that the context will contain connections too.
however, we will get them substituted in eventually, so not an issue.

- also note: we don't have to introspect into app. we can make
something better. something based on lists.

list codomains should not mention ourselves.
ideally, we should output a term representing the final type, but which is
well-typed via judgment.

The x component is the codomain.

Or, we could just literally put anything in the term component
and encode the codomain via the type. doesn't really matter. just interpretation.

However, to do that, we would need to produce a well-typed function.

If we implicitly accepted ourselves in our type, this would solve the issue,
but it isn't very elegant.

The most pragmatic approach is to output a judgment whose term
corresponds to the codomain type.
-/

open Std Format
open Lean (Macro)
open Lean (MacroM)
open Lean (Syntax)

abbrev Level := ℕ

  /-
  JUICE TO SAVE FOR LATER
  | `(at⟪⟨($a:atom : ($α:atom : Type $m:atom))
    , ($b:atom : ($β:atom : Type $n:atom))⟩⟫) =>
    `(a⟪mkcons (I.[at⟪$m:atom⟫] (($α:atom : Type $m) → $α:atom))
      (I.[at⟪$m:atom⟫] $α:atom)
      (I.[at⟪$n:atom⟫] $β:atom) $a:atom $b:atom⟫)
  -/

/-
I'm fairly certain you can derive fst and snd from the new generalized cons.
-/

inductive Expr where
  | I       : Level → Expr
  | K       : Level → Level → Expr -- Dependent K
  | K'      : Level → Level → Expr -- Nondependent K
  | S       : Level → Level → Level → Expr -- Dependent S
  | mkcons  : Expr
  -- ^ (mkcons πcons πf πg f g x) = (πcons πf πg (πf f x) (πg g x))
  | judge  : Level  → Expr -- judge t is a freestanding expr
  /-
    Sorts:
  -/
  | type   : Level → Expr
  | prop   : Expr
  | sort   : Level → Expr
  | fst    : Level → Expr
  | snd    : Level → Expr
  /-
    Sigma projection:
    TODO: we will need explicit type arguments here of some kind.
  -/
  | app    : Expr → Expr → Expr
deriving BEq

open Expr

declare_syntax_cat expr
declare_syntax_cat atom
declare_syntax_cat sort
declare_syntax_cat app
declare_syntax_cat judgment
declare_syntax_cat arrow
declare_syntax_cat cons
declare_syntax_cat fall

syntax "#(" term ")"  : atom

syntax num            : atom
syntax ident          : atom

syntax "Type" term   : sort
syntax "Sort" term   : sort
syntax "Prop"        : sort

syntax:50 atom ":" atom : judgment

syntax "∀" "(" judgment,* ")"             : fall
syntax fall "," "::(" atom,* ")"          : fall
syntax "::(" atom "," atom,* ")"          : cons
--          ^ this argument stores the config
-- of the sigma. specifically projection

syntax atom "→" atom              : arrow

syntax sort                       : atom
syntax  "(" expr ")"              : atom
syntax ":" term                   : atom

-- assignments are always well-typed judgment
-- with an assigned value.
-- these are not core to the language,
-- but rather derived from operational semantics of cons.

syntax app atom : app
syntax atom     : app

syntax app          : expr
syntax judgment     : expr
syntax cons         : expr
syntax fall         : expr
syntax arrow        : expr

syntax (name := expr) "⟪" expr "⟫"  : term
syntax (name := mapp) "a⟪" app "⟫"          : term

def parse_sort : Lean.Macro
  | `(⟪Type $n:term⟫) => `(Expr.type $n:term)
  | `(⟪Sort $n:term⟫) => `(Expr.sort $n:term)
  | `(⟪Prop⟫) => `(Expr.prop)
  | _ => Macro.throwUnsupported

def compute_sort (s : Syntax) : Lean.MacroM (Lean.TSyntax `term) :=
  match s with
  | `(expr| Prop) => `(0)
  | `(expr| Type $m:term) => `(1 + $m:term)
  | `(expr| Sort $m:term) => `($m:term)
  | _ => Macro.throwUnsupported

-- If this variable is contained in vars, then look up the corresponding debruijn index
-- otherwise, insert the variable

-- debruijn index 0 corresponds to rejecting all future inputs
-- for the head
-- 1 corresponds to accepting the input
-- all others decrement from n to 1
-- this assumes that α is well-tyepd as a Type
-- default behavior of the second component is that it will accept the next argument.
def mk_debruijn (n₁ : ℕ) (n₂ : Option ℕ := .none) : Lean.MacroM (Lean.TSyntax `app) := do
  /-
    If we are at indxe 1, we will accept the argument. Otherwise, we will reject it.
  -/
  let mk_fetch (n : ℕ) : Lean.MacroM (Lean.TSyntax `app) :=
    if n == 1 then
      `(app| (I 0) Prop) -- only once we've hit debruijn index one we accept the argument
    else

      `(app| (K 0 0) Prop Prop)

  let advance (inner : Lean.TSyntax `app) : Lean.MacroM (Lean.TSyntax `app) := do
    let map_f ← mk_fetch n₁
    let map_g ← (mk_fetch <$> n₂).getD `(app| #(I 0) Prop)
    -- if we don't care where substitutions get sent,
    -- e.g., if we are not the very tail of the list,
    -- we can usually leave n₂ alone.

    `(app| #(Expr.mkcons) ($inner:app) ($map_f:app) ($map_g:app))

  match n₁ with
    | .succ n₁ =>
      match n₂ with
      | .some (.succ n₂) =>
        mk_debruijn n₁ n₂ >>= advance
      | .some .zero =>
        mk_debruijn n₁ (.some .zero) >>= advance
      | .none =>
        mk_debruijn n₁ .none >>= advance
    | .zero =>
      match n₂ with
      | .some (.succ n₂) => do
        mk_debruijn .zero n₂ >>= advance
      | .some .zero => do `(app| #(Expr.mkcons) (#(K' 0 0) Prop Prop) (#(K' 0 0) Prop Prop))
      | .none => `(app| #(Expr.mkcons) (#(K' 0 0) Prop Prop) (#(I 0) Prop))

/-
Use this to figure out which variables an element in the list is using.
-/
def allOuterIdents (base_vars : List (Lean.TSyntax `ident)) (e : Lean.TSyntax `app) : List (Lean.TSyntax `ident) :=
  match base_vars with
  | .nil => .nil
  | (.cons x' xs) =>
    match e with
    | `(app| $f:app $x:ident) =>
      if x' == x then (x :: allOuterIdents xs f) else []
    | `(app| $f:atom $x:ident) => if x' == x then [x] else []
    | _ => []

def fall.pop (f : Syntax) : MacroM Syntax := do
  match f with
  | `(fall| ∀($_j₁:judgment, $tail:judgment,*)) =>`(fall| ∀($tail:judgment,*))
  | _ => Macro.throwUnsupported

def fall.infer (e : Lean.TSyntax `atom) : MacroM (Option (Lean.Term)) :=
  match e with
  | `(sort| Type $m:term) => `(⟪Type 1 + $m⟫)
  | `(sort| Sort $m:term) => `(⟪Sort 1 + $m⟫)
  | `(sort| Prop) => `(⟪Type 0⟫)
  | `(arrow| $_α:atom → ($_β:atom : Type $m)) => `(⟪Type $m⟫)
  -- forall substitutions are guaranteed
  -- to produce judgment propositions.
  -- as a result, an entire forall is a proposition.
  | `(fall| ∀($_jd:judgment,*), ::($_a:atom,*)) => `(⟪Prop⟫)
  | _ => Macro.throwUnsupported

def fall.sort_of (e : Lean.TSyntax `atom) : MacroM (Option Lean.Term) := do
  match e with
  | `(sort| Type $m:ident) => `($m - 1)
  | `(sort| Sort $m:ident) => `($m)
  | `(sort| Prop) => `(Option.some 0)
  | `(sort| Type $m:num) => `(Option.some ($m - 1))
  | `(sort| Sort $m:num) => `($m)
  | `(arrow| $_α:atom → ($_β:atom : Type $m:term)) => `($m:term)
  -- forall substitutions are guaranteed
  -- to produce judgment propositions.
  -- as a result, an entire forall is a proposition.
  | `(expr| ∀($_jd:judgment,*), ::($_a:atom,*)) => `(0)
  | _ => Macro.throwUnsupported

def fall.unwrap {α : Type} : Option α → MacroM α
  | .some x => return x
  | .none => Macro.throwUnsupported

def fall.type_of (ident : Lean.TSyntax `ident) (f : Syntax) : MacroM (Option (Lean.TSyntax `atom)) := do
  match f with
  | `(fall| ∀($j:judgment,*)) =>
    let elem ← unwrap <| ← j.getElems.toList.findM? (fun (j : Lean.TSyntax `judgment) => match j with
      | `(judgment| $var:ident : $_ty:atom) => pure <| var == ident
      | _ => pure false)
    match elem with
    | `(judgment| $_var:ident : $ty₁:atom) => pure ty₁
    | _ => pure <| .none
  | _ => Macro.throwUnsupported

/-
Note: this is offset by one.
1 corresponds to accepting an argument, while zero corresponds
to rejecting all further arguments.
-/
def fall.debruijn_idx_of (ident : Lean.TSyntax `ident) (f : Syntax) : MacroM (Option ℕ) := do
  match f with
  | `(fall| ∀($j:judgment,*)) =>
    pure <| Nat.succ <$> j.getElems.toList.findIdx? (fun (e : Lean.TSyntax `judgment) => match e with
      | `(judgment| $var:ident : $_ty:atom) => var == ident
      | _ => false)
  | _ => Macro.throwUnsupported

/-
Note: this will underflow to a score of zero to prevent arguments from being
substituted in if the user has not substituteda  variable anywhere.
-/
def fall.idx_of' (a : Lean.TSyntax `atom) (f : Syntax) : MacroM ℕ := do
  match a with
  | `(atom| ($var:ident))
  | `(atom| ($_fn:atom $var:ident))
  | `(atom| ($_fn:app $var:ident)) =>
    pure <| (← fall.debruijn_idx_of var f).getD 0
  | _ => pure 0

/-
We ideally want to register the function the user intends to substitute.
If the user only specifies a "variable," then we us the I combinator.
-/
def fall.fn_of (a : Lean.TSyntax `atom) (f : Syntax) : MacroM (Lean.TSyntax `atom) := do
  match a with
  | `(atom| ($fn:atom $_var:ident)) => pure <| fn
  | `(atom| $var:ident) =>
    let α ← unwrap <| ← fall.type_of var f
    match ← unwrap <| ← fall.infer α with
    | `(⟪Type $m:term⟫) => `(atom| (#(I $m:term) $α))
    | _ => Macro.throwUnsupported
  | e => pure e

/-
(∀(x : α, y : β), ::(f x, g y)) x y
= ::(f x, g y)
-/
def parse_fall (f : Syntax) : MacroM Syntax := do
  match f with
  | `(⟪∀($judgs:judgment,*), ::($h₁:atom, $h₂:atom)⟫) => do
    -- calculate debruijn indices for either, if they have them.
    -- zero is a reasonable default if not, since they would just reject the argument
    let ctx ← `(fall| ∀($judgs:judgment,*))

    let fn₁ ← fall.fn_of h₁ ctx
    let fn₂ ← fall.fn_of h₂ ctx

    let idx₁ ← fall.idx_of' h₁ ctx
    let idx₂ ← fall.idx_of' h₂ ctx

    let mycons ← mk_debruijn idx₁ (.some idx₂)
    `(⟪$mycons:app $fn₁:atom $fn₂:atom⟫)
  | `(⟪∀($judgs:judgment,*), ::($_cfg:atom, $h₁:atom, $hrst:atom,*)⟫) => do
    let ctx ← `(fall| ∀($judgs:judgment,*))
    let rst' ← `(⟪$ctx:fall, ::($_cfg:atom, $hrst:atom,*)⟫)

    let fn₁ ← fall.fn_of h₁ ctx
    let idx₁ ← fall.idx_of' h₁ ctx

    let mycons ← mk_debruijn idx₁ .none
    `(⟪$mycons:app $fn₁:atom #($rst')⟫)
  | _ => Macro.throwUnsupported

def parse_atom (s : Syntax) : MacroM Syntax :=
  match s with
  | `(⟪$n:num⟫) => `($n)
  | `(⟪#($t:term)⟫) => `($t)
  | `(⟪$id:ident⟫) =>`($id:ident)
  | `(⟪: $m:term⟫) => `(Expr.judge $m:term)
  | _ => Macro.throwUnsupported

def parse_cons : Lean.Macro
  -- carry the configuration settings
  -- down the cons. these
  -- are required by mkcons.
  | `(⟪::((::($πcons:atom, $πf:atom, $πg:atom)), $x:atom, $y:atom)⟫) =>
    `(⟪#(Expr.mkcons) $πcons:atom $πf:atom $πg:atom $x:atom $y:atom⟫)
  | `(⟪::((::($πcons:atom, $πf:atom, $πg:atom)), $x:atom, $args:atom,*)⟫) =>
    `(⟪#(Expr.mkcons) $πcons:atom $πf:atom $πg:atom $x:atom (::((::($πcons:atom, $πf:atom, $πg:atom)), $args:atom,*))⟫)
  | _ => Macro.throwUnsupported

/-
β isn't necessarily a terminal form.
β could be chain in an intermediate step.
-/

def parse_arrow : Lean.Macro
  | `(arrow| ($α:atom : Type $m:term) → ($β:atom : Type $n:term)) =>
    `(expr| ∀(x : $α), ::(((: $m:term) $α x), ((: ($n:term + 1)) (Type $n:term) $β)))
  | `(arrow| $α:atom → $β:atom) => do
    let m ← compute_sort α
    let n ← compute_sort β
    `(expr| ($α:atom : Type #($m)) → ($β:atom : Type #($n)))
  | _ => Macro.throwUnsupported

@[macro app] def parse_app : Lean.Macro
  | `(

@[macro expr] def parse_expr : Lean.Macro
  | s@`(⟪$_s:sort⟫) => parse_sort s
  | s@`(⟪$_s:atom⟫) => parse_atom s
  | s@`(⟪$_s:arrow⟫) => parse_arrow s
  | s@`(⟪$_s:cons⟫) => parse_cons s
  | s@`(⟪$_s:fall⟫) => parse_fall s
  | `(⟪$x:atom $y:atom⟫) => `(Expr.app ⟪$x:atom⟫ ⟪$y:atom⟫)
  | `(⟪$x:atom $xs:atom,*⟫) => `(Expr.app ⟪$x:atom⟫ ⟪$y:atom⟫)
  | `(⟪$x:atom $xs:atom,*⟫) => do
    xs.getElems.toList.foldlM (fun acc e => `(Expr.app $acc $e)) (← `(⟪$x:atom⟫))
  | _ => Macro.throwUnsupported
  /-| `(⟪∀$_vars:judgment,*, ::($concl:atom,*)⟫)
  | `(⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(⟪$srt:sort⟫) => `(srt⟪$srt:sort⟫)
  | `(⟪$e:app⟫) => `(a⟪$e:app⟫)
  | `(⟪$a:app $b:atom⟫) => `(Expr.app a⟪$a:app⟫ at⟪$b:atom⟫)
  | `(⟪$s:sort⟫) => `(srt⟪$s:sort⟫)
  | `(⟪$a:atom⟫) => `(at⟪$a:atom⟫)
  | `(⟪($α:atom : Type $m) → $β:atom⟫) => do
    let myId ← Lean.withFreshMacroScope (pure <| Lean.mkIdent `my_x)
    `(⟪∀($myId:ident : $α:atom) [((: $m) $α:atom $myId:ident), $β:atom]⟫)
  | `(⟪$α:atom → $β:atom⟫) => do
    let myId ← Lean.withFreshMacroScope (pure <| Lean.mkIdent `my_x)

    `(⟪∀($myId:ident : $α:atom) [((: sortof <| $α:atom) $α:atom $myId:ident), $β:atom]⟫)
  | _ => Macro.throwUnsupported-/

#eval ⟪#(Expr.mkcons)⟫

#eval ⟪∀(x : α), ::(((I 1) x), (#(I 1) x))⟫
