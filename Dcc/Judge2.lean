import Dcc.Ast2
import Dcc.Eval2
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation

/-
Λ(Λ(?))

assume for assoc we have just args in scope

a b c

Λ(dpair a) b c
= (a, (b, c))

Λ(

App(Λ(x)y, z) = x(y, z)

oh wait we can put Λ inside the list?

((a, b), c)

Λ(id) Λ(dpair) ((a, b), c)

= (Λ(dpair), ((a, b), c))

(x ∘ y) z = x (y z)
(dpair a) ∘ (dpair b) c = (a, (b, c))

(App ∘ ⟨(App ∘ ⟨comp ∘ dpair, dpair⟩), id⟩) ((a, b), c)
=
App (⟨(App ∘ ⟨comp ∘ dpair, dpair⟩), id⟩ ((a, b), c)
= App (((dpair a) ∘ (dpair b)), c)
= ((dpair a) ∘ dpair b) c
= (dpair a) ((dpair b) c)
= (a, (b, c))
-/
def assoc : Expr :=
  (SK (App ∘ ⟨App ∘ ⟨comp ∘ pair, pair⟩, id⟩))

def assoc_couple : Expr :=
  (SK (⟨id, ⟨id, id⟩⟩ ∘ assoc))

#eval Std.format <| (SK ((⟨App ∘ ⟨comp ∘ pair, pair⟩, id⟩ ((Sort 0, Sort 1), Sort 2)))).reduce
#eval Std.format <| (SK (#(assoc) ((Sort 0, Sort 1), Sort 2))).reduce

/-
Pi types are advance by:
(α, β)
appending to the environment:
((nil, α), x)
and applying to β:
β ((nil, α), x)

Pi judgments:

similar process to before. essentially a fold.

TODO:
- judging Π
- K, K', S types

Π judge is basically a fold.

JudgePi has two cases: init (α, β), step ⟨α, β⟩

(α, β)

would be cool if we could do JudgePi with just a rewrite rule...

(α, β)
(β (α, __ : α))

since we have pairs and couples, we ought to type them explicitly.

(α, β) is just the type of β, I think.

I'm going to be lazy for now, maybe.

K' type:

id = Λ(snd)

_e has in scope α, then β
so we can do Λ
Λ(⟨I,

β gets mapped to
swap, basically

is my order right? (α, β)

Λ(?) α β = ?(α, β)

definitely need some way to swap, probably. don't think we can derive it as is.
as is blowing up a little bit.

we will need nil delimeters, I think.

? =

fst / snd feel somewhat sus as is.

_e receives (α, β)

need to make (β, quot α)

(Sort m, ⟨quot (Sort n), _e

we can use nil for this, I think.
nil x = x

β receives (Sort m, α)

for β

Λ(β_actual) env x = β_actual (env, x)

can use this to shuffle context down, I think.
challenge is, of course, duplication, except we will receive the arg anyway.
we won't receive α, though.

⟨fst _, snd _⟩

so all pairs need to have this.

how do we pass along the environment?
we will need α twice.

Λ(x)y, z = x (y, z)

Λ(⟨id, ?⟩) (Sort n) α = (Sort n, α)

? = Λ(id)

for this we can rearrange, I think?

α and β as args.

? α β = (α, β)

we need some way to retain α.

this is kinda like RAII.

β will receive x, but that's it.

we don't want x though.

can use something instead of a couple.

should probably include α in the context as well, I think.
then the issue is solved.

this is some kind of operations.

β α x.

size is not guaranteed to decrease here.

we want the entire context to shuffle around.

we can just tack α in as well.

we're just including everything we produced so far and everything we consumed so far.

this is giving rust vibes.
we end the scope with everything we had in context, do stuff with them.

dpair (Sort n)

K' : (Sort m, Λ(⟨quot Sort n, ⟨id, ⟨id, fst⟩ ∘ snd⟩⟩))

? receives α, Sort n, and β

? = ⟨id, ?⟩

snd ∘ ? receives β, α, and x

? = ⟨id, fst⟩

map_α_β receives α, Sort n, and β

map_α_β = ⟨id, map_β_α ∘ snd⟩

map_β_α receives β, α, and x

K' : (Sort m,
  Λ(⟨quot Sort n
  -- α in scope, then Sort n, then β
  -- grab α and β
  , Λ(⟨id
    -- β, then α, then x in scope
    -- make (β, α), then done
    -- Λ(id) ∘ snd β 
    , quot ∘ Λ(⟨id, quot⟩)⟩)⟩)
-/

/-
(flip ∘ (Λ(id) (quot Sort n))) -- make β : α → Sort n. (α, quot Sort n)

mk_β_ty := (flip ∘ (Λ(id) (quot Sort n)))

grab α from (α → Type): fst

we will also have in scope Sort n and β

then for y type, 

(Sort m, (quot (Λ(⟨fst, mk_β_ty)

this is where ac might be useful.

in scope as args: β then α then x.

App(Λ(x)y, z) = x(y, z)

⟨β, quot⟩ (x, α)

want to make (β x, quot α)

just need to flip (x, α)

(

Λ(flip ∘ ⟨quot, β⟩)

⟨quot, β⟩ ∘ Λ(id)

Λ(Λ(?))

? has in scope ((β, α), x)

then do

⟨flip, id⟩ ((β, α), x) = ((α, β), x)

flip ∘ ⟨flip, id⟩ ((β, α), x) = (x, (α, β))

⟨id,

β then α then x in scope

(flip ∘ Λ(⟨id, β⟩)) α x = ⟨β x, α⟩

flip ∘ ⟨id, β⟩ ∘ (Λ(⟨id, id⟩))

(comp flip) ∘ ((App ∘ flip ∘ (Λ(id) Λ(⟨id, id⟩)) ∘ comp)) ∘ (dpair id)

(comp flip) ∘ (App ∘ flip ∘ (Λ(id) Λ(⟨id, id⟩)) ∘ comp) ∘ (dpair id) β
= (comp flip) ∘ (App ∘ flip ∘ (Λ(id) Λ(⟨id, id⟩)) ∘ comp) ⟨id, β⟩
= (comp flip) ∘ (App ∘flip (Λ(⟨id, id⟩), comp ⟨id, β⟩))
= (comp flip) ∘ (App (comp ⟨id, β⟩, Λ(⟨id, id⟩)))
= (comp flip) ∘ (⟨id, β⟩ ∘ Λ(⟨id, id⟩))

(comp flip) ∘ (⟨id, β⟩ ∘ Λ(⟨id, id⟩)) α x
= (Λ(⟨id, id⟩) α)

β α and x

Λ(Λ(?))

receive ((β, α), x)

? = flip ∘ ⟨⟨?, quot⟩, id⟩

((β, quot α), x)

want to turn into (quot α, (β x))

? gets ((β, α), x)

App ((β, α), x) = (β, α) x



() ∘ flip ∘ (dpair quot)

also need app I guess.

K : (Sort m, a)

a receives Sort m, α

want to get rid of Sort m, replace with sort n

a = ⟨(quot 
-/

def K.type (m n : Level) : Expr :=
  let α_ty := (SK Sort m)
  -- make α → Sort n from scope: Sort m, α. get rid of Sort m first
  let β_ty := (SK (quot (flip ∘ (Λ(id) (quot Sort n)))))
  -- with (α → Sort n), β in scope
  -- make x : α type with fst ∘ fst
  -- (y : β x) will have in scope β, α, and x
  --
  let x_βx_ty := (SK Λ(⟨
    fst, -- (x : α)
    -- β in scope here, then α, then x. want to make (y : β x), and quot α at the end
    -- can do this with ⟨β, quot (quot α)⟩
    
    Λ(Λ(
  sorry

def K'.type (m n : Level) : Expr :=
  SK (Sort m,
  Λ(⟨(quot Sort n)
  -- α in scope, then Sort n, then β
  -- grab α and β
  , Λ(⟨id
    -- β, then α, then x in scope
    -- make (β, α), then done
    -- Λ(id) ∘ snd β
    , quot ∘ Λ(⟨id, quot⟩)⟩)⟩))

def S.type (m n o : Level) : Expr :=
  sorry

inductive Judge : Expr → Expr → Prop
  | k    : Judge (K.type m n) (SK K.{[m, n]})
  | k'   : Judge (K'.type m n) (SK K'.{[m, n]})
  | s    : Judge (S.type m n o) (SK S.{[m, n, o]})
  | srt  : Judge (SK Sort m.succ) (SK Sort m)
  | app  : Judge (SK (α, β)) f
    → Judge α x
    → Judge (SK (β x)) (SK (f x))
  | coup : Judge (SK Sort 1) (SK (α, β))
  | pair : Judge (SK Sort 1) (SK ⟨α, β⟩)
  | conv  {α β : Expr} : Judge α x → α.RedTyTrans β → Expr.IsNorm β → Judge β x
