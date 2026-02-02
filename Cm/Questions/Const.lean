import Cm.Questions.PiBetterBoth

namespace old_const

/-
Dependent K.

K : ∀ (α : Type) (β : α → Type) (x : α) (y : β x), α
-/

def const.type.just_α : Expr :=
  ::[::[fst_postfix, snd_postfix] -- ::[α, β] doesn't get flipped
    , Expr.cons] -- flip to ::[x, ::[α, β]]. then snd, fst to get α

-- with ::[::[α, β], x] in scope. ::[x, ::[α, β]]
def const.type.β_arrow : Expr :=
  mk_arrow_pointfree just_α
    ($ const, (Prod Ty ($ nil, Ty)), ::[snd_postfix, Expr.cons])

def const.type : Expr :=
  let β_arrow := const.type.β_arrow

  -- for α, β in scope, we need to make a pi binder, but without substituting
  -- pi application (Pi t_in t_out map_ctx) x causes x to be pushed to map_ctx
  -- so, if ::[α, β] is in scope, we can apply t_in_arrow ::[α, β].
  -- we should use cons as our map_ctx
  (Pi -- α in scope
    ($ nil, Ty) -- first argument is of type Ty
    (Pi -- ::[α, β] in scope.
      β_arrow -- β : α → Type 
      (Pi
        const.type.just_α
        (Pi
          sorry
          --const.type.y_type
          sorry
          sorry)
        Expr.cons) -- with ::[::[α, β], x] in scope
      Expr.cons)
    ($ id, Ty))

end old_const

namespace old_const'

/-
α : Type
β x : Type
β we assume to be a list operation
on the context ::[α, x]

β : Prod (Prod Ty ($ id, Ty)) ($ const', Ty, (Prod Ty ($ id, Ty)), Ty)

x : α
y : β x
out: α

so we need to track α, β, and x

β has in scope ::[α, β]
::[α, β] : 
-/
def const.type.β.type : Expr :=
  Prod (Prod Ty ($ id, Ty)) ($ const', Ty, (Prod Ty ($ id, Ty)), Ty)

def const.type.α.type : Expr := Ty

def const.type.αβ.type : Expr :=
  Prod const.type.α.type ($ const', Ty, Ty, const.type.β.type)

-- ::[::[α, β], x]
def const.type.αβx.type : Expr :=
  Prod const.type.αβ.type ::[(snd_postfix ($ const', Ty, const.type.β.type, Ty) const.type.β.type), Expr.cons]

/-
  with ::[::[α, β], x] in scope.
  both f = α
  g = β

  we want β ::[α, x]
  x = ::[::[α, β], x]

  f = ::[::[snd_postfix, snd_postfix], Expr.cons]
  f x = β

  g = both αβx.type _ _ ::[::[fst_postfix, snd_postfix], Expr.cons] ::[fst_postfix, Expr.cons]
  g x = ::[α, x]
  g[f] = ::[::[fst_postfix, snd_postfix], Expr.cons]

  α = αβx.type
  f = ::[::[snd_postfix, snd_postfix], Expr.cons]

  (f x = β : β!)

  β! = ($ const', Ty, Ty, β.type)

  ::[::[fst_postfix, snd_postfix], Expr.cons] ::[::[α, β], x]
  = α

  ::[α, β] ($ const', _, _, Expr.cons)
  = cons α

  ::[($ const', _, _, Expr.cons), Expr.cons] ::[::[α, β], x]
  = ::[::[α, β], x] Expr.cons ($ const', _, _, Expr.cons)
  = Expr.cons x ::[α, β] ($ const', _, _, Expr.cons)
  = ::[x, ::[α, β]] ($ const', _, _, Expr.cons)
  = ($ const', _, _, Expr.cons) ::[α, β] x

  = ($ const', _, _, Expr.cons) ::[α, β] x
  = ($ const', _, _, Expr.cons)

  ::[($ const', _, _, Expr.cons), Expr.cons] ::[α, β]
  = ::[α, β] Expr.cons ($ const', _, _, Expr.cons)
  = Expr.cons β α ($ const', _, _, Expr.cons)
  = ::[β, α] ($ const', _, _, Expr.cons)
  = ($ const', _, _, Expr.cons) α β
  = Expr.cons β

  both ::[::[::[::[αβx.type, 

  both 
-/
def const.type.y_type : Expr :=
  let α := const.type.αβx.type

  -- β receives ::[s_α, x]
  -- (g x) = ::[α, x], as in OUR α and x
  let β := ($ const', Ty, (Prod α, ($ id, Ty)), (Prod const.type.α.type ($ id, Ty)))
  let g := ($ both, ::[αβx.type, _ _ ::[::[fst_postfix, snd_postfix], Expr.cons] ::[fst_postfix, Expr.cons]

  -- f ::[::[α, β], x] = β
  -- γ receives ::[::[α, x]
  let f := ::[::[snd_postfix, snd_postfix], Expr.cons]
  -- t_f receives ::[α, (x : α)], outputs β.type
  let t_f := ($ const', Ty, (Prod Ty ($ id, Ty)), β.type)

  -- g ::[::[α, β], x] = β = ::[α, x]
  -- γ receives ::[::[::[α, x], β], ($ β, ::[α, x])]
  -- β receives ::[α, x]
  -- α is just 
  let g := 

  sorry

/-
y : (β ::[α, x])
entire context: ::[::[α, β], x]

smart way to do this:
both _ _ _  ::[::[snd_postfix, snd_postfix], Expr.cons] ??
               ^ this grabs β
??

::[x, cons] ::[(flip cons), α]
= ::[(flip cons), α] cons x
= cons α ((flip cons)) x
= ::[α, ((flip cons))] x
= ((flip cons)) x α
= ::[α, x]

flip ::[a, b] = ::[b, a]

flip = ::[id _, Expr.cons]

::[Expr.cons, Expr.cons] ::[a, b] = ::[a, b] Expr.cons id _
= Expr.cons b a (id _)
= ::[b, a] (id _)
= (id _) a b


-/
def const.type.αβxy.type : Expr :=
  --Prod const.type.αβx.type
  sorry

def const.type : Expr :=
  (Pi
    ($ nil, const.type.α.type)
    (Pi
      ($ const', const.type.αβ.type, Ty, const.type.β.type)
      (Pi -- ::[::[α, β], x] in scope
        ::[fst_postfix' const.type.α.type const.type.β.type, Expr.cons] -- (x : α)
        (Pi -- ::[::[::[α, β], x], y] in scope
          sorry
          sorry
          sorry)
      Expr.cons) -- ::[::[α, β], x]
      Expr.cons) -- make ::[α, β]
    ($ id, Ty))

end old_const'
