/-
Sigma types feel almost like application.

if you think about it, it feels kinda suboptimal to be doing the order this way.

:: (x : α) (xs : ∀ (x : α), β x)

this is literally reversed application.
x is the argument, xs is the function.

id : ∀ (α : Type), α → α

:: (α : Type) id
:: x (:: α id)
this doesn't really solve the currying issue.

apply : ∀ (α : Type) (β : α → Type) : ∀ (l : ((∀ (x : α), β x) × α)), l.fst l.snd

apply : ∀ (l : ((α : Type) × (β (α : Type) (β : α → Type) (l : ((x : α) × (f : β x))), β l.fst

(:: (x : α) (xs : β x)) : ((x : α) × β x)

what is the purpose of apply?
apply ((x : α) × β x) into just β x

(:: (x : α) (

observations:
- we would like to use fully uncurried positional arguments. this makes making the types a BREEZE.

id : ∀ (x : α)

we are being imprecise with how we write ×.

× α β represents the entirety of ((x : α) × β x)

the type of id α x is ::[(Ty m), α, α]

this is

t_id α x = ::[(α : (Ty m)), ::[both, ::[id, Ty m], ::[id, Ty m]]]

so wait what?
projection gives us the values?

(t_id α x).snd = ::[α, α]
but then here, α wants to depend on α again, which is fine.

t_id α x = ::[:: id m.succ Ty m, ::[id m.succ, Ty m], ::[id m.succ, Ty m]]

what happens to x?

id.{[m]} : ::[:: id m.succ Ty m, ::[id m.succ, Ty m], ::[id m.succ, Ty m]]
nil at the end closes the loop?

::[x, α, ::[:: id m.succ Ty m, ::[id m.succ, Ty m], ::[id m.succ, Ty m]]]

there is an extra α here.

- sigma cons seems like absurdly powerful.

but what about checking (α : Ty m)?

(::[α, ::[::[id m.succ, Ty m], ::[id m.succ, Ty m]]]).snd

.snd kind of normalizes, since it turns ((x : α) × (β x)) into just β x. it's normalization.

snd is application.

so, snd gives us like the output type. this is fine for the α → α part.
but then what about x?

nil feels like we can change it a bit.
it downgrades us from a term to a type.

nil.{[m]} α : α → (Ty m)
nil α x = α

::[x, α, ::[

.snd.fst gives us the "assertion" for the given argument.
.snd.snd gives us the return type.

nil.{[m.succ]} (Ty m)

::[(α : Ty m), ::[nil.{[m.succ]} (Ty m), ::[nil.{[m]}, ::[id m.succ, Ty m]]]

::[nil.{[m.succ]} (Ty m), ::[nil.{[m]}, ::[id m.succ, Ty m]]
nil.{[m]} α x = α
::[α, ::[id m.succ, Ty m]]

::[α, ::[nil.{[m.succ]} (Ty m), ::[nil.{[m]}, ::[id m.succ, Ty m]]]]

::[nil.{[m.succ]} (Ty m) α = Ty m, ::[nil.{[m]}, ::[id m.succ, Ty m]]]

::[x, (::[nil.{[m.succ]} (Ty m) α = Ty m, ::[nil.{[m]}, ::[id m.succ, Ty m]]]).snd]

::[x, ::[nil.{[m]}, ::[id m.succ, Ty m]]

if the head becomes

::[α, ::[

nil.{[3]} (Ty 2) : (Ty 2) → (Ty 3)
feels like we should have to duplicate α somehow.

but xs : β x.
to check α, we want to downgrade to Ty m.
but then β x can bring us back out somehow.

so we need some way to simultaneously downgrade α to Ty m and pass it on.

we need to remember α.
we can potentially make it more dependent just for this use case

t.fst x gives the input type
snd gets acces to the Ty m part and the α part.

::[(α : Ty m), (? : Ty m)]

so the entire type is dependent on (α : Ty m)
it feels like we need some duplication mechanism.
I think we're capping and nil actually works like we think it does.

nil downgrades a term to its type, pretty much.

if all of ? is dependnet on α..
we can make the head extra dependent, so
?.fst : ∀ (x : α)

how exactly does nested "normalization" of lists look like?

::[x, ::[y, z]]

z depends on y, which depends on x, is how I would read this.

((x : α) × (yz : tyz x))
how is this not circular, then?

nested normalization of lists requires some finagling.

::[y, z] needs to depend on x, but it is a sigma (⨯' α β)
I mean the obvious answer is:

::[x, ::[y, z]].snd -> ::[::[x, y], z]

::[y, x] is not normalized yet, though.
it's just a pair.

so

id α x
(::[α, t_id].snd.fst.fst gives us the normalized value, which we can use to check α
::[α, ::[

(id m) : ::[nil.{[m.succ]} (Ty m), ::[nil.{[m]}, ::[id m.succ, Ty m]]]

(::[α, ::[nil.{[m.succ]} (Ty m), ::[nil.{[m]}, ::[id m.succ, Ty m]]]]).snd
= ::[::[α, nil.{[m.succ]} (Ty m)], ::[nil.{[m]}, ::[id m.succ, Ty m]]]

(::[::[α, nil.{[m.succ]} (Ty m)], ::[nil.{[m]}, ::[id m.succ, Ty m]]]).fst.snd
= Ty m, due to nil eval rule. this checks that α : Ty m, as it should in first arugment position to id.

(::[::[α, nil.{[m.succ]} (Ty m)], ::[nil.{[m]}, ::[id m.succ, Ty m]]]).snd
should give us the return type, which should be something we can apply x to like this:

::[x, t_out_α_call].fst.snd = α
::[x, t_out_α_call].snd = α

::[x, ::[::[α, nil.{[m]}], Prod.snd]].snd

we can make nil not work with lists or work differently to make this work don't worry about that.

::[x, ::[α, nil.{[m]}]].snd = α

id m : ::[

? = ::[nil.{[m.succ]} (Ty m)

::[α, ::[

(id m) : t_id = ::[::[(Ty m), nil.{[m.succ]}], Prod.fst]

::[α, t_id].snd.fst = ::[α, ::[(Ty m), nil.{[m.succ]}]] = Ty m. this checks (α : Ty m)

::[α, ::[::[(Ty m), nil.{[m.succ]}], Prod.fst]].snd.snd
= ::[::[α, (Ty m), nil.{[m.succ]}], Prod.fst].snd = α

so now we need to make this work with the x argument.

we literally just prepend α to nil.{[m]}

nil.{[m]} ∘ Prod.fst

::[x, ::[α, nil.{[m]}]].snd = α

(id m) : t_id = ::[::[(Ty m), nil.{[m.succ]}], ((id.{[m.succ]} Ty m) ∘ (nil.{[m]} ∘ Prod.fst))]

::[α, t_id].snd.fst.snd = ::[α, Ty m, nil.{[m.succ]}].snd = Ty m
::[α, t_id].snd.snd = ((id.{[m.succ]} Ty m) ∘ ((nil.{[m]} ∘ Prod.fst))) ::[α, Ty m, nil.{[m.succ]}]
  = ::[α, nil.{[m]}]

::[x, ::[::[α, nil.{[m]}], (id.{[m.succ]} (Ty m))].snd.fst.snd
= ::[x, α, nil.{[m]}].snd
= α

::[x, ::[::[α, nil.{[m]}], (id.{[m.succ]} (Ty m))].snd.snd
= ::[::[x, α, nil.{[m]}] (id.{[m.succ]} (Ty m))]
= α
-/
