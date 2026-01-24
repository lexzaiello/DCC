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


-/
