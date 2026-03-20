import Dcc.Ast
import Dcc.Eval

/-
We might end up with more nested Π, even if we substitute.

Outside in.

B (Π α, etc..)

This gives B a type.

And the size strictly decreases, since the number of TyCombs decreases.
But how do we duplicate? we have no mechanism for this.
Π was this mechanism.

W could do this.

W could do this, but then we need a decreasing measure.
Or, we could literally require all the type combinators to have arguments.

All TyComb.

I  : TyComb
K* :

Now it literally is equational.

W copies into both

we need a decreasing measure for Π itself.

C is not necessary. Ever.

K' : ∀ (α : Type) (β : Type), α → β → α

W duplicates the Π.

Outside in. Outside in.

K' : ∀ (α : Type) (β : Type), α → β → α

B (K* Type) (W

context

fn ctx

W fn (

size of fn strictly decreasing.

Composition is the only thing that chains. Others are atoms.

W Π α = Π α, α

Ways to insert:

I Π α = Π α α

We can have literally whatever we want as our combinators if we can show decreasing.

Size of the program fn decreases

fn

Core combinators:
W, I, B, K*

Always have a Π shape filled in.

Π Sort m, Sort n, for example

fn (Π α, β) ctx

I (Π α, β) x
= (Π x, x)

need to distinguish left from right.

e.g.,

I_term : I (Π Sort m, Sort m) α
= Π α, α

K* (Π α, β) x
= Π α, β

Il (Π α, β) x
= Π x, β

Ir (Π α, β) x
= Π α, x

K* (Π α, β) x
= Π α, β

W (Π α, β) x

(W fn) (Π α, β) x y
= fn (Π α, β) x y x

B better for composition

B f g (Π α, β) x
= f (g (Π α, β) x)

Elements: B, K*, Il, Ir (is W necessary?)

K' :

(Π Type, Type)

I (Π Type, Type) x
= Π Type, x

K'.{[m, n]} : I (Π (Sort m), (Sort n))

(I (Π (Sort m), (Sort n))) α
= Π (Sort n), α

K'.{[m, n]} : B I I (Π (Sort m), (Sort n))

B I I (Π (Sort m), (Sort n)) α
= I (Π (Sort n), α)

I (Π (Sort n), α) β

= Π α, β

K* shifts up.

I just inserts.

W duplicates in some unknown way.

We can probably even have C. B = sesquence. decrease.

K* (Π α, β)

= β

I (Π α, β)
= Π α, β

W (Π α, β) x

= (Π α x, β x)

K* (Π α, β) x
= Π α, β

I (Π α, β) x
= Π α, x

C (Π α, β) x
= Π x, β

- I (Π α, β) x = Π α, x
- C (Π α, β) x = Π x, β
- W (Π α, β) x = Π x, x
- B f g (Π α, β) x =
- f (g (Π α, β) x)



I'm tweaking, we can maybe just use S' and K'.

K* (Π α, β) x
= (Π α, β)

W f (Π α β) x
f (Π (α x) (β x))

K* f (Π α β) x
f (Π α β)

I (Π α, β) x
= Π α, α

(W f) (Π α, β) x
= f (Π (α x), (β x))

(B f g) (Π α β) x
= f (g (Π α β) x)
-/

inductive Expr.PiSize : Expr → ℕ → Prop
  | pi : 

inductive Expr.RedPi : Expr → Expr → Prop
  | step : Expr.RedTy (SK (f x)) x'
    
    → Expr.RedPi (SK ((f (Π α, β)) x)) (SK 

def Expr.pi_size : Expr → Option ℕ
  | SK (M (Π α, β)) => do
    let size_m := ty_size M
    match size_m with
    | .zero => .none
    | m =>
      let n ← α.pi_size
      let o ← β.pi_size
      pure ((m + 1) + n + o)
  | SK (Π α, β) =>
    let m := ty_size α
    let n := ty_size β
    pure (m + n)
  | _ => .none


