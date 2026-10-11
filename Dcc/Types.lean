import Dcc.Ast
import Dcc.Attrs

namespace Expr

  /-| dep    : Arrow α β u (DCC ((Π (Id Sort u) (Λ Sort u (Id Sort u) (` (Σ (Id Sort u)) β))) α))
  | dep'   : Arrow α β u (DCC ((Π (Id Sort u) (!Λ Sort u (Id Sort u) (` (! (Σ (Id Sort u))) β))) α))-/

/-
(Π(Id(Sort 2),
             `(Sort 2,
               Π(!<Snd(`(⊤, Sort 1))>,
                 !Λ(Coup(`(⊤, Sort 1)), Snd(`(⊤, Sort 1)), `(!(Coup(Snd(`(⊤, Sort 1)))), Sort 2)))))
             !(Coup(`(⊤, Sort 1))))
-/

/-
(Swap B C) (& (,B₂ x y)) = (,(C x) y x)

B : A → Sort u       C : (x : A) (y : B x) → Sort v
---------------------------------------------------
(Swap B C) : (x : (! (Σ B))) → ((∘ (Σ (∘ B (Fst B)) (∘ C (Fst B))) (* (Σ B))) x)
-/

open Dsl in
def Swap.type (A B : Expr) : Expr :=
  DCC (→ (Σ' A (`A B)) (Σ (`⊤ A) (`⊤ (`B A))))

/-
(Π(Id(Sort 3),
                     `(Sort 3,
                       Π(!<Snd(`(⊤, Sort 2))>,
                         !Λ(Coup(`(⊤, Sort 2)), Snd(`(⊤, Sort 2)), `(!(Coup(Snd(`(⊤, Sort 2)))), Sort 3)))))
                     !(Coup(`(⊤, Sort 2))))
-/

open Dsl in
@[dcc_judge] abbrev Top.type : Expr :=
  DCC Sort 0

open Dsl in
@[dcc_judge] abbrev Tintro.type : Expr :=
  DCC ⊤

open Dsl in
@[dcc_judge] abbrev Bot.type : Expr :=
  DCC Sort 0

/-
TODO: x needs to depend on (env : δ)
-/
open Dsl in
@[dcc_judge] abbrev fst.f_β.type (α δ : Expr) (n : Level) : Expr :=
  (DCC (→ δ (→ α Sort n)))

open Dsl in
@[dcc_judge] abbrev id.type (α : Expr) : Expr :=
  DCC (→ α α)

/-
B : A → Sort u
--------------------------------
(Fst B) : (x : ((Σ (`⊤ A) (`⊤ B)) ∗)) → A
-/
open Dsl in
@[dcc_judge] abbrev fstc.type (A B : Expr) : Expr :=
  (DCC (→ (Σ' A B) A))

/-
B : A → Sort u
C : (x : A) → (y : B x) → Sort v
--------------------------------
(Fst B C) : (x : A) → (y : (Σ B C) x) → C x ((Fst B C) x)

I think we can leave (Fst B) and (Snd B).
They were expressive enough before.
-/
open Dsl in
@[dcc_judge] abbrev sndc.type (A B : Expr) : Expr :=
  (DCC ((Π (`⊤ (Σ' A B)) (`⊤ (∘ B (Fst B)))) ∗))

/-
Λ(β, x) y z → x ⟦β⟧(y, z)

β receives x

x : ∀ (s : coup.type α β m), γ s
-/
open Dsl in
@[dcc_judge] def curr.type (α β γ : Expr) : Expr :=
  DCC ((Π (`⊤ α) (`⊤ (Π β (Λ α β γ)))) ∗) -- weaken α, keep x

open Dsl in
@[dcc_judge] abbrev curr.x.type (A B C : Expr) : Expr :=
  DCC ((Π (`⊤ (Σ' A B)) (`⊤ C)) ∗)

open Dsl in
@[dcc_judge] abbrev curr'.type (α β γ : Expr) : Expr :=
  DCC ((Π (`⊤ (! α)) (`⊤ (Π (!<> β) (!Λ α β γ)))) ∗) -- weaken α, keep x

open Dsl in
@[dcc_judge] abbrev curr'.x.type (A B C : Expr) : Expr :=
  DCC ((Π (`⊤ (Σ' A B)) (`⊤ C)) (! (Σ A B)))

/-
*(f) &(x) = (f x)
-/

/-
Nondependent quotation.

x : α
`(β, x) : β → α
-/
open Dsl in
@[dcc_judge] abbrev quot.type (α β : Expr) : Expr :=
  DCC (→ β α)

open Dsl in
@[dcc_judge] abbrev comp.type (A C g : Expr) : Expr :=
  DCC ((Π (`⊤ A) (`⊤ (∘ C g))) ∗)

open Dsl in
@[dcc_judge] abbrev comp.f.type (B C : Expr) : Expr :=
  DCC ((Π (`⊤ B) (`⊤ C)) ∗)

/-
((Eql B) env (,B x y)) →ᵦ (= (B env) x y)
-/
open Dsl in
@[dcc_judge] def eql.type (B A : Expr) : Expr :=
  (DCC ((Π (`⊤ A) (`⊤ (Π (Σ B (Λ A B (∘ B (Fst B)))) (Λ A (Σ B (Λ A B (∘ B (Fst B)))) (`(Σ B (Λ A B (∘ B (Fst B)))) (Sort 0)))))) ∗))

/-
have (, (& env) (& x))

⟨?, ?₂⟩ (& (, env x)) = ( (, env x), ?₂ (, env x) (? (, env x)))

(⟨,⟩ (Id (Σ f_α))
     (Λ (Σ f_α)
        (`(Σ f_α) (Σ f_α)))
        ()))

must make (Eql f_α) env (, x x)

pair shouldn't actually be required. we should be able to do this with Map.

we can duplicate Eql, actually.

duplicate both.

Assume we have

? (, env env) (& x)
(∘ (Eval ?) (Map Id ?₂)) (, env env) (& x)
= ? env (? env) (& x)

want (,x x)

λenv&.λx&. ((Eql f_α)

Can we derive Dup? Don't think so.
We can with curry? No we can't because we can't change what's inside B.

But B is a function

? (& env) (& x)

(& (, env x))

(, (, env x) (, env x))
(Map' B C f g) (& (, env x)) = (, (f env) (g x))
this one is dependent.

(⟨,⟩ (Id δ) (Λ ? env ((Λ ? ? ?) env (& x))

But pair is analagous to S, so it should be able to do everything we need.

This is like W combinator:
(Dup A) (& x) = (,(`A A) x x)

(Dup (Σ f_α)) (& (, env x)) = (,(, env x) (, env x))

(Dup f_α f) (& env) (& x) = f env (,(`(f_α env) (f_α env)) x x)
-/

open Dsl in
@[dcc_judge] def refl.type (f_α δ : Expr) : Expr :=
  (DCC ((Π (`⊤ (! δ)) (`⊤ (Π (!<> f_α) (Dup f_α (Eql f_α))))) ∗))

/-
B : A → Sort u      f : (x : A) → (y : (Σ B (Λ A B (∘ B (Fst B)))) x) → C x y
-------------------------------
(Dup B f) : (x : (! A)) → (y : (!<> B) x) → ((Dup B c) x y)
-/
open Dsl in
@[dcc_judge] def Dup.type (A B C : Expr) : Expr :=
  (DCC ((Π (`⊤ (! A)) (`⊤ (Π (!<> B) (Dup B C)))) ∗))

/-
f_α : α → Sort m
f_β : (x : α) (y : f_α x) → Sort n
Π(m, f_α, f_β) : α → Sort n
-/
open Dsl in
@[dcc_judge] def Pi.type (α : Expr) (v s : Level) : Expr :=
  DCC (→ α Sort (max v s))

/-abbrev Pi.C.type (f_α α : Expr) (m o : Level) :=
  (DCC (Π(Id(Sort m), `(Sort m, Π(f_α, Λ(α, f_α, `(Coup(m, α, f_α), Sort o))))) α))-/

open Dsl in
@[dcc_judge] def pair.β.type (α : Expr) (m n : Level) : Expr :=
  DCC (→ (Sort m) (→ α Sort n))

/-
f_β : ∀ (env : δ) (x : α), Sort n
x : ∀ (env : δ) (y : β),
β = f_β env x
Subst(x, Snd(f_β)) : ∀ (env : δ) (s : Σ(f_β) env),
-/

/-
Σ(f_β)

f_β : δ → α → Sort n

Σ(f_β) : δ → Sort n
-/
open Dsl in
@[dcc_judge] abbrev Sigma.type (δ : Expr) (m n : Level) : Expr :=
  DCC (→ δ Sort max m n)

open Dsl in
@[dcc_judge] abbrev Coup.type (m n : Level) : Expr :=
  DCC Sort max m n

/-
f_α : δ → Sort m
Eval(f_α, f_β) : ∀ (s : ∀ (env : δ), (Σ(f_α, f_β) env)) (env : δ),
  f_β env (Fst(f_β env) (s env))

Fst ({ f, g } x) = f x

Eval(f_α, f_β) f x = (Snd ∘ f) x

Eval(f_α, f_β) : ∀ (s : ∀ (env : δ), (Σ(f_α, f_β) env)) (env : δ),
  f_β env (Fst(f_β env) (s env))

Eval takes M and N explicitly?

Eval(M, N)

but then we can't destructure couple back into data.
Need actual eval.

Eval(x) ⟦β⟧(y, z) = x y z?

x : ∀ (x : α) (y : β x), γ x y
Eval(x) : ∀ (c : Coup(β)), Eval(γ) c

This is canonical.
-/

open Dsl in
@[dcc_judge] abbrev Eval.type (α β γ : Expr) : Expr :=
  DCC ((Π (`⊤ (Σ' α β)) (`⊤ (Eval α β γ))) ∗)

open Dsl in
@[dcc_judge] abbrev Eval.x.type (A' B' C : Expr) : Expr :=
  DCC ((Π (`⊤ A') (`⊤ (Π B' C))) ∗)

open Dsl in
@[dcc_judge] abbrev Pair.f.type (A B : Expr) : Expr :=
  DCC ((Π (`⊤ A) (`⊤ B)) ∗)

open Dsl in
@[dcc_judge] abbrev Pair.g.type (A B C : Expr) : Expr :=
  DCC ((Π (`⊤ A) (`⊤ (Π B C))) ∗)

/-
⟨f, g⟩ x = (f x, g x (f x))

f : ∀ (x : α), β x
g : ∀ (x : α) (y : β x), γ x y
⟨f, g⟩ : ∀ (x : α), Σ(Λ(α, β, γ)) x
-/
open Dsl in
@[dcc_judge] abbrev Pair.type (A B C : Expr) : Expr :=
  DCC ((Π (`⊤ (! A)) (`⊤ (∘ (Σ B C) (* A)))) ∗)

/-
(≃.3 A B) : (eq : (! (≃ A B))) → (x : (! A)) → (= ((≃.2 A B) ((≃.1 A B) x.raw)) x.raw)

have (, (& (_ : (≃ A B))) (& x))

want

(, (, (_ : (≃ A B)) (_ : (≃ A B))) (, x x))

can do this with dup

Swap (, (, (_ : (≃ A B)) (_ : (≃ A B))) (, x x)) = (, (,x x)  (, (_ : (≃ A B)) (_ : (≃ A B))))
Assoc (, (,x x)  (, (_ : (≃ A B)) (_ : (≃ A B)))) = (, x (, x (, (_ : (≃ A B)) (_ : (≃ A B)))))

-/

open Dsl in
abbrev Dup' (A : Expr) (u : Level) : Expr :=
  DCC ((Dup (Id (Sort u)) (`(Sort u) (Id (Σ' A (`A A))))) (& A))

/-open Dsl in
@[dcc_judge] def Equiv_3.type (A B : Expr) (u v : Level) : Expr :=
  let t_to_fun   := DCC (→ (: A Sort u) B)
  let t_from_fun := DCC (→ (: B Sort v) A)
  (DCC ((Π (Id (Sort (max u v)))
            (`(Sort (max u v))
               (Π (`(! (≃ A B)) (! A))
                  (Λ (! (≃ A B))
                     (! A)
                     (∘ ((Eql (Id Sort u)) A)
                        (∘ (Swap A A)
                           (∘ (∘ (Map A
                                      A
                                      (Id A)
                                      (∘ (∘ (∘ (Eval t_from_fun (`t_from_fun B) (Id (t_from_fun)))
                                               (Map t_from_fun
                                                    B
                                                    (Id t_from_fun)
                                                    (Eval t_to_fun (`t_to_fun A) (Id t_to_fun))))
                                            (Assoc t_from_fun t_to_fun A))
                                         (Swap A (Σ (`t_from_fun t_to_fun))) /- Have (, x (, from_fun to_fun)) -/)) -- have (, x (, x (, from_fun to_fun)))
                                 (Assoc A A (Σ (`t_from_fun t_to_fun)))) -- have (, (, x x) (, from_fun to_fun))
                              (Map (Σ (`A A))
                                   (Σ (`t_from_fun t_to_fun))
                                   #(Dup' A u)
                                   (∘ (Map (t_from_fun)
                                           (t_to_fun)
                                           (≃.2 A B)
                                           (≃.1 A B))
                                      #(Dup' (DCC (≃ A B)) (max u v))))))))))) (! (≃ A B))))

open Dsl in
@[dcc_judge] def Equiv_4.type (A B : Expr) (u v : Level) : Expr :=
  let t_to_fun   := DCC (→ (: A Sort u) B)
  let t_from_fun := DCC (→ (: B Sort v) A)
  (DCC ((Π (Id (Sort (max u v)))
            (`(Sort (max u v))
               (Π (`(! (≃ A B)) (! B))
                  (Λ (! (≃ A B))
                     (! B)
                     (∘ ((Eql (Id Sort u)) B)
                        (∘ (Swap B B)
                           (∘ (∘ (Map B
                                      B
                                      (Id B)
                                      (∘ (∘ (∘ (Eval t_to_fun (`t_to_fun A) (Id (t_to_fun)))
                                               (Map t_to_fun
                                                    A
                                                    (Id t_to_fun)
                                                    (Eval t_from_fun (`t_from_fun B) (Id t_from_fun))))
                                            (Assoc t_to_fun t_from_fun A))
                                         (Swap B (Σ (`t_to_fun t_from_fun))) /- Have (, x (, from_fun to_fun)) -/)) -- have (, x (, x (, from_fun to_fun)))
                                 (Assoc B B (Σ (`t_to_fun t_from_fun)))) -- have (, (, x x) (, from_fun to_fun))
                              (Map (Σ (`B B))
                                   (Σ (`t_to_fun t_from_fun))
                                   #(Dup' B u)
                                   (∘ (Map (t_to_fun)
                                           (t_from_fun)
                                           (≃.1 A B)
                                           (≃.2 A B))
                                      #(Dup' (DCC (≃ A B)) (max u v))))))))))) (! (≃ A B))))
-/

end Expr
