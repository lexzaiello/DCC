import Mathlib.Data.Nat.Notation

/-
Improvements to DCC:

- Holes / metavariables are not well-typed expressions, but they are unifiable
- Bool is renamed to 𝟚
- ⊤ is renamed to 𝟙
- ⊥ is renamed to 𝟘
- ℕ is a base type
- No combinator has an arity of more than 2 now, except "points" (Γ)
- Vector is not primitive, but we assume it exists
- Σ.size does a literal syntactic size count
  - The head of Σ is either a Value or a Comb (spine)
  - Congruence is represented through nested Comb.reduct
    - This way we might be able to even avoid congrFun and congrArg altogether and only have head reductions
      - Comb.type gives the list that is applied to Π
      - $ : Σ (c : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c))) (x : (Snd Sort) Comb.dom c) → Comb.cod c x
        - This subsumes Comb.mk
    - Comb.cod is only necessary if the combinator returns a Value.
    - e.g., (Id 𝟙) ∗, or (Fst <sigma containing values>)
      - n is just head, not maximal
    - Λ : Comb 1, as well. But its context must be extended with x.
      - Λ x redcues to Λ₁(x)
      - This way, $ is always of arity 1
      - All combinators have arity 1, so we can ditch that. Nice.
        - They are still distinguished however by n. Λ₁ is 1 (Λ)
- & is also a combinator, but it is not represented with a list it is just a normal function
  - It freezes reduction. No reduction happens under its point.
  - In order to run some function on its contents, you must prove that the function decreases the size
- Level  : Sort 0
- Value  : (u : Level) → (A : Sort u) → (x : A) → Sort u
- A combinator is an interpretation of a context, which is a Σ-list of terms
  - Comb : ℕ → Type 0
  - (Λ)  : Comb 3
  - Comb : Type 0
  - A combinator has a signature, which is the context it expects
    - The signature also contains the universe levels
  - Comb.dom     : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c)) → (Σ (u : Level), Sort u)
  - Comb.cod     : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c)) → (x : Fst (Comb.dom n c Γ)) → (Σ (u : Level), Sort u)

  - Comb.arity   : (n : ℕ) → (c : Comb n)      → ℕ := n

  - Comb.mono    : (Σ (n : ℕ) (c : Comb (.succ n)) (Γ : Comb.sig (.succ n) c)) → (x : Comb.dom n c Γ) → (< $ (Id _) (,n c Γ x))
- Level is a base type
  - zero : Level
  - succ : Level → Level
  - max  : Level → Level → Level
- Sort : (lv : Level) → (∘ Sort Level.succ)
- (Σ B C) is the default now instead of just (Σ B)
- Nothing needs to index the environment anymore, since all combinators are curryable via lists.
- Lists are primitive, but not made of points
  - , : (u : Level) → (v : Level) → (A : (Sort u)) → (B : (x : A) → (Sort v)) → (x : A) → (y : (B x)) → (Σ A B)
- Parenthesized combinators as in past DCC, e.g., (Id A) expand to:
  (Id A) ⇒ (comb Id (, l_1 _ 𝟙 (`𝟙 (Sort _)) ∗

The meat of it. What will Π look like now?
We can use an even simpler encoding now. I think.

($ (,(, 4 Π (, ∗ u)) A))        := (, 3 Π (, u A))
($ (, (, 3 Π (, u A)) v))       := (, 2 Π (, u A v))
($ (, (, 2 Π (, u A v)) B))     := (, 1 Π (, u A v B))
($ (, (, 1 Π (, u A v B)) env)) := (Π u A v B env)

we definitely still want to keep the environment for Π. Or, the type-checker can duplicate it manually.

f : (Π u A₁ v B env)  x : A₂      (A₁ env) ≡ A₂
----------------------------------------------
B env x →ᵦ τ                           f x : τ

u : (env : Γ) → Level     A : (env : Γ) → Sort (u env)
v : (env : Γ) → Level     B : (env : Γ) → (x : A env) → Sort (v env)
                      env : Γ
----------------------------------------------------------------------
             (Π u A v B env) : Sort (max (u env) (v env))

---------------------------------------------------------
Comb.sig 1 Id := (Σ (Id (Sort 0)) (`(Sort 0) Sort) Level)


-------------
Id : ℕ → Comb


----------------------------------------------------------------
Comb.dom (, 1 (,(Comb.sig 1) (Id 1) (,Sort u A))) := (,Sort u A)

------------------------------------------------------------------
Comb.cod (, 1 (,(Comb.sig 1) (Id 1) (,Sort u A))) _x := (,Sort u A)

VERY IMPORTANT: CONGRFUN is avoided due to nested ($ indicating congrFun explicitly

general CongrFun is avoided easily since we just match nested $.
Combinators that make no "step" should not use $. e.g., Π.


-/
