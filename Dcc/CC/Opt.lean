import Dcc.CC.Ast
import Dcc.CC.Judge2

/-
Λ(?, ?, x ∘ Snd) = `(x)
-/

inductive RedAffEta : Expr → Expr → Prop
  | idl      : RedAffEta (DCC (Id(α) ∘ f)) f
  | idr      : RedAffEta (DCC (f ∘ Id(α))) f
  | fst      : RedAffEta (DCC (Fst(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) x
  | snd      : RedAffEta (DCC (Snd(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) y
  | snd'     : RedAffEta (DCC Λ(α, _b, x ∘ (Snd(_c) _env))) (DCC `(α, x))
  | beta     : RedAffEta
    (DCC ((App(_f_α, _f_β) _env) ∘ ⟦m, α, _b, γ⟧⟨Λ(_α, _β, x), y⟩))
    (DCC (x ∘ ⟦m, α, Fstc(Id(Sort m)), γ⟧⟨Id(α), y⟩))
  | ai       : RedAffEta (DCC Λ(α, β, (App(f_α, f_β) env))) (DCC Id((Π(f_α, f_β) env)))
  | fsi      : RedAffEta (DCC ⟦m, a, b, c⟧⟨(Fst(_β) env), (Snd(_β) env)⟩) (DCC Id((Σ(_β) env)))
  | uncur    : RedAffEta (DCC Λ(α, β,
    (App(_f_α, _f_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₁)⟩)) f
  | sigl     : RedAffEta x x' → RedAffEta (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y))
  | sigr     : RedAffEta y y' → RedAffEta (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y'))
  | congrFun : RedAffEta f f' → RedAffEta (DCC (f x)) (DCC (f' x))
  | congrArg : RedAffEta x x' → RedAffEta (DCC (f x)) (DCC (f x'))

/-
Other eta reductions I want to do:

- Want to "canonicalize" every sigma

Put them all in quoted form, if a normal form can be reached.

- can easily check for normal form.

- would also be cool if we could canonicalize Π. maybe we can use similar rules to as in Λ?

Λ(x) ∘ y = Λ(x ∘ ⟨y ∘ Fst, Snd⟩)
Λ(App) = Id

environments in general I feel like we could amortize.

If we can create a normal form, we can create a couple type.
-/
