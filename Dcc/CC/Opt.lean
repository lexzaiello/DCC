import Dcc.CC.Ast
import Dcc.CC.Judge2

/-
Λ(?, ?, x ∘ Snd) = `(x)

f ∘ `(x) = `(f x)

`(?, `(
-/

namespace Expr

/-
Only count β in size of Pi so we can normalize greedily.
-/

inductive RedAffEta : Expr → Expr → Prop
  /-
   pi rule might break things
  -/
  | red      : e.RedAff e' → e'.IsNormAff → RedAffEta e e'
  | pi       : Size env (m + 1)
    → RedAffEta (DCC (f_α env)) α → RedAffEta (DCC (f_β env)) β
    → RedAffEta (DCC (Π(f_α, f_β) env)) (DCC (Π(`(⊤, α), `(⊤, β)) ∗))
  | quot     : RedAffEta (DCC f ∘ `(β, x)) (DCC `(β, (f x)))
  | idl      : RedAffEta (DCC (Id(α) ∘ f)) f
  | idr      : RedAffEta (DCC (f ∘ Id(α))) f
  | fst      : RedAffEta (DCC (Fst(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) x
  | snd      : RedAffEta (DCC (Snd(_β) _env) ∘ ⟦_m, _a, _b, _c⟧⟨x, y⟩) y
  | snd'     : RedAffEta (DCC Λ(α, _b, x ∘ (Snd(_c) _env))) (DCC `(α, x))
  | beta     : RedAffEta
    (DCC ((App(_f_α, _f_β, _f_γ) _env) ∘ ⟦m, α, _b, γ⟧⟨Λ(_α, _β, x), y⟩))
    (DCC (x ∘ ⟦m, α, Fstc(Id(Sort m)), γ⟧⟨Id(α), y⟩))
  | ai       : RedAffEta (DCC Λ(α, β, (App(f_α, f_β, f_γ) env))) (DCC Id((Π(f_α, f_β) env)))
  | fsi      : RedAffEta (DCC ⟦m, a, b, c⟧⟨(Fst(_β) env), (Snd(_β) env)⟩) (DCC Id((Σ(_β) env)))
  | uncur    : RedAffEta (DCC Λ(α, β,
    (App(_f_α, _f_β, _f_γ) _env) ∘ ⟦_m, _a, _b, _c⟧⟨f ∘ (Fst(_x) _env₁), (Snd(_x₂) _env₁)⟩)) f
  | sigl     : RedAffEta x x' → RedAffEta (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y))
  | sigr     : RedAffEta y y' → RedAffEta (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y'))
  | congrFun : RedAffEta f f' → RedAffEta (DCC (f x)) (DCC (f' x))
  | congrArg : RedAffEta x x' → RedAffEta (DCC (f x)) (DCC (f x'))

def RedAffEta.decreasing (h : RedAffEta e e') : (size e').fst < (size e).fst := by
  induction h <;> (try grind)  

end Expr

