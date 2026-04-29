import Dcc.Attrs
import Dcc.Ast

inductive Red : Expr → Expr → Prop
  | subst₁   : Red (DCC (Subst(x, Fst(f_β)) env ⟦β⟧(y, z))) (DCC (x env y))
  | subst₂   : Red (DCC (Subst(x, Snd(f_β)) env ⟦β⟧(y, z))) (DCC (x env z))
  | snd'     : Red (DCC (Snd'(_δ, _τ) ⟦β⟧(a, b))) b
  | quot     : Red (DCC (`(β, x) y)) x
  | id       : Red (DCC (Id(α) x)) x
  | appl     : Red (DCC (App(_α, _β) ⟦δ⟧(env, ⟦β⟧(x, y)))) (DCC (x y))
  | appp     : Red (DCC (App(_α, _β) ⟦δ⟧(env, (⟨f, g⟩ x)))) (DCC ((f x) (g x)))
  | fst      : Red (DCC (Fst(_α) _env ⟦β⟧(a, b))) a
  | fstp     : Red (DCC (Fst(_α) _env (⟨f, g⟩ x))) (DCC (f x))
  | snd      : Red (DCC (Snd(_α) _env ⟦β⟧(a, b))) b
  | sndp     : Red (DCC (Snd(_α) _env (⟨f, g⟩ x))) (DCC (g x))
  | comp     : Red (DCC ((x ∘ y) z)) (DCC (x (y z)))
  | curr     : Red (DCC (Λ(α, β, x) y z)) (DCC (x ⟦β⟧(y, z)))
  | sigl     : Red x x' → Red (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x', y))
  | sigr     : Red y y' → Red (DCC ⟦β⟧(x, y)) (DCC ⟦β⟧(x, y'))
  | congrFun : Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congrArg : Red x x' → Red (DCC (f x)) (DCC (f x'))
