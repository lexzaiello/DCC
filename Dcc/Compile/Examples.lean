import Dcc.Compile.Core

open Dsl in
example : Cc (.lam (.share_ty 1 (.const (.sort 0))) (.bvar 0)) (DCC ((!Λ ⊤ (`⊤ (Sort 0)) (∘ (Snd (`⊤ (Sort 0))) (* (Σ ⊤ (`⊤ (Sort 0)))))) (& ∗))) := by
  apply Cc.lam
  · apply Abstract.const
    constructor
  · apply Abstract.var
    apply AbstractVar.bang
    · apply AbstractVar.zero

example : Cc (.lam (.share_ty 1 (.const (.sort 0))) (.lam (.share_ty 1 (.const (.sort 0))) (.bvar 1)))
             (open Dsl in (DCC ((!Λ ⊤
                       (`⊤ (Sort 0))
                       (!Λ (Σ ⊤ (`⊤ (Sort 0)))
                           (`(Σ ⊤ (`⊤ (Sort 0))) (Sort 0))
                           (∘ (∘ (Snd (`⊤ (Sort 0)))
                                 (Fst (`(Σ ⊤ (`⊤ (Sort 0))) (Sort 0))))
                              (* (Σ (Σ ⊤ (`⊤ (Sort 0))) (`(Σ ⊤ (`⊤ (Sort 0))) (Sort 0))))))) (& ∗)))) :=
  .lam (.const (.sort)) (.lam (.const .sort) (.var (.bang (.succ .zero))))
