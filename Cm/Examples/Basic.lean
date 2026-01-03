import Cm.Ast
import Cm.Eval
import Cm.Infer

#eval infer ⟪₂ :: Data nil ⟫
#eval infer ⟪₂ push_on (:: Data nil) nil ⟫

#eval Expr.display_infer <$> infer ⟪₂ push_on (:: Data nil) nil ⟫
#eval Expr.display_infer <$> infer ⟪₂ Data ⟫

def t_k : Expr := ⟪₂ ((, ((:: (quot Data)) ((:: (, ((:: ((>> fst) read)) ((:: ((quot) Data)) nil)))) ((:: ((>> fst) read)) ((:: (#read_y)) ((:: ((>> fst) read)) nil)))))) ((, nil) nil)) ⟫

#eval Expr.display_infer <$> infer ⟪₂ K ⟫

#eval Expr.display_infer <$> infer ⟪₂ (I :t_k K) Data (I Data) Data Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data ((I :t_k K) Data (I Data) Data Data) ⟫
#eval infer ⟪₂ (I :t_k K) ⟫

#eval norm_context <$> infer ⟪₂ K ⟫

#eval Expr.display_infer <$> infer ⟪₂ K' Data Data Data Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ >> read read (, I I) ⟫

#eval Expr.display_infer <$> (infer <=< infer) ⟪₂ K ⟫
#eval Expr.display_infer <$> (infer <=< infer) ⟪₂ I ⟫

#eval Expr.display_infer <$> infer ⟪₂ map_fst (I Data) (, I I) ⟫
#eval Expr.display_infer <$> infer ⟪₂ read (, K I) ⟫
#eval Expr.display_infer <$> infer ⟪₂ , K I ⟫

-- Context here looks like
#eval Expr.display_infer <$> infer ⟪₂ both (>> fst (>> next read)) (>> fst (>> next (>> next read))) (, (:: Data (:: (I Data) (:: Data nil))) (:: Data (:: Data (:: Data nil)))) ⟫
#eval Expr.display_infer <$> infer ⟪₂ bothM (>> fst (>> next read)) (>> fst (>> next (>> next read))) (, (:: Data (:: (I Data) (:: Data nil))) (:: Data (:: Data (:: Data nil)))) ⟫

#eval Expr.display_infer <$> infer ⟪₂ :: K I ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ I Data Data ⟫
#eval Expr.display_infer <$> infer ⟪₂ quot Data Data ⟫
#eval infer ⟪₂ I Data ⟫

#eval infer ⟪₂ (:: Data nil) ⟫

#eval Expr.display_infer <$> infer ⟪₂ (, I I) ⟫

/-
S combinator test: I combinator derivation.

S : ∀ (α : Type) (β : α → Type) (γ : ∀ (x : α), β x → Type)
  (x : ∀ (z : α) (y : β z), γ z y)
  (y : ∀ (z : α), β z)
  (z : α), γ z (y z)

I = S K K

S Data (I Data) (K' Data Data) (K' Data Data) (K' Data Data Data) Data

Check each component first.

We just need to streal the context from the actual argument,
probably.
-/

#eval Expr.display_infer <$> infer ⟪₂ S Data (I Data) (K' Data Data) (K' Data Data) (K' Data Data Data) Data ⟫

#eval try_step_n! 10 ⟪₂ ((, Data) ((, Data) ((((K' Data) Data) Data) Data))) ⟫

#eval infer ⟪₂ read ⟫
#eval infer ⟪₂ >>* read read ⟫

#eval infer ⟪₂ I ⟫

#eval infer ⟪₂ (K' :t_i Data I) ⟫
#eval infer ⟪₂ >>* read (K' :t_i Data I) (:: Data nil) Data Data ⟫
#eval infer ⟪₂ :: Data nil ⟫
#eval Expr.display_infer <$> infer ⟪₂ S Data (I Data) (K' Data Data) (K' Data Data) (K' Data Data Data) Data ⟫

#eval infer ⟪₂ quot ⟫

#eval infer ⟪₂ I Data ⟫
