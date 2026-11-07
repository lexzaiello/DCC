import Dcc.Compile.Core

#eval (dcc_share (fun (x : Bool) => x))
#eval (LExpr.lam (.share_ty 1 (.const (.sort 0))) (.bvar 0))
#eval Std.format (dcc_compile (fun (x : Bool) => x))
#eval (·.fst) <$> Expr.infer (dcc_compile (fun (x : Bool) => x))
#eval Expr.infer' (dcc_compile (fun (x : Sort 0) => x))
#eval dcc_share (fun (α : Type) (x : α) => x)
#eval (dcc_share (fun (α : Type) (x : α) => x))
#eval Std.format (dcc_compile (fun (α : Type) (x : α) => x))
#eval Std.format (dcc_compile (fun (α : Type) (x : α) => x))
#eval (·.fst) <$> Expr.infer (dcc_compile (fun (α : Type) (x : α) => x))
#eval (·.fst) <$> Expr.infer (dcc_compile ((fun (α : Prop) (x : α) => x) True True.intro))
#eval dcc_share (fun (α : Sort 2) (x : α) => (fun (x : α) => x) x)
#eval Std.format (dcc_compile ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x)))
#eval (·.fst) <$> Expr.infer (dcc_compile ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x)))

/-
- Term is not well-typed:
                      because an unexpected term was found at: 
                        (Λ (Σ (Σ 𝟙 (`𝟙 (Sort 2))) (Snd (`𝟙 (Sort 2))))
                           (`(Σ (Σ 𝟙 (`𝟙 (Sort 2))) (Snd (`𝟙 (Sort 2)))) (Σ (Σ 𝟙 (`𝟙 (Sort 2))) (Snd (`𝟙 (Sort 2)))))
                           (∘ (Snd (Snd (`𝟙 (Sort 2))))
                              (Fst (`(Σ (Σ 𝟙 (`𝟙 (Sort 2))) (Snd (`𝟙 (Sort 2)))) (Σ (Σ 𝟙 (`𝟙 (Sort 2)))
                                                                     (Snd (`𝟙 (Sort 2))))))))
-/

open Dsl in
#eval Expr.infer' (DCC (Σ (Σ 𝟙 (`𝟙 (Sort 2))) (Snd (`𝟙 (Sort 2)))))
