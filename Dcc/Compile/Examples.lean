import Dcc.Compile.Core
import Dcc.Tactic.Quote
import Dcc.Judge2

/-
TODO: tomorrow, need to add existential support for conversion to Lean.
Either that or lift everything to TYpe. Not sure.
-/

#eval Std.format <| dcc_compile' {Expr.infer₂} ((fun (α : Sort 0) (x : α) => x) True True.intro)
#eval Std.format <| dcc_compile' {Expr.infer₂} ((fun (α : Sort 0) (x : α) => x) True True.intro)
#check dcc_decompile #(dcc_compile' {Expr.infer₂} ((fun (α : Sort 0) (x : α) => x) True True.intro))
#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} (fun (α : Sort 2) (x : α) => x) (Sort 1)
#check dcc_decompile #(dcc_compile' {Expr.infer₂} {Expr.reduce₂} (fun (α : Sort 2) (x : α) => x) (Sort 1))
dcc_show #(dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => x) (Sort 1) (Sort 0)))
#eval Std.format <| dcc_infer'' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => x))
dcc_show #(dcc_infer'' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => x)))
#check dcc_decompile #(dcc_infer'' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => x)))
dcc_show #(dcc_infer'' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => x)))
#eval Std.format (dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => x) (Sort 1)))
dcc_show #(dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => x) (Sort 1)))
#eval Std.format <| dcc_infer' {Expr.infer₂} (fun (α : Sort 0) (x : α) => x) True True.intro

#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} (fun (x : Sort 0) => (fun (x : Sort 0) => x) x)
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} (fun (x : Sort 0) => (fun (x : Sort 0) => x) x)
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} ((fun (x : Sort 1) => (fun (x : Sort 1) => x) x) (Sort 0))
#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))

#eval Std.format <| dcc_compile' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce₂} ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1) (Sort 0))

#eval Std.format <| (dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x) (fun x => x) True.intro))
--#check dcc_decompile #((dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x) (fun x => x) True.intro)))
#time #eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x) (fun x => x) True.intro)

#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 0 → Sort 0) (x : f True) => x))
#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (f : Sort 2 → Sort 2) (x : f (Sort 1)) => x))

def K_example₁ : Expr :=
  dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 1) (β : α → Sort 1) (x : α) (_y : β x) => x))

def K_example : Expr :=
  dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 1) (β : α → Sort 1) (x : α) (_y : β x) => x) (Sort 0))

def K_example₂ : Expr :=
  dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 1) (β : α → Sort 1) (x : α) (_y : β x) => x) (Sort 0))

def K_example₃ : Expr :=
  dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 3) (β : α → Sort 2) (x : α) (_y : β x) => x) (Sort 2) (fun x => x))

def K_example₃' : Expr :=
  dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 3) (β : α → Sort 2) (x : α) (_y : β x) => x) (Sort 2) (fun x => x) (Sort 1) (Sort 0))

def K_examplea : Expr :=
  dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 3) (β : α → Sort 2) (x : α) (_y : β x) => x) (Sort 2) (fun x => x) (Sort 1))

def K_example₃'' : Expr :=
  dcc_compile' {Expr.infer₂} {Expr.reduce_all₂} ((fun (α : Sort 3) (β : α → Sort 2) (x : α) (_y : β x) => x) (Sort 2) (fun x => x) (Sort 1) (Sort 0))

#eval Std.format <| K_example₃
#eval Std.format <| K_example₃

--#check dcc_decompile #(K_example₃)

#eval Std.format <| K_example₃'
#eval Std.format <| K_examplea
#eval Std.format <| K_example₃''

def K_example' : Expr :=
  dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} (fun (α : Sort 1) (β : α → Sort 1) (x : α) (_y : β x) => x)

#eval Std.format <| K_example'

#eval Std.format <| K_example

#eval Std.format <| dcc_infer' {Expr.infer₂} {Expr.reduce_all₂} (fun (x : Sort 0) => x)

#eval Std.format <| (DCC (!<Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))> &(⟦`(⊤, Sort 1)⟧(∗, Sort 0)))).reduce_all₂

#eval Std.format <| (DCC (Sndc(`(⊤, Sort 1)) (⟦`(⊤, Sort 1)⟧(∗, Sort 0)))).reduce_all₂

#eval Std.format <| K_example₂

#eval Std.format <| (DCC (Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))) ⟦`(⊤, Sort 1)⟧(∗, Sort 0))).reduce_all₂
#eval (DCC (Sndc(`(⊤, Sort 1)) ⟦`(⊤, Sort 1)⟧(∗, Sort 0))).reduce_all₂

#eval Std.format <| (DCC !<Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))>).infer₂'

def S_example : Expr :=
  dcc_compile' {GenericExpr.infer₂} {GenericExpr.reduce_all₂}
    fun (α : Sort 1) (β : α → Sort 1) (γ : ∀ (x : α) (y : β x), Sort 1) (x : ∀ (x : α) (y : β x), γ x y) (y : ∀ (x : α), β x) (z : α) => x z (y z)

#eval Std.format <| (DCC (*<(*<(`(Coup(`(⊤, Sort 1)), Sort 1))>)> ∘'
                Fstc(!<(!<(Π(Sndc(`(⊤, Sort 1)),
                           Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))>)>))).reduce_all₂

#eval Sigma.fst <$> (DCC? (*<(*<(`(Coup(`(⊤, Sort 1)), Sort 1))>)> ∘'
                Fstc(!<(!<(Π(Sndc(`(⊤, Sort 1)),
                           Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1))))>)>))).domain? (τ_c := Unit)

/-
Deref order may be reversed?
-/

/-
∀ argument is being marked shared, but it needs its context applied before it can be banged. otherwise, it is not a type.

this is probably an issue with auto-sharing since this can only be explained by the number of calculations.
K has the same first two params.

this is happening before infer time, to be clear, which is even more sus. probably issue with auto wrap share.

the number of times being shared is not the issue.
the issue is when a share is itself shared.
the other confusion is Π not receiving its context, even though it's being used like a type.

unless we're at the top level, i.e., in CC, I think we can assume there is a context,
in which case it should not be !(..), but actually !<...>? maybe.

things under abstract are all functions of the context. so !(...) is wrong I think.
-/

#eval (DCC Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))).infer₂'
#eval (DCC Π(Sndc(`(⊤, Sort 1)), Λ(Coup(`(⊤, Sort 1)), Sndc(`(⊤, Sort 1)), `(Coup(Sndc(`(⊤, Sort 1))), Sort 1)))).infer₂'
