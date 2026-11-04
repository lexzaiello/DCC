import Dcc.Judge3
import Dcc.Ast
import Dcc.Ast.Share
import Dcc.Metatheory.Progress
import Dcc.Types

open Expr (Value)

/-
This version of the compiler allocates memory via bump allocation.
A maximum memory is specified. Then, each top-level value is shared
exactly that number of times. Contexts are always curried with !Λ.
This is done with a preprocessing step, however.

Variable abstraction:

----------------
⟦0⟧_(Σ Γ Δ) := Snd Δ


--------------------------------------
    ⟦n + 1⟧_(Σ Γ Δ) := (∘ ⟦n⟧_Γ (Fst Δ))

----------------------------
⟦n⟧_(! A) := (∘ ⟦n⟧_A (! A))

where Γ and Δ are a DCC terms.

Variable lookup should never occur on a banged context.
Rather, a context is dereferenced first.
A context is either 𝟙 or (Σ Γ Δ).

Nested Σ binders:

------------------------
⟦Σ A B⟧_(! Γ) := (Σ' ⟦A⟧_Γ ⟦B⟧_(Σ Γ ⟦A⟧_Γ))

-----------------------
⟦A × B⟧_(! Γ) := (Σ' ⟦A⟧_Γ (Λ Γ ⟦A⟧_Γ (∘ ⟦B⟧_(! 𝟙) (`(Σ Γ ⟦A⟧_Γ) (& ∗)))))

Nested lambda binders:

----------------------------------
⟦(λ x : A => M)⟧_(! Γ) := (!Λ Γ ⟦A⟧_Γ ⟦M⟧_(! (Σ Γ ⟦A⟧_γ)))

Γ is not a bang
----------------------------------
⟦(λ x : A => M)⟧_Γ := (Λ Γ ⟦A⟧_Γ ⟦M⟧_(Σ Γ ⟦A⟧_γ))

Nested Π binders:

If A does not depend on the context
and if M depends only on x, but not the context
----------------------------------
⟦(∀ x : A, M)⟧_(! Γ) := ((Π (`𝟙 (⟦A⟧_(! 𝟙) (& ∗))) (`𝟙 (⟦M⟧_(! (Σ 𝟙 ⟦A⟧_𝟙)) (& ∗)))) ∗)

If A does not depend on the context and M does not depend on the context
----------------------------------
⟦(∀ x : A, M)⟧_(! Γ) := ((Π (`𝟙 (⟦A⟧_(! 𝟙) (& ∗))) (`𝟙 (`(⟦A⟧_(! 𝟙) (& ∗)) (⟦M⟧_(! 𝟙) (& ∗))))) ∗)

If either A or M depend on the context
------------------------------------- TODO: this should be split up for if M does not as well
⟦(∀ x : A, M)⟧_(! Γ) := (Π ⟦A⟧_(! Γ) (!Λ Γ ⟦A⟧_Γ ⟦M⟧_(! (Σ Γ ⟦A⟧_Γ))))

A and M can be checked to depend on the context by attempting compiling them with their respective
empty or nondependent contexts, then falling back.

Nested application:

⟦M⟧_Γ : ((Π B₁ C₁) x₁)    ⟦N⟧_Γ : ((Π B₂ C₂) x₂)
(B₁ x₁) →ᵦ A              (C₂ x) →ᵦ B

(∘ N (Fst (`Γ Γ))) : ((Π (`𝟙 A₃) (`𝟙 (Π B₃ C₃))) ∗)
---------------------------------------------
⟦M N⟧_(! Γ) := (∘ (Eval A B ⟦M⟧_Γ) (⟨,⟩C₃ (Id Γ) (Λ Γ (`Γ Γ) (∘ ⟦N⟧_Γ (Fst (`Γ Γ)))))

Constants:

--------------------
⟦Bool.True⟧_Γ := (`Γ 𝟙₂)

--------------------
⟦Bool.False⟧_Γ := (`Γ 𝟘₂)

--------------------
⟦True⟧_Γ := (`Γ 𝟙)

--------------------
⟦False⟧_Γ := (`Γ 𝟘)

--------------------
⟦True.intro⟧_Γ := (`Γ ∗)

--------------------
⟦Sort u⟧_Γ := (`Γ (Sort u))

Shared constants:

x is not also shared, and x is a constant
-----------------------------------------
⟦Share.share x⟧_(! Γ) := ($<> ⟦x⟧_Γ)

⟦A⟧_𝟙 is not a bang
-----------------------------------------
⟦λ x : A => M⟧ := ((Λ 𝟙 ⟦A⟧_𝟙 ⟦M⟧_(Σ 𝟙 ⟦A⟧_𝟙)) ∗)

⟦A⟧_𝟙 is a bang
-----------------------------------------
⟦λ x : A => M⟧ := ((!Λ 𝟙 ⟦A⟧_(! 𝟙) ⟦M⟧_(! (Σ 𝟙 ⟦A⟧_(! 𝟙)))) (& ∗))

--------------------
⟦(M N)⟧ := (⟦M⟧ ⟦N⟧)

Constants:

--------------------
⟦Bool.True⟧ := 𝟙₂

--------------------
⟦Bool.False⟧ := 𝟘₂

--------------------
⟦True⟧ := 𝟙

--------------------
⟦False⟧ := 𝟘

--------------------
⟦True.intro⟧ := ∗

--------------------
⟦Sort u⟧ := Sort u

Shared constants:

x is not also shared, and x is a constant
-----------------------------------------
⟦Share.share x⟧ := (& ⟦x⟧)

⟦A⟧_𝟙 is not a bang
-----------------------------------------
⟦λ x : A => M⟧ := ((Λ 𝟙 ⟦A⟧_𝟙 ⟦M⟧_(Σ 𝟙 ⟦A⟧_𝟙)) ∗)

⟦A⟧_𝟙 is a bang
-----------------------------------------
⟦λ x : A => M⟧ := ((!Λ 𝟙 ⟦A⟧_(! 𝟙) ⟦M⟧_(! (Σ 𝟙 ⟦A⟧_(! 𝟙)))) (& ∗))

--------------------
⟦(M N)⟧ := (⟦M⟧ ⟦N⟧)

Σ binders:

-------------------
⟦Σ A B⟧ := ((Σ' ⟦A⟧_𝟙 (Λ 𝟙 ⟦A⟧_𝟙 ⟦B⟧_(Σ 𝟙 ⟦A⟧_𝟙))) (& ∗))

-------------------
⟦A × B⟧ := (Σ ⟦A⟧ (`⟦A⟧ ⟦B⟧))

TODO:
- equality
- shared constants more times than the context we are under
-/

open Dsl in
inductive IsCtx : Expr → Type
  | unit  : IsCtx (DCC 𝟙)
  | sigma : IsCtx A → Value B → IsCtx (DCC (Σ A B))
  | bang  : IsCtx A → IsCtx (DCC (! A))

inductive Ctx where
  | mk : (Γ : Expr) → (hΓ : IsCtx Γ) → Ctx

inductive RawCompileError (δ : Type) : Type
  | not_a_context : (Δ    : Expr) → (Γ : δ)           → RawCompileError δ
  | sub           : (at_e : Expr) → (Γ : δ)           → RawCompileError δ → RawCompileError δ
  | and           : (Γ    : δ)    → RawCompileError δ → RawCompileError δ → RawCompileError δ
  | not_a_value   : (v    : Expr) → (Γ : δ)           → RawCompileError δ

def RawCompileError.with_ctx (e : RawCompileError Δ) (x : Γ) : RawCompileError Γ :=
  match e with
  | .not_a_context Δ _ => .not_a_context Δ x
  | .not_a_value v _ => .not_a_context v x
  | .sub x₀ _ x₁ => .sub x₀ x (x₁.with_ctx x)
  | .and _ x₁ y₂ => .and x (x₁.with_ctx x) (y₂.with_ctx x)

abbrev SimpleError  := RawCompileError Unit
abbrev CompileError := RawCompileError Ctx

open Lean.Meta (MetaM)

abbrev DebruijnIdx := ℕ

deriving instance Lean.ToExpr for Expr

abbrev CtxT (m : Type → Type v) (α : Type) := StateT Ctx m α

inductive SeekCtx : Type where
  | mk : (e : Expr) → (Γ : Ctx) → SeekCtx

abbrev SeekExcept (α : Type u) := Except CompileError α

abbrev SeekExcept.map {α β : Type u} (f : α → β) : SeekExcept α → SeekExcept β := Except.map f

abbrev SeekExceptT (m : Type → Type) (α : Type) := ExceptT CompileError m α

def SeekT (m : Type → Type) (α : Type) := SeekExceptT (StateT SeekCtx m) α

instance [hM : Applicative m] : Applicative (SeekT m) where
  map := fun f xM Γ => hM.map (fun ⟨x, _Δ⟩ => ⟨SeekExcept.map f x, Γ⟩) (xM Γ)
  pure := fun x Γ => hM.pure ⟨pure x, Γ⟩
  seq  := fun xM g Γ =>
    hM.seq (hM.map (fun ⟨x, Δ⟩ y => match x, y with
      | .ok f, ⟨.ok y, _Δ'⟩ => ⟨(pure ∘ f) y, Γ⟩
      | .error e₁, ⟨.error e₂, Δ'⟩ => ⟨.error
        (.sub Γ.1 Γ.2 (.and Γ.2 (.sub Δ.1 Δ.2 e₁) (.sub Δ'.1 Δ'.2 e₂))), Γ⟩
      | .error e₁, _ => ⟨.error (.sub Γ.1 Γ.2 (.sub Δ.1 Δ.2 e₁)), Γ⟩
      | _, ⟨.error e₂, Δ'⟩ => ⟨.error (.sub Γ.1 Γ.2 (.sub Δ'.1 Δ'.2 e₂)), Γ⟩) (xM Γ)) (fun x => g x Γ)

abbrev SeekM (α : Type) := SeekT Id α

instance [hM : Monad m] : Monad (SeekT m) where
  bind := fun xM f Γ =>
    hM.bind (xM Γ) (fun ⟨x, Δ⟩ => match x with
      | .ok x =>
        hM.map (fun ⟨x, Δ'⟩ => ⟨x.mapError
          (fun e₂ => (.sub Γ.1 Γ.2 (.sub Δ.1 Δ.2 (.sub Δ'.1 Δ'.2 e₂)))),
          Δ'⟩) (f x Δ)
      | .error e₁ => pure ⟨.error (.sub Γ.1 Γ.2 (.sub Δ.1 Δ.2 e₁)), Δ⟩)

instance [hM : Monad m] : MonadLift m (SeekT m) where
  monadLift := fun x Γ => hM.map (fun x => ⟨pure x, Γ⟩) x

instance [Monad m] : MonadReader SeekCtx (SeekT m) where
  read := fun Γ => pure ⟨.ok Γ, Γ⟩

def raise_error (e : SimpleError) : SeekM α := fun Γ => ⟨.error (e.with_ctx Γ.2), Γ⟩

set_option maxHeartbeats 10000000 in
open Dsl in
def Expr.as_value? (e : Expr) : SeekM (Value e) := do
  match cases_point_arity' e with
  | .inl ⟨_heq⟩ =>
    match e with
    | DCC ∗      => return .tintro
    | DCC 𝟙₂     => return .true
    | DCC 𝟘₂     => return .false
    | DCC 𝟚      => return .bool
    | DCC 𝟘      => return .bot
    | DCC 𝟙      => return .top
    | DCC Sort u => return .sort
    | DCC ((refl B) (& x)) => Value.refl₁ <$> B.as_value? <*> x.as_value?
    | DCC ((refl B) (& x) (& y)) => Value.refl₂ <$> B.as_value? <*> x.as_value? <*> y.as_value?
    | DCC ((Eql B) (& x)) => Value.eql₁ <$> B.as_value? <*> x.as_value?
    | DCC ((=' B) x) => Value.eq'₁ <$> B.as_value? <*> x.as_value?
    | DCC ((=' B) x y) => Value.eq'₂ <$> B.as_value? <*> x.as_value? <*> y.as_value?
    | DCC ((Λ A B x) y) => Value.curr₁ <$> A.as_value? <*> B.as_value? <*> x.as_value? <*> y.as_value?
    | DCC ((!Λ A B x) (& y)) => Value.curr'₁ <$> A.as_value? <*> B.as_value? <*> x.as_value? <*> y.as_value?
    | DCC ((𝟚.Rec motive x y) z) => Value.ind_bool₁ <$> motive.as_value? <*> x.as_value? <*> y.as_value? <*> z.as_value?
    | DCC ((𝟘.Rec motive) x) => Value.ind_bot₁ <$> motive.as_value? <*> x.as_value?
    | DCC ((Π B C) x) => Value.pi <$> B.as_value? <*> C.as_value? <*> x.as_value?
    | e => raise_error (.not_a_value e ())
  | .inr (.inl ⟨heq⟩) => do
    have h_dec : sizeOf (e.points.get ⟨0, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    let h₁ ← (e.points.get ⟨0, by grind⟩).as_value?
    return Value.points₁ heq h₁
  | .inr (.inr (.inl ⟨heq⟩)) => do
    have h_dec₁ : sizeOf (e.points.get ⟨0, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    have h_dec₂ : sizeOf (e.points.get ⟨1, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    let h₁ ← (e.points.get ⟨0, by grind⟩).as_value?
    let h₂ ← (e.points.get ⟨1, by grind⟩).as_value?
    return Value.points₂ heq h₁ h₂
  | .inr (.inr (.inr (.inl ⟨heq⟩))) => do
    have h_dec₁ : sizeOf (e.points.get ⟨0, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    have h_dec₂ : sizeOf (e.points.get ⟨1, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    have h_dec₃ : sizeOf (e.points.get ⟨2, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    let h₁ ← (e.points.get ⟨0, by grind⟩).as_value?
    let h₂ ← (e.points.get ⟨1, by grind⟩).as_value?
    let h₃ ← (e.points.get ⟨2, by grind⟩).as_value?
    return Value.points₃ heq h₁ h₂ h₃
  | .inr (.inr (.inr (.inr ⟨heq⟩))) => do
    have h_dec₁ : sizeOf (e.points.get ⟨0, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    have h_dec₂ : sizeOf (e.points.get ⟨1, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    have h_dec₃ : sizeOf (e.points.get ⟨2, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    have h_dec₄ : sizeOf (e.points.get ⟨3, by grind⟩) < sizeOf e := by
      cases e <;> (simp [points, Vector.get]; try grind)
    let h₁ ← (e.points.get ⟨0, by grind⟩).as_value?
    let h₂ ← (e.points.get ⟨1, by grind⟩).as_value?
    let h₃ ← (e.points.get ⟨2, by simp_all⟩).as_value?
    let h₄ ← (e.points.get ⟨3, by rw [heq]; simp⟩).as_value?
    return Value.points₄ heq h₁ h₂ h₃ h₄
termination_by sizeOf e

def Expr.is_ctx? (Γ : Expr) : SeekM (IsCtx Γ) :=
  open Dsl in match Γ with
  | DCC 𝟙 => return .unit
  | DCC (Σ A B) => IsCtx.sigma <$> A.is_ctx? <*> B.as_value?
  | DCC (! A) => .bang <$> A.is_ctx?
  | e => raise_error (.not_a_context e ())

def Expr.as_ctx? (Γ : Expr) : SeekM Ctx := do
  return ⟨Γ, ← Γ.is_ctx?⟩

def cc_var (Γ : Ctx) (n : ℕ) : Expr :=
  open Dsl in
  match Γ with
  | ⟨DCC 𝟙, .unit⟩ => DCC (Id 𝟙)
  | ⟨(DCC (Σ A B)), .sigma hΓ₀ _hv⟩ =>
    match n with
    | 0 => DCC (Snd B)
    | n + 1 => DCC (∘ #(cc_var ⟨A, hΓ₀⟩ n) (Fst B))
  | ⟨DCC (! A), .bang hΓ₀⟩ => DCC (∘ #(cc_var ⟨A, hΓ₀⟩ n) (! A))



/-open Dsl in
inductive Ty : Expr → Type
  | sort : Ty (DCC Sort u)
  | eq   : Ty (DCC (= A x y))
  | top  : Ty (DCC 𝟙)
  | bot  : Ty (DCC 𝟘)
  | -/

