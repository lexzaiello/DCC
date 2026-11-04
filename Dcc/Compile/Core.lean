import Dcc.Judge3
import Dcc.Ast
import Dcc.Ast.Share
import Dcc.Metatheory.Progress
import Dcc.Types

open Expr (Value Judge point_arity points reduce Red infer reduce_sound_fst reduce_norm_fst reduce_sound reduce_norm)
open Lean.Meta (MetaM)

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
⟦(λ x : A => M)⟧_Γ := (Λ Γ ⟦A⟧_Γ ⟦M⟧_(Σ Γ ⟦A⟧_Γ))

Nested Π binders:

If A does not depend on the context
and if M depends only on x, but not the context
----------------------------------
⟦(∀ x : A, M)⟧_(! Γ) := ((Π (`𝟙 (⟦A⟧_(! 𝟙) (& ∗))) (`𝟙 (⟦M⟧_(! (Σ 𝟙 ⟦A⟧_𝟙)) (& ∗)))) ∗)

How do we know if A in A → B depends on the context?
If there are free variables in the lean expression A.

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

inductive LConst where
  | true       : LConst
  | false      : LConst
  | true_intro : LConst
  | sort       : ℕ → LConst
  | bool_true  : LConst
  | bool_false : LConst
  | bool       : LConst
deriving Repr

abbrev VarIdx := ℕ

inductive LExpr where
  | bvar     : VarIdx → LExpr
  | const    : LConst → LExpr
  | app      : LExpr  → LExpr    → LExpr
  | lam      : LExpr  → LExpr    → LExpr
  | forallE  : LExpr  → LExpr    → LExpr
  | sigma    : (u v : Level)     → LExpr  → LExpr    → LExpr
  | sigma_mk : (u v : Level)     → (A B x y : LExpr) → LExpr
  | share_ty : (u : Level)       → (A : LExpr)   → LExpr
  | share    : (u : Level)       → (A x : LExpr) → LExpr
  | deref    : (u : Level)       → (A : LExpr)   → LExpr
deriving Repr

open Expr in
inductive TypedExpr : Type
  | mk : (e : Expr) → (ht : Judge e τ) → TypedExpr

open Dsl in
inductive IsCtx : Expr → Type
  | unit  : IsCtx (DCC 𝟙)
  | sigma : IsCtx A → Value B → IsCtx (DCC (Σ A B))
  | bang  : IsCtx A → IsCtx (DCC (! A))
deriving Repr

open Dsl in
def IsCtx.bang₀ (h : IsCtx (DCC (! A))) : IsCtx A :=
  match h with
  | .bang h => h

open Dsl in
def IsCtx.sigma₀ (h : IsCtx (DCC (Σ A B))) : IsCtx A :=
  match h with
  | .sigma h _=> h

def IsCtx.is_value (h : IsCtx e) : Value e :=
  match h with
  | .unit => .top
  | .sigma A B => .points₂ (by point_arity) A.is_value B
  | .bang h => .points₁ (by point_arity) h.is_value

inductive Ctx where
  | mk : (Γ : Expr) → (hΓ : IsCtx Γ) → Ctx
deriving Repr

inductive RawCompileError (α δ : Type) : Type
  | not_a_context     : (at_e : α) → (Δ    : Expr)       → (Γ : δ)             → RawCompileError α δ
  | sub               : (at_e : α) → (Γ : δ)             → RawCompileError α δ → RawCompileError α δ
  | and               : (at_e : α) → (Γ    : δ)          → RawCompileError α δ → RawCompileError α δ → RawCompileError α δ
  | not_a_value       : (at_e : α) → (v    : Expr)       → (Γ : δ)             → RawCompileError α δ
  | invalid_level     : (at_e : α) → (u    : Lean.Level) → (Γ : δ)             → RawCompileError α δ
  | unsupported       : (at_e : Lean.Expr) → (Γ : δ)             → RawCompileError α δ
  | unexpected        : (at_e : α) → (Γ : δ)             → RawCompileError α δ
  | type_error        : (at_e : α) → (at_e_tm : Expr)    → TypeError at_e_tm → (Γ : δ) → RawCompileError α δ
  | expected_binder   : (at_e : α) → (found_e : LExpr)   → RawCompileError α δ
  | expected_app      : (at_e : α) → (found_e : LExpr)   → RawCompileError α δ
  | expected_bang     : (at_e : α) → (found_e : Expr)    → (Γ : δ) → RawCompileError α δ
  | expected_sigma_tm : (at_e : α) → (found_e : LExpr)   → (Γ : δ) → RawCompileError α δ
deriving Repr

def RawCompileError.with_ctx (e : RawCompileError α Δ) (x : Γ) : RawCompileError α Γ :=
  match e with
  | .expected_bang at_e found_e _Γ => .expected_bang at_e found_e x
  | .not_a_context at_e Δ _ => .not_a_context at_e Δ x
  | .not_a_value at_e v _ => .not_a_context at_e v x
  | .sub x₀ _ x₁ => .sub x₀ x (x₁.with_ctx x)
  | .and at_e _ x₁ y₂ => .and at_e x (x₁.with_ctx x) (y₂.with_ctx x)
  | .invalid_level at_e u _ => .invalid_level at_e u x
  | .unsupported e _ => .unsupported e x
  | .unexpected e _ => .unexpected e x
  | .type_error at_e₀ at_e ε _Γ => .type_error at_e₀ at_e ε x
  | .expected_binder at_e found => .expected_binder at_e found
  | .expected_app at_e found => .expected_app at_e found
  | .expected_sigma_tm at_e found _Γ => .expected_sigma_tm at_e found x

def RawCompileError.with_source (e : RawCompileError α δ) (x : β) : RawCompileError β δ :=
  match e with
  | .expected_bang _at_e found_e Γ => .expected_bang x found_e Γ
  | .not_a_context _ Δ y => .not_a_context x Δ y
  | .not_a_value _ v y => .not_a_context x v y
  | .sub _ x₀ x₁ => .sub x x₀ (x₁.with_source x)
  | .and _ x₀ x₁ y₂ => .and x x₀ (x₁.with_source x) (y₂.with_source x)
  | .invalid_level _ u y => .invalid_level x u y
  | .unsupported x e => .unsupported x e
  | .unexpected _x e => .unexpected x e
  | .type_error _ at_e ε Γ  => .type_error x at_e ε Γ
  | .expected_binder _at_e found => .expected_binder x found
  | .expected_app _at_e found => .expected_app x found
  | .expected_sigma_tm _at_e found Γ => .expected_sigma_tm x found Γ

abbrev SimpleError  := RawCompileError Unit Unit
abbrev CompileError := RawCompileError LExpr Ctx

deriving instance Lean.ToExpr for Expr

abbrev CtxT (m : Type → Type v) (α : Type) := StateT Ctx m α

inductive SeekCtx : Type where
  | mk : (at_e : LExpr) → (Γ : Ctx) → SeekCtx
deriving Repr

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
        (.sub Γ.1 Γ.2 (.and Γ.1 Γ.2 (.sub Δ.1 Δ.2 e₁) (.sub Δ'.1 Δ'.2 e₂))), Γ⟩
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

def raise_error (e : SimpleError) : SeekM α := fun Γ => ⟨.error ((e.with_ctx Γ.2).with_source Γ.1), Γ⟩

def guard_type_error (ε : Except (TypeError e) α) : SeekM α :=
  fun Γ => ⟨ε.mapError (.type_error Γ.1 e · Γ.2), Γ⟩

theorem sizeOf_points (n : Fin (point_arity e)) : sizeOf (e.points.get n) < sizeOf e := by
  cases e
  <;> (
    simp only [point_arity] at n
    fin_cases n
    <;> (
      simp [points, Vector.get]
      try (grind)))

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
    | e => raise_error (.not_a_value () e ())
  | .inr (.inl ⟨heq⟩) => do
    have h_dec : sizeOf (e.points.get ⟨0, by grind⟩) < sizeOf e := sizeOf_points ⟨0, by grind⟩
    let h₁ ← (e.points.get ⟨0, by grind⟩).as_value?
    return Value.points₁ heq h₁
  | .inr (.inr (.inl ⟨heq⟩)) => do
    have h_dec₁ : sizeOf (e.points.get ⟨0, by grind⟩) < sizeOf e := sizeOf_points ⟨0, by grind⟩
    have h_dec₂ : sizeOf (e.points.get ⟨1, by grind⟩) < sizeOf e := sizeOf_points ⟨1, by grind⟩
    let h₁ ← (e.points.get ⟨0, by grind⟩).as_value?
    let h₂ ← (e.points.get ⟨1, by grind⟩).as_value?
    return Value.points₂ heq h₁ h₂
  | .inr (.inr (.inr (.inl ⟨heq⟩))) => do
    have h_dec₁ : sizeOf (e.points.get ⟨0, by grind⟩) < sizeOf e := sizeOf_points ⟨0, by grind⟩
    have h_dec₂ : sizeOf (e.points.get ⟨1, by grind⟩) < sizeOf e := sizeOf_points ⟨1, by grind⟩
    have h_dec₃ : sizeOf (e.points.get ⟨2, by grind⟩) < sizeOf e := sizeOf_points ⟨2, by grind⟩
    let h₁ ← (e.points.get ⟨0, by grind⟩).as_value?
    let h₂ ← (e.points.get ⟨1, by grind⟩).as_value?
    let h₃ ← (e.points.get ⟨2, by grind⟩).as_value?
    return Value.points₃ heq h₁ h₂ h₃
  | .inr (.inr (.inr (.inr ⟨heq⟩))) => do
    have h_dec₁ : sizeOf (e.points.get ⟨0, by grind⟩) < sizeOf e := sizeOf_points ⟨0, by grind⟩
    have h_dec₂ : sizeOf (e.points.get ⟨1, by grind⟩) < sizeOf e := sizeOf_points ⟨1, by grind⟩
    have h_dec₃ : sizeOf (e.points.get ⟨2, by grind⟩) < sizeOf e := sizeOf_points ⟨2, by grind⟩
    have h_dec₄ : sizeOf (e.points.get ⟨3, by grind⟩) < sizeOf e := sizeOf_points ⟨3, by grind⟩
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
  | e => raise_error (.not_a_context () e ())

def Expr.as_ctx? (Γ : Expr) : SeekM Ctx := do
  return ⟨Γ, ← Γ.is_ctx?⟩

def Lean.Level.to_nat (u : Lean.Level) : SeekM ℕ :=
  match u with
  | .zero => return 0
  | .succ n => .succ <$> n.to_nat
  | u => raise_error (.invalid_level () u ())

def Nat.to_level (u : ℕ) : Lean.Level :=
  match u with
  | 0 => .zero
  | u + 1 => u.to_level.succ

def LConst.of_expr (e : Lean.Expr) : SeekM LConst :=
  match e with
  | .const ``Bool [] => return .bool
  | .const ``Bool.true [] => return .bool_true
  | .const ``Bool.false [] => return .bool_false
  | .const ``True [] => return .true
  | .const ``False [] => return .false
  | .const ``True.intro [] => return .true_intro
  | .sort u => .sort <$> u.to_nat
  | e => fun Γ => ⟨.error (.unsupported e Γ.2), Γ⟩

def LConst.to_expr (e : LConst) : Lean.Expr :=
  match e with
  | .bool => .const ``Bool []
  | .bool_true => .const ``Bool.true []
  | .bool_false => .const ``Bool.false []
  | .true => .const ``True []
  | .false => .const ``False []
  | .true_intro => .const ``True.intro []
  | .sort u => .sort u.to_level

def LExpr.of_expr (e : Lean.Expr) : SeekM LExpr :=
  match e with
  | .app (.const ``Share [u]) A => .share_ty <$> u.to_nat <*> (LExpr.of_expr A)
  | .app (.const ``Share.deref [u]) A => .deref <$> u.to_nat <*> (LExpr.of_expr A)
  | .app (.app (.const ``Share.share [u]) A) x => .share <$> u.to_nat <*> (LExpr.of_expr A) <*> (LExpr.of_expr x)
  | .app (.app (.const ``Sigma [u, v]) A) B => .sigma <$> u.to_nat <*> v.to_nat <*> (LExpr.of_expr A) <*> (LExpr.of_expr B)
  | .app (.app (.app (.app (.const ``Sigma.mk [u, v]) A) B) x) y => .sigma_mk <$> u.to_nat <*> v.to_nat <*> (LExpr.of_expr A) <*> (LExpr.of_expr B)
    <*> (LExpr.of_expr x) <*> (LExpr.of_expr y)
  | .lam _ ty bdy _ => .lam <$> (LExpr.of_expr ty) <*> (LExpr.of_expr bdy)
  | .forallE _ ty bdy _ => .forallE <$> (LExpr.of_expr ty) <*> (LExpr.of_expr bdy)
  | .app x y => .app <$> (LExpr.of_expr x) <*> (LExpr.of_expr y)
  | .bvar n => return .bvar n
  | e => .const <$> (LConst.of_expr e)

def LExpr.to_expr (e : LExpr) : Lean.Expr :=
  match e with
  | .share_ty u A => .app (.const ``Share [u.to_level]) A.to_expr
  | .deref u A => .app (.const ``Share.deref [u.to_level]) A.to_expr
  | .share u A x => .app (.app (.const ``Share.share [u.to_level]) A.to_expr) x.to_expr
  | .sigma u v A B => .app (.app (.const ``Sigma [u.to_level, v.to_level]) A.to_expr) B.to_expr
  | .sigma_mk u v A B x y => .app (.app (.app (.app (.const ``Sigma.mk [u.to_level, v.to_level]) A.to_expr) B.to_expr) x.to_expr) y.to_expr
  | .lam ty bdy => .lam .anonymous ty.to_expr bdy.to_expr .default
  | .forallE ty bdy => .forallE .anonymous ty.to_expr bdy.to_expr .default
  | .app x y => .app x.to_expr y.to_expr
  | .bvar n => .bvar n
  | .const c => c.to_expr

open Dsl in
inductive AbstractVar : (Γ : Ctx) → (n : VarIdx) → (e' : Expr) → (Value e') → Type
  | init  : AbstractVar ⟨.top, .unit⟩ _n (DCC (Id 𝟙)) (.points₁ (by point_arity) .top)
  | succ  : AbstractVar ⟨A, hΓ₀⟩ n f hv₁
    → AbstractVar ⟨.sigma A B, .sigma hΓ₀ hv₂⟩ (n + 1) (DCC (∘ f (Fst B))) (.points₂ (by point_arity) hv₁ (.points₁ (by point_arity) hv₂))
  | zero  : AbstractVar ⟨.sigma A B, .sigma hΓ₀ hv₁⟩ 0 (DCC (Snd B)) (.points₁ (by point_arity) hv₁)
  | bang  : AbstractVar ⟨A, hΓ₀⟩ n f hv₁ → AbstractVar ⟨.bang A, .bang hΓ₀⟩ n (DCC (∘ f (! A))) (.points₂ (by point_arity) hv₁ (.points₁ (by point_arity) hΓ₀.is_value))
deriving Repr

open Dsl in
inductive AbstractConst : (Γ : Ctx) → (c : LConst) → (e' : Expr) → (Value e') → Type
  | bool       : AbstractConst Γ .bool (DCC (`#(Γ.1) 𝟚)) (.points₂ (by point_arity) Γ.2.is_value .bool)
  | bool_true  : AbstractConst Γ .bool_true (DCC (`#(Γ.1) 𝟙₂)) (.points₂ (by point_arity) Γ.2.is_value .true)
  | bool_false : AbstractConst Γ .bool_false (DCC (`#(Γ.1) 𝟘₂)) (.points₂ (by point_arity) Γ.2.is_value .false)
  | true       : AbstractConst Γ .true (DCC (`#(Γ.1) 𝟙)) (.points₂ (by point_arity) Γ.2.is_value .top)
  | false      : AbstractConst Γ .false (DCC (`#(Γ.1) 𝟘)) (.points₂ (by point_arity) Γ.2.is_value .bot)
  | true_intro : AbstractConst Γ .true_intro (DCC (`#(Γ.1) ∗)) (.points₂ (by point_arity) Γ.2.is_value .tintro)
  | sort       : AbstractConst Γ (.sort u) (DCC (`#(Γ.1) (Sort u))) (.points₂ (by point_arity) Γ.2.is_value .sort)
deriving Repr

open Dsl in
inductive Abstract : (Γ : Ctx) → (e : LExpr) → (e' : Expr) → (Value e') → Type
  | sigma_mk : Abstract ⟨Γ, hn_Γ₁.bang₀⟩ x x' hv₁
    → Abstract ⟨Γ, hn_Γ₁.bang₀⟩ y y' hv₂
    → Judge x' (DCC ((Π B₁ C₁) x₁))
    → Judge y' (DCC ((Π B₂ C₂) x₂))
    → (B₁ x₁) →ᵦ A
    → (C₁ x₁) →ᵦ B
    → (hv₃ : Value A)
    → (hv₄ : Value B)
    → Judge (DCC (∘ y' (Fst B))) (DCC ((Π (`𝟙 A₃) (`𝟙 (Π B₃ C₃))) ∗))
    → (hv₅ : Value C₃)
    → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.sigma_mk u v _A _B x y) (DCC (⟨,⟩C₃ x' (Λ A B (∘ y' (Fst B)))))
      (.points₃ (by point_arity) hv₅ hv₁
        (.points₃ (by point_arity) hv₃ hv₄
          (.points₂ (by change point_arity (DCC (∘ y' (Fst B))) = _; grind) hv₂
            (.points₁ (by change point_arity (DCC (Fst B)) = _; grind) hv₄))))
  | share    : Abstract ⟨Γ, hn_Γ₁.bang₀⟩ x x' hv₁ → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.share u A x) (DCC ($<> x')) (.points₁ (by point_arity) hv₁)
  | share_ty : Abstract ⟨Γ, hn_Γ₁.bang₀⟩ x x' hv₁ → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.share_ty u A) (DCC (!<> x')) (.points₁ (by point_arity) hv₁)
  | const    : AbstractConst Γ c e hv → Abstract Γ (.const c) e hv
  | var      : AbstractVar Γ n e hv   → Abstract Γ (.bvar n) e hv
  | sigma    : Abstract ⟨Γ, hn_Γ.bang₀⟩ A B' hv₁
    → Abstract ⟨DCC (Σ Γ B'), .sigma hn_Γ.bang₀ hv₁⟩ B C' hv₂
    → Abstract ⟨DCC (! Γ), hn_Γ⟩ (.sigma u v A B) (DCC (Σ' B' C')) (.points₂ (by point_arity) hv₁ hv₂)
  | lam      : Abstract ⟨Γ, h_Γ₁⟩ A A' hv₁
    → Abstract ⟨(DCC (! (Σ Γ A'))), .bang (.sigma h_Γ₁ hv₁)⟩ M M' hv₂
    → Abstract ⟨DCC (! Γ), .bang h_Γ₁⟩ (.lam A M) (DCC (!Λ Γ A' M')) (.points₃ (by point_arity) h_Γ₁.is_value hv₁ hv₂)
  -- If both the domain and codomain of a function type depend on the context,
  -- we should be a nested Π such that we can capture the context ((Π A' B') Γ)
  | forallE  : (Lean.Expr.hasLooseBVar A.to_expr 0 = true ∨ Lean.Expr.hasLooseBVar B.to_expr 1 = true)
    → Abstract ⟨(DCC (! Γ)), hn_Γ₁⟩ A A' hv₁
    → Abstract ⟨(DCC (! (Σ Γ A'))), (.bang (.sigma hn_Γ₁.bang₀ hv₁))⟩ B B' hv₂
    → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.forallE A B) (DCC (Π A' (!Λ Γ A' B'))) (.points₂ (by point_arity) hv₁ (.points₃ (by point_arity) hn_Γ₁.bang₀.is_value hv₁ hv₂))
  -- For arrows. Dom and cod don't depend, so make an arrow
  | forallE' : (Lean.Expr.hasLooseBVar A.to_expr 0 = false ∧ Lean.Expr.hasLooseBVar B.to_expr 0 = false)
    → Abstract ⟨(DCC (! 𝟙)), (.bang .unit)⟩ A A' hv₁
    → Abstract ⟨(DCC (! 𝟙)), (.bang .unit)⟩ B B' hv₂
    → (A' (& ∗)) →ᵦ A''
    → (B' (& ∗)) →ᵦ B''
    → (hv₃ : Value A'')
    → (hv₄ : Value B'')
    → Abstract Γ (.forallE A B) (DCC (→ A'' B'')) (.pi (.points₂ (by point_arity) .top hv₃) (.points₂ (by point_arity) .top (.points₂ (by point_arity) hv₃ hv₄)) .tintro)
  | app      : Abstract ⟨Γ, hn_Γ₁⟩ M M' hv₁
    → Abstract ⟨Γ, hn_Γ₁⟩ N N' hv₂
    → Judge M' (DCC ((Π B₁ C₁) x₁))
    → Judge N' (DCC ((Π B₂ C₂) x₂))
    → (B₁ x₁) →ᵦ A
    → (C₂ x₂) →ᵦ B
    → (hv₃ : Value A)
    → (hv₄ : Value B)
    → Judge (DCC (∘ N' (Fst (`Γ Γ)))) (DCC ((Π (`𝟙 A₃) (`𝟙 (Π B₃ C₃))) ∗))
    → (hv₅ : Value C₃)
    → Abstract ⟨DCC (! Γ), .bang hn_Γ₁⟩ (.app M N) (DCC (∘ (Eval A B M') (⟨,⟩C₃ (Id Γ) (Λ Γ (`Γ Γ) (∘ N' (Fst (`Γ Γ)))))))
      (.points₂ (by point_arity) (.points₃ (by point_arity) hv₃ hv₄ hv₁) (.points₃ (by point_arity) hv₅ (.points₁ (by change point_arity (DCC (Id Γ)) = _; point_arity) hn_Γ₁.is_value) (.points₃ (by change point_arity (DCC (Λ Γ (`Γ Γ) (∘ N' (Fst (`Γ Γ))))) = _; grind) hn_Γ₁.is_value (.points₂ (by change (DCC (`Γ Γ)).point_arity = _; grind) hn_Γ₁.is_value hn_Γ₁.is_value) (.points₂ (by change point_arity (DCC (∘ N' (Fst (`Γ Γ)))) =_; grind) hv₂ (.points₁ (by change (DCC (Fst (`Γ Γ))).point_arity = _; grind) (.points₂ (by change (DCC (`Γ Γ)).point_arity = _; grind) hn_Γ₁.is_value hn_Γ₁.is_value))))))
deriving Repr

open Dsl in
inductive CcConst : (e : LConst) → (e' : Expr) → (hv : Value e') → Type
  | bool_true  : CcConst .bool_true (DCC 𝟙₂) .true
  | bool_false : CcConst .bool_false (DCC 𝟘₂) .false
  | true       : CcConst .true (DCC 𝟙) .top
  | false      : CcConst .false (DCC 𝟘) .bot
  | true_intro : CcConst .true_intro (DCC ∗) .tintro
  | sort       : CcConst (.sort u) (DCC (Sort u)) .sort
deriving Repr

open Dsl in
inductive Cc : (e : LExpr) → (e' : Expr) → Type
  | const    : CcConst c e' hv → Cc (.const c) e'
  | share_ty : Cc A A' → Cc (.share_ty _u A) (DCC (! A'))
  | share    : Cc x x' → Cc (.share _u _A x) (DCC (& x'))
  | lam      : Abstract ⟨.top, .unit⟩ A A' hv₁
    → Abstract ⟨DCC (! (Σ 𝟙 A')), .bang (.sigma .unit hv₁)⟩ M M' hv₂
    → Cc (.lam (.share_ty u A) M) (DCC ((!Λ 𝟙 A' M') (& ∗)))
  | sigma    : Cc A A'
    → A' →ᵦ A''
    → (hv : Value A'')
    → Abstract ⟨DCC (! (Σ 𝟙 A'')), .bang (.sigma .unit hv)⟩ B B' hv₂
    → Cc (.sigma u v (.share_ty u₂ A) B) (DCC (Σ A'' ((!Λ 𝟙 A'' B') (& ∗))))
  | app      : Cc x x' → Cc y y' → Cc (.app x y) (DCC (x' y'))
  | forallE  : Cc A A'
    → Abstract ⟨DCC (! (Σ 𝟙 A')), .bang (.sigma .unit hv₁)⟩ B B' hv₂
    → Cc (.forallE (.share_ty u A) M) (DCC ((Π (`𝟙 A') (`𝟙 ((!Λ 𝟙 A' B') (& ∗)))) ∗))
deriving Repr

def Ctx.mk_var (Γ : Ctx) (n : VarIdx) : Σ (e : Expr) (hv : Value e), AbstractVar Γ n e hv :=
  match Γ with
  | ⟨.top, .unit⟩ => ⟨(open Dsl in (DCC (Id 𝟙))), _, .init⟩
  | ⟨.sigma A B, .sigma hΓ₀ _hv⟩ =>
    match n with
    | 0 => ⟨(open Dsl in (DCC (Snd B))), _, .zero⟩
    | n + 1 => ⟨(open Dsl in (DCC (∘ #((mk_var ⟨A, hΓ₀⟩ n).1) (Fst B)))), _, .succ (mk_var ⟨A, hΓ₀⟩ n).2.2⟩
  | ⟨.bang A, .bang hΓ₀⟩ => ⟨(open Dsl in (DCC (∘ #((mk_var ⟨A, hΓ₀⟩ n).1) (! A)))), _, .bang (mk_var ⟨A, hΓ₀⟩ n).2.2⟩

def mk_var (n : VarIdx) : SeekM (Σ (Γ : Ctx) (e : Expr) (hv : Value e), AbstractVar Γ n e hv) :=
  (fun x => ⟨x.2, Ctx.mk_var x.2 n⟩) <$> read

/-
Inspect the body of a ∀, λ, or Σ binder and update
the context internally as such
-/

def LExpr.binder_ty (e : LExpr) : SeekM LExpr := do
  match e with
  | .lam bty _bdy => pure bty
  | .forallE bty _bdy => pure bty
  | .sigma _ _ bty _bdy => pure bty
  | found => raise_error (.expected_binder () found)

def LExpr.sigl (e : LExpr) : SeekM LExpr := do
  match e with
  | .sigma_mk _ _ _ _ x _ => pure x
  | found => raise_error (.expected_sigma_tm () found ())

def LExpr.sigr (e : LExpr) : SeekM LExpr := do
  match e with
  | .sigma_mk _ _ _ _ y _ => pure y
  | found => raise_error (.expected_sigma_tm () found ())

def LExpr.binder_body (e : LExpr) : SeekM LExpr := do
  match e with
  | .lam _bty bdy => pure bdy
  | .forallE _bty bdy => pure bdy
  | .sigma _ _ _bty bdy => pure bdy
  | found => raise_error (.expected_binder () found)

def LExpr.congr_fun (e : LExpr) : SeekM LExpr := do
  match e with
  | .app x _y => pure x
  | found => raise_error (.expected_app () found)

def LExpr.congr_arg (e : LExpr) : SeekM LExpr := do
  match e with
  | .app _x y => pure y
  | found => raise_error (.expected_app () found)

/-
Replace the context and jump to a position in a lean term.
e.g.,

λ x : A => M

seek_to binder_ty does nothing, since the context is the same in A, but we get out the lean term A
seek_to binder_body changes the context to (Σ Γ A) and gives us M

Note that seek_to is only a mechanism for logging and reporting error messages,
and is not meant to be trusted fully.
-/
def seek_to (f : LExpr → SeekM LExpr) (Γ' : Ctx) : SeekM (Ctx × LExpr) := fun Γ =>
  let ⟨x, _y⟩ := f Γ.1 Γ
  ⟨x.map (⟨Γ', ·⟩), x.toOption.getD Γ.1, Γ'⟩

def binder_ty : SeekM LExpr := do
  (← read).1.binder_ty

def Ctx.mk_const (Γ : Ctx) (c : LConst) : Σ (e : Expr) (hv : Value e), AbstractConst Γ c e hv :=
  match c with
  | .true
  | .false
  | .true_intro
  | .sort u
  | .bool_true
  | .bool_false
  | .bool => ⟨_, _, by constructor⟩

def mk_const (c : LConst) : SeekM (Σ (Γ : Ctx) (e : Expr) (hv : Value e), AbstractConst Γ c e hv) :=
  (fun x => ⟨x.2, Ctx.mk_const x.2 c⟩) <$> read

def Ctx.abstract (Γ : Ctx) (e : LExpr) : SeekM (Σ (e' : Expr) (hv : Value e'), Abstract Γ e e' hv) := open Dsl in do
  match e with
  | .sigma_mk u v A B x y =>
    match Γ with
    | ⟨DCC (! Γ), hn_Γ⟩ =>
      let (⟨x', hv₁, h₁⟩, ⟨y', hv₂, h₂⟩) ← Prod.mk <$> (seek_to LExpr.sigl ⟨Γ, hn_Γ.bang₀⟩ *> Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ x)
        <*> (seek_to LExpr.sigr ⟨Γ, hn_Γ.bang₀⟩ *> Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ y)
      let (⟨τ₁, ht₁⟩, ⟨τ₂, ht₂⟩) ← Prod.mk <$> (guard_type_error x'.infer) <*> (guard_type_error y'.infer)
      match τ₁, τ₂ with
      | (DCC ((Π B₁ C₁) x₁)), (DCC ((Π B₂ C₂) x₂)) =>
        let (hv₃, hv₄) ← Prod.mk <$> (Expr.as_value? (reduce Red (DCC (B₁ x₁))).fst) <*> (Expr.as_value? (reduce Red (DCC (C₁ x₁))).fst)
        match ← (guard_type_error (DCC (∘ y' (Fst #((reduce Red (DCC (C₁ x₁))).fst)))).infer) with
        | ⟨(DCC ((Π (`𝟙 A₃) (`𝟙 (Π B₃ C₃))) ∗)), ht₃⟩ =>
          let hv₅ ← Expr.as_value? C₃
          return ⟨_, _, .sigma_mk h₁ h₂ ht₁ ht₂ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ hv₃ hv₄ ht₃ hv₅⟩
        | _ => raise_error (.unexpected () ())
      | x, y => raise_error (.unexpected () ())
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | .share u A x =>
    match Γ with
    | ⟨DCC (! Γ), hn_Γ⟩ =>
      return ⟨_, _, .share (← Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ x).2.2⟩
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | .share_ty u A =>
    match Γ with
    | ⟨DCC (! Γ), hn_Γ⟩ =>
      return ⟨_, _, .share_ty (← Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ A).2.2⟩
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | .const c =>
    let ⟨e, hv, h⟩ := Γ.mk_const c
    return ⟨e, hv, .const h⟩
  | .bvar n =>
    let ⟨e', hv, h⟩ := Γ.mk_var n
    return ⟨e', hv, .var h⟩
  | (.sigma u v A B) =>
    match Γ with
    | ⟨DCC (! Γ), hn_Γ⟩ => do
      let ⟨B', hv₁, h₁⟩ ← Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ A
      let ⟨C', hv₂, h₂⟩ ← Ctx.abstract ⟨(DCC (Σ Γ B')), .sigma hn_Γ.bang₀ hv₁⟩ B
      return ⟨DCC (Σ' B' C'), .points₂ (by point_arity) hv₁ hv₂, .sigma h₁ h₂⟩
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | (.lam A M) => sorry
  | (.forallE A B) => sorry
  | .app x y => sorry
  | e => raise_error (by sorry)

