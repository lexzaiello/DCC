import Dcc.Judge
import Dcc.Ast
import Dcc.Ast.Share
import Dcc.Metatheory.Progress
import Dcc.Types
import Lean.Elab

open Expr (Value Judge point_arity points reduce Red infer reduce_sound_fst reduce_norm_fst reduce_sound reduce_norm)
open Lean.Meta (MetaM)
open Lean.Elab
open Lean.Elab.Term
open Std (Format ToFormat)
open Std.ToFormat

/-
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
A context is either ⊤ or (Σ Γ Δ).

Nested Σ binders:

------------------------
⟦Σ A B⟧_(! Γ) := (Σ' ⟦A⟧_Γ ⟦B⟧_(Σ Γ ⟦A⟧_Γ))

-----------------------
⟦A × B⟧_(! Γ) := (Σ' ⟦A⟧_Γ (Λ Γ ⟦A⟧_Γ (∘ ⟦B⟧_(! ⊤) (`(Σ Γ ⟦A⟧_Γ) (& ∗)))))

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
⟦(∀ x : A, M)⟧_(! Γ) := ((Π (`⊤ (⟦A⟧_(! ⊤) (& ∗))) (`⊤ (⟦M⟧_(! (Σ ⊤ ⟦A⟧_⊤)) (& ∗)))) ∗)

How do we know if A in A → B depends on the context?
If there are free variables in the lean expression A.

If A does not depend on the context and M does not depend on the context
----------------------------------
⟦(∀ x : A, M)⟧_(! Γ) := ((Π (`⊤ (⟦A⟧_(! ⊤) (& ∗))) (`⊤ (`(⟦A⟧_(! ⊤) (& ∗)) (⟦M⟧_(! ⊤) (& ∗))))) ∗)

If either A or M depend on the context
------------------------------------- TODO: this should be split up for if M does not as well
⟦(∀ x : A, M)⟧_(! Γ) := (Π ⟦A⟧_(! Γ) (!Λ Γ ⟦A⟧_Γ ⟦M⟧_(! (Σ Γ ⟦A⟧_Γ))))

A and M can be checked to depend on the context by attempting compiling them with their respective
empty or nondependent contexts, then falling back.

Nested application:

⟦M⟧_Γ : ((Π B₁ C₁) x₁)    ⟦N⟧_Γ : ((Π B₂ C₂) x₂)
(B₁ x₁) →ᵦ A              (C₂ x) →ᵦ B

(∘ N (Fst (`Γ Γ))) : ((Π (`⊤ A₃) (`⊤ (Π B₃ C₃))) ∗)
---------------------------------------------
⟦M N⟧_(! Γ) := (∘ (Eval A B ⟦M⟧_Γ) (⟨,⟩C₃ (Id Γ) (Λ Γ (`Γ Γ) (∘ ⟦N⟧_Γ (Fst (`Γ Γ)))))

Constants:

--------------------
⟦Bool.True⟧_Γ := (`Γ True)

--------------------
⟦Bool.False⟧_Γ := (`Γ False)

--------------------
⟦True⟧_Γ := (`Γ ⊤)

--------------------
⟦False⟧_Γ := (`Γ ⊥)

--------------------
⟦True.intro⟧_Γ := (`Γ ∗)

--------------------
⟦Sort u⟧_Γ := (`Γ (Sort u))

Shared constants:

x is not also shared, and x is a constant
-----------------------------------------
⟦Share.share x⟧_(! Γ) := ($<> ⟦x⟧_Γ)

⟦A⟧_⊤ is not a bang
-----------------------------------------
⟦λ x : A => M⟧ := ((Λ ⊤ ⟦A⟧_⊤ ⟦M⟧_(Σ ⊤ ⟦A⟧_⊤)) ∗)

⟦A⟧_⊤ is a bang
-----------------------------------------
⟦λ x : A => M⟧ := ((!Λ ⊤ ⟦A⟧_(! ⊤) ⟦M⟧_(! (Σ ⊤ ⟦A⟧_(! ⊤)))) (& ∗))

--------------------
⟦(M N)⟧ := (⟦M⟧ ⟦N⟧)

Constants:

--------------------
⟦Bool.True⟧ := True

--------------------
⟦Bool.False⟧ := False

--------------------
⟦True⟧ := ⊤

--------------------
⟦False⟧ := ⊥

--------------------
⟦True.intro⟧ := ∗

--------------------
⟦Sort u⟧ := Sort u

Shared constants:

x is not also shared, and x is a constant
-----------------------------------------
⟦Share.share x⟧ := (& ⟦x⟧)

⟦A⟧_⊤ is not a bang
-----------------------------------------
⟦λ x : A => M⟧ := ((Λ ⊤ ⟦A⟧_⊤ ⟦M⟧_(Σ ⊤ ⟦A⟧_⊤)) ∗)

⟦A⟧_⊤ is a bang
-----------------------------------------
⟦λ x : A => M⟧ := ((!Λ ⊤ ⟦A⟧_(! ⊤) ⟦M⟧_(! (Σ ⊤ ⟦A⟧_(! ⊤)))) (& ∗))

--------------------
⟦(M N)⟧ := (⟦M⟧ ⟦N⟧)

Σ binders:

-------------------
⟦Σ A B⟧ := ((Σ' ⟦A⟧_⊤ (Λ ⊤ ⟦A⟧_⊤ ⟦B⟧_(Σ ⊤ ⟦A⟧_⊤))) (& ∗))

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
deriving Repr, Lean.ToExpr

def LConst.toFormat (e : LConst) : Format :=
  match e with
  | .true => "True"
  | .false => "False"
  | .true_intro => "True.intro"
  | .sort n => s!"Sort {n}"
  | .bool_true => s!"Bool.true"
  | .bool_false => s!"Bool.false"
  | .bool => s!"Bool"

instance : ToFormat LConst := ⟨LConst.toFormat⟩
instance : Repr LConst := ⟨fun x _ => LConst.toFormat x⟩

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
deriving Lean.ToExpr

def LExpr.toFormat (e : LExpr) : Format :=
  match e with
  | .bvar n => s!"{n}"
  | .const c => format c
  | .app x y => .paren (x.toFormat ++ " " ++ y.toFormat)
  | .lam A M => "λ " ++ .paren ("_ : " ++ A.toFormat) ++ " =>" ++ " " ++ M.toFormat
  | .forallE A M => "∀ _ : " ++ A.toFormat ++ "," ++ " " ++ M.toFormat
  | .sigma _u _v A B => "Σ " ++ A.toFormat ++ ", " ++ B.toFormat
  | .sigma_mk _u _v A B x y => .paren ("⟨" ++ x.toFormat ++ "," ++ y.toFormat ++ "⟩ :" ++ " " ++ "Σ " ++ A.toFormat ++ ", " ++ B.toFormat)
  | .share_ty _u A => "Shared " ++ A.toFormat
  | .share _u A x => .paren ("share " ++ x.toFormat ++ " :" ++ " " ++ "Shared " ++ A.toFormat)
  | .deref _u A => "deref " ++ A.toFormat

instance : ToFormat LExpr := ⟨LExpr.toFormat⟩
instance : Repr LExpr := ⟨fun x _ => LExpr.toFormat x⟩

open Expr in
inductive TypedExpr : Type
  | mk : (e : Expr) → (ht : Judge e τ) → TypedExpr

open Dsl in
inductive IsCtx : Expr → Type
  | unit  : IsCtx (DCC ⊤)
  | sigma : IsCtx A → Value B → IsCtx (DCC (Σ A B))
  | bang  : IsCtx A → IsCtx (DCC (! A))
deriving Repr

def IsCtx.toFormat (_hΓ : IsCtx Γ) : Format := Γ.toFormat

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

def Ctx.toFormat (c : Ctx) : Std.Format := c.1.toFormat

instance : ToFormat Ctx := ⟨Ctx.toFormat⟩

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
  | expected_sigma_ty : (at_e : α) → (found_e : LExpr)   → (Γ : δ) → RawCompileError α δ
  | expected_box      : (at_e : α) → (found_e : LExpr)   → (Γ : δ) → RawCompileError α δ
  | expected_bang_tm  : (at_e : α) → (found_e : LExpr)   → (Γ : δ) → RawCompileError α δ

def RawCompileError.toFormat [ToFormat α] [ToFormat δ] (e : RawCompileError α δ) : Format :=
  let footer (at_e : α) (Γ : δ) : Format := "at " ++ format Γ ++ ": " ++ format at_e
  match e with
  | .not_a_context at_e Δ Γ => "- expected a context, but found: " ++ (.nest 1 (format Δ))-- ++ .line ++ footer at_e Γ
  | .sub at_e Γ e => (toFormat e) ++ .line ++ footer at_e Γ
  | .and at_e Γ e₁ e₂ => (.nest 1 (toFormat e₁)) ++ .line ++ (.nest 1 (toFormat e₂)) ++ .line ++ footer at_e Γ
  | .not_a_value at_e v Γ => "- expected a value, but found: " ++ (.nest 1 (format v))-- ++ .line ++ footer at_e Γ
  | .invalid_level at_e u Γ => "- expected a level, but found: " ++ (.nest 1 (format u))-- ++ .line ++ footer at_e Γ
  | .unsupported at_e Γ => "- not supported: " ++ (.nest 1 (format at_e)) ++ .line ++ "at: " ++ (format Γ)
  | .type_error at_e at_e_tm e Γ => "- type error: " ++ (.nest 1 ((.nest 1 (format e)) ++ .line ++ "at: " ++ (format at_e_tm)))-- ++ .line ++ footer at_e Γ
  | .expected_binder at_e found_e => "- expected binder, but found: " ++ (.nest 1 (format found_e)) ++ .line ++ "at: " ++ (format at_e)
  | .expected_app at_e found_e => "- expected an app, but found: " ++ (.nest 1 (format found_e)) ++ .line ++ "at: " ++ (format at_e)
  | .expected_sigma_tm at_e found_e Γ => "- expected a Σ-term, but found: " ++ (.nest 1 (format found_e))-- ++ .line ++ footer at_e Γ
  | .expected_sigma_ty at_e found_e Γ => "- expected a Σ-type, but found: " ++ (.nest 1 (format found_e))-- ++ .line ++ footer at_e Γ
  | .expected_box at_e found_e Γ => "- expected a boxed value, but found: " ++ (.nest 1 (format found_e))-- ++ .line ++ footer at_e Γ
  | .expected_bang at_e found_e Γ => "- expected a bang type, but found: " ++ (.nest 1 (format found_e))-- ++ .line ++ footer at_e Γ
  | .expected_bang_tm at_e found_e Γ => "- expected a bang-type, but found: " ++ (.nest 1 (format found_e))-- ++ .line ++ footer at_e Γ
  | .unexpected at_e Γ => "- unexpected value" ++ .line ++ footer at_e Γ

instance [ToFormat α] [ToFormat δ] : ToFormat (RawCompileError α δ) := ⟨RawCompileError.toFormat⟩
instance [ToFormat α] [ToFormat δ] : Repr (RawCompileError α δ) := ⟨fun x _ => RawCompileError.toFormat x⟩

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
  | .expected_sigma_ty at_e found _Γ => .expected_sigma_ty at_e found x
  | .expected_box at_e found _Γ => .expected_box at_e found x
  | .expected_bang_tm at_e found _Γ => .expected_bang_tm at_e found x

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
  | .expected_sigma_ty _at_e found Γ => .expected_sigma_ty x found Γ
  | .expected_box _at_e found Γ => .expected_box x found Γ
  | .expected_bang_tm _at_e found Γ => .expected_bang_tm x found Γ

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
    | DCC True     => return .true
    | DCC False     => return .false
    | DCC Bool      => return .bool
    | DCC ⊥      => return .bot
    | DCC ⊤      => return .top
    | DCC Sort u => return .sort
    | DCC ((refl B) (& x)) => Value.refl₁ <$> B.as_value? <*> x.as_value?
    | DCC ((refl B) (& x) (& y)) => Value.refl₂ <$> B.as_value? <*> x.as_value? <*> y.as_value?
    | DCC ((Eql B) (& x)) => Value.eql₁ <$> B.as_value? <*> x.as_value?
    | DCC ((=' B) x) => Value.eq'₁ <$> B.as_value? <*> x.as_value?
    | DCC ((=' B) x y) => Value.eq'₂ <$> B.as_value? <*> x.as_value? <*> y.as_value?
    | DCC ((Λ A B x) y) => Value.curr₁ <$> A.as_value? <*> B.as_value? <*> x.as_value? <*> y.as_value?
    | DCC ((!Λ A B x) (& y)) => Value.curr'₁ <$> A.as_value? <*> B.as_value? <*> x.as_value? <*> y.as_value?
    | DCC ((Bool.Rec motive x y) z) => Value.ind_bool₁ <$> motive.as_value? <*> x.as_value? <*> y.as_value? <*> z.as_value?
    | DCC ((⊥.Rec motive) x) => Value.ind_bot₁ <$> motive.as_value? <*> x.as_value?
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
  | DCC ⊤ => return .unit
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
  | init  : AbstractVar ⟨.top, .unit⟩ _n (DCC (Id ⊤)) (.points₁ (by point_arity) .top)
  | succ  : AbstractVar ⟨A, hΓ₀⟩ n f hv₁
    → AbstractVar ⟨.sigma A B, .sigma hΓ₀ hv₂⟩ (n + 1) (DCC (∘ f (Fst B))) (.points₂ (by point_arity) hv₁ (.points₁ (by point_arity) hv₂))
  | zero  : AbstractVar ⟨.sigma A B, .sigma hΓ₀ hv₁⟩ 0 (DCC (Snd B)) (.points₁ (by point_arity) hv₁)
  | bang  : AbstractVar ⟨A, hΓ₀⟩ n f hv₁
    → AbstractVar ⟨.bang A, .bang hΓ₀⟩ n (DCC (∘ f (* A))) (.points₂ (by point_arity) hv₁ (.points₁ (by point_arity) hΓ₀.is_value))
deriving Repr

open Dsl in
inductive AbstractConst : (Γ : Ctx) → (c : LConst) → (e' : Expr) → (Value e') → Type
  | bool       : AbstractConst Γ .bool (DCC (`#(Γ.1) Bool)) (.points₂ (by point_arity) Γ.2.is_value .bool)
  | bool_true  : AbstractConst Γ .bool_true (DCC (`#(Γ.1) True)) (.points₂ (by point_arity) Γ.2.is_value .true)
  | bool_false : AbstractConst Γ .bool_false (DCC (`#(Γ.1) False)) (.points₂ (by point_arity) Γ.2.is_value .false)
  | true       : AbstractConst Γ .true (DCC (`#(Γ.1) ⊤)) (.points₂ (by point_arity) Γ.2.is_value .top)
  | false      : AbstractConst Γ .false (DCC (`#(Γ.1) ⊥)) (.points₂ (by point_arity) Γ.2.is_value .bot)
  | true_intro : AbstractConst Γ .true_intro (DCC (`#(Γ.1) ∗)) (.points₂ (by point_arity) Γ.2.is_value .tintro)
  | sort       : AbstractConst Γ (.sort u) (DCC (`#(Γ.1) (Sort u))) (.points₂ (by point_arity) Γ.2.is_value .sort)
deriving Repr

open Dsl in
def app_is_value (hn_Γ₁ : IsCtx (DCC (! Γ))) (hv₁ : Value M') (hv₂ : Value N') (hv₃ : Value A) (hv₄ : Value B) (hv₅ : Value C₃) : Value (DCC (∘ (Eval A B M') (⟨,⟩C₃ (Id Γ) (Λ Γ (`Γ Γ) (∘ N' (Fst (`Γ Γ))))))) :=
  (.points₂ (by point_arity) (.points₃ (by point_arity) hv₃ hv₄ hv₁) (.points₃ (by point_arity) hv₅ (.points₁ (by change point_arity (DCC (Id Γ)) = _; point_arity) hn_Γ₁.bang₀.is_value) (.points₃ (by change point_arity (DCC (Λ Γ (`Γ Γ) (∘ N' (Fst (`Γ Γ))))) = _; grind) hn_Γ₁.bang₀.is_value (.points₂ (by change (DCC (`Γ Γ)).point_arity = _; grind) hn_Γ₁.bang₀.is_value hn_Γ₁.bang₀.is_value) (.points₂ (by change point_arity (DCC (∘ N' (Fst (`Γ Γ)))) =_; grind) hv₂ (.points₁ (by change (DCC (Fst (`Γ Γ))).point_arity = _; grind) (.points₂ (by change (DCC (`Γ Γ)).point_arity = _; grind) hn_Γ₁.bang₀.is_value hn_Γ₁.bang₀.is_value))))))

open Dsl in
inductive Abstract : (Γ : Ctx) → (e : LExpr) → (e' : Expr) → (Value e') → Type
  | sigma_mk  : Abstract ⟨Γ, hn_Γ₁.bang₀⟩ x x' hv₁
    → Abstract ⟨Γ, hn_Γ₁.bang₀⟩ y y' hv₂
    → Judge x' (DCC ((Π B₁ C₁) x₁))
    → Judge y' (DCC ((Π B₂ C₂) x₂))
    → (B₁ x₁) →ᵦ A
    → (C₁ x₁) →ᵦ B
    → (hv₃ : Value A)
    → (hv₄ : Value B)
    → Judge (DCC (∘ y' (Fst B))) (DCC ((Π (`⊤ A₃) (`⊤ (Π B₃ C₃))) ∗))
    → (hv₅ : Value C₃)
    → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.sigma_mk u v _A _B x y) (DCC (⟨,⟩C₃ x' (Λ A B (∘ y' (Fst B)))))
      (.points₃ (by point_arity) hv₅ hv₁
        (.points₃ (by point_arity) hv₃ hv₄
          (.points₂ (by change point_arity (DCC (∘ y' (Fst B))) = _; grind) hv₂
            (.points₁ (by change point_arity (DCC (Fst B)) = _; grind) hv₄))))
  | share     : Abstract ⟨Γ, hn_Γ₁.bang₀⟩ x x' hv₁ → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.share u A x) (DCC ($<> x')) (.points₁ (by point_arity) hv₁)
  | share_ty  : Abstract ⟨Γ, hn_Γ₁.bang₀⟩ x x' hv₁ → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.share_ty u A) (DCC (!<> x')) (.points₁ (by point_arity) hv₁)
  | const     : AbstractConst Γ c e hv → Abstract Γ (.const c) e hv
  | var       : AbstractVar Γ n e hv   → Abstract Γ (.bvar n) e hv
  | sigma     : Abstract ⟨Γ, hn_Γ.bang₀⟩ A B' hv₁
    → Abstract ⟨DCC (Σ Γ B'), .sigma hn_Γ.bang₀ hv₁⟩ B C' hv₂
    → Abstract ⟨DCC (! Γ), hn_Γ⟩ (.sigma u v A B) (DCC (Σ' B' C')) (.points₂ (by point_arity) hv₁ hv₂)
  | lam       : Abstract ⟨Γ, h_Γ₁.bang₀⟩ A A' hv₁
    → Abstract ⟨(DCC (! (Σ Γ A'))), .bang (.sigma h_Γ₁.bang₀ hv₁)⟩ M M' hv₂
    → Abstract ⟨DCC (! Γ), h_Γ₁⟩ (.lam (.share_ty _u A) M) (DCC (!Λ Γ A' M')) (.points₃ (by point_arity) h_Γ₁.bang₀.is_value hv₁ hv₂)
  | lam'      : Abstract ⟨Γ, h_Γ₁⟩ A A' hv₁
    → Abstract ⟨(DCC (Σ Γ A')), (.sigma h_Γ₁ hv₁)⟩ M M' hv₂
    → Abstract ⟨DCC Γ, h_Γ₁⟩ (.lam A M) (DCC (Λ Γ A' M')) (.points₃ (by point_arity) h_Γ₁.is_value hv₁ hv₂)
  -- If both the domain and codomain of a function type depend on the context,
  -- we should be a nested Π such that we can capture the context ((Π A' B') Γ)
  | forallE   : (Lean.Expr.hasLooseBVar (LExpr.share_ty _u A).to_expr 0 = true ∨ Lean.Expr.hasLooseBVar B.to_expr 1 = true)
    → Abstract ⟨(DCC (! Γ)), hn_Γ₁⟩ A A' hv₁
    → Abstract ⟨(DCC (! (Σ Γ A'))), (.bang (.sigma hn_Γ₁.bang₀ hv₁))⟩ B B' hv₂
    → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.forallE (.share_ty _u A) B) (DCC (Π A' (!Λ Γ A' B'))) (.points₂ (by point_arity) hv₁ (.points₃ (by point_arity) hn_Γ₁.bang₀.is_value hv₁ hv₂))
  | forallE'' : (Lean.Expr.hasLooseBVar A.to_expr 0 = true ∨ Lean.Expr.hasLooseBVar B.to_expr 1 = true)
    → Abstract ⟨(DCC Γ), hn_Γ₁⟩ A A' hv₁
    → Abstract ⟨(DCC (Σ Γ A')), (.sigma hn_Γ₁ hv₁)⟩ B B' hv₂
    → Abstract ⟨DCC Γ, hn_Γ₁⟩ (.forallE A B) (DCC (Π A' (Λ Γ A' B'))) (.points₂ (by point_arity) hv₁ (.points₃ (by point_arity) hn_Γ₁.is_value hv₁ hv₂))
  -- For arrows. Dom and cod don't depend, so make an arrow
  | forallE'  : (Lean.Expr.hasLooseBVar A.to_expr 0 = false ∧ Lean.Expr.hasLooseBVar B.to_expr 1 = false)
    → Abstract ⟨(DCC (! ⊤)), (.bang .unit)⟩ A A' hv₁
    → Abstract ⟨(DCC (! ⊤)), (.bang .unit)⟩ B B' hv₂
    → (A' (& ∗)) →ᵦ A''
    → (B' (& ∗)) →ᵦ B''
    → (hv₃ : Value A'')
    → (hv₄ : Value B'')
    → Abstract Γ (.forallE A B) (DCC (`#(Γ.1) (→ A'' B''))) (.points₂ (by point_arity) Γ.2.is_value (.pi (.points₂ (by point_arity) .top hv₃) (.points₂ (by point_arity) .top (.points₂ (by point_arity) hv₃ hv₄)) .tintro))
  | app       : Abstract ⟨Γ, hn_Γ₁.bang₀⟩ M M' hv₁
    → Abstract ⟨Γ, hn_Γ₁.bang₀⟩ N N' hv₂
    → Judge M' (DCC ((Π B₁ C₁) x₁))
    → Judge N' (DCC ((Π B₂ C₂) x₂))
    → (B₁ x₁) →ᵦ A
    → (C₂ x₂) →ᵦ B
    → (hv₃ : Value A)
    → (hv₄ : Value B)
    → Judge (DCC (Λ Γ (`Γ Γ) (∘ N' (Fst (`Γ Γ))))) (DCC ((Π B₃ C₃) x₃))
    → (C₃ x₃ (hole C₃.max_hole.succ)) →ᵦ ((Π B₄ C₄) x₄)
    → (hv₅ : Value C₄)
    → Abstract ⟨DCC (! Γ), hn_Γ₁⟩ (.app M N) (DCC (∘ (Eval A B M') (⟨,⟩C₄ (Id Γ) (Λ Γ (`Γ Γ) (∘ N' (Fst (`Γ Γ))))))) (app_is_value hn_Γ₁ hv₁ hv₂ hv₃ hv₄ hv₅)
deriving Repr

open Dsl in
inductive CcConst : (e : LConst) → (e' : Expr) → (hv : Value e') → Type
  | bool       : CcConst .bool (DCC Bool) .bool
  | bool_true  : CcConst .bool_true (DCC True) .true
  | bool_false : CcConst .bool_false (DCC False) .false
  | true       : CcConst .true (DCC ⊤) .top
  | false      : CcConst .false (DCC ⊥) .bot
  | true_intro : CcConst .true_intro (DCC ∗) .tintro
  | sort       : CcConst (.sort u) (DCC (Sort u)) .sort
deriving Repr

open Dsl in
inductive Cc : (e : LExpr) → (e' : Expr) → Type
  | sigma_mk : Abstract ⟨.bang .top, .bang .unit⟩ (.sigma_mk u v A B x y) e' hv → Cc (.sigma_mk u v A B x y) (DCC (e' (& ∗)))
  | const    : CcConst c e' hv → Cc (.const c) e'
  | share_ty : Cc A A' → Cc (.share_ty _u A) (DCC (! A'))
  | share    : Cc x x' → Cc (.share _u _A x) (DCC (& x'))
  | lam      : Abstract ⟨.top, .unit⟩ A A' hv₁
    → Abstract ⟨DCC (! (Σ ⊤ A')), .bang (.sigma .unit hv₁)⟩ M M' hv₂
    → Cc (.lam (.share_ty u A) M) (DCC ((!Λ ⊤ A' M') (& ∗)))
  | lam'     : Abstract ⟨.top, .unit⟩ A A' hv₁
    → Abstract ⟨DCC (Σ ⊤ A'), (.sigma .unit hv₁)⟩ M M' hv₂
    → Cc (.lam A M) (DCC ((Λ ⊤ A' M') ∗))
  | sigma    : Cc A A'
    → A' →ᵦ A''
    → (hv : Value A'')
    → Abstract ⟨DCC (! (Σ ⊤ A'')), .bang (.sigma .unit hv)⟩ B B' hv₂
    → Cc (.sigma u v (.share_ty u₂ A) B) (DCC (Σ A'' ((!Λ ⊤ A'' B') (& ∗))))
  | app      : Cc x x' → Cc y y' → Cc (.app x y) (DCC (x' y'))
  | forallE  : Cc A A'
    → A' →ᵦ A''
    → (hv₁ : Value A'')
    → Abstract ⟨DCC (! (Σ ⊤ A'')), (.bang (.sigma .unit hv₁))⟩ B B' hv₂
    → Cc (.forallE (.share_ty u A) B) (DCC ((Π (`⊤ A'') (`⊤ ((!Λ ⊤ A'' B') (& ∗)))) ∗))
  | forallE'  : Cc A A'
    → A' →ᵦ A''
    → (hv₁ : Value A'')
    → Abstract ⟨DCC (Σ ⊤ A''), (.sigma .unit hv₁)⟩ B B' hv₂
    → Cc (.forallE A B) (DCC ((Π (`⊤ A'') (`⊤ ((Λ ⊤ A'' B') ∗))) ∗))
deriving Repr

def Ctx.mk_var (Γ : Ctx) (n : VarIdx) : Σ (e : Expr) (hv : Value e), AbstractVar Γ n e hv :=
  match Γ with
  | ⟨.top, .unit⟩ => ⟨(open Dsl in (DCC (Id ⊤))), _, .init⟩
  | ⟨.sigma A B, .sigma hΓ₀ _hv⟩ =>
    match n with
    | 0 => ⟨(open Dsl in (DCC (Snd B))), _, .zero⟩
    | n + 1 => ⟨(open Dsl in (DCC (∘ #((mk_var ⟨A, hΓ₀⟩ n).1) (Fst B)))), _, .succ (mk_var ⟨A, hΓ₀⟩ n).2.2⟩
  | ⟨.bang A, .bang hΓ₀⟩ => ⟨(open Dsl in (DCC (∘ #((mk_var ⟨A, hΓ₀⟩ n).1) (* A)))), _, .bang (mk_var ⟨A, hΓ₀⟩ n).2.2⟩

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

def LExpr.box₀ (e : LExpr) : SeekM LExpr := do
  match e with
  | .share _ _ x => pure x
  | found => raise_error (.expected_box () found ())

def LExpr.bang₀ (e : LExpr) : SeekM LExpr := do
  match e with
  | .share_ty _ x => pure x
  | found => raise_error (.expected_bang_tm () found ())

def LExpr.sigma₀ (e : LExpr) : SeekM LExpr := do
  match e with
  | .sigma _ _ A _ => pure A
  | found => raise_error (.expected_sigma_ty () found ())

def LExpr.sigma₁ (e : LExpr) : SeekM LExpr := do
  match e with
  | .sigma _ _ A _ => pure A
  | found => raise_error (.expected_sigma_ty () found ())

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
def seek_to (e' : LExpr) (Γ' : Ctx) (fX : SeekM α) : SeekM α := fun Γ =>
  ⟨(fX.run ⟨e', Γ'⟩).1, Γ⟩

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
      let (⟨x', hv₁, h₁⟩, ⟨y', hv₂, h₂⟩) ← Prod.mk <$> (seek_to x ⟨Γ, hn_Γ.bang₀⟩ (Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ x))
        <*> (seek_to y ⟨Γ, hn_Γ.bang₀⟩ (Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ y))
      let (⟨τ₁, ht₁⟩, ⟨τ₂, ht₂⟩) ← Prod.mk <$> (guard_type_error x'.infer) <*> (guard_type_error y'.infer)
      match τ₁, τ₂ with
      | (DCC ((Π B₁ C₁) x₁)), (DCC ((Π B₂ C₂) x₂)) =>
        let (hv₃, hv₄) ← Prod.mk <$> (Expr.as_value? (reduce Red (DCC (B₁ x₁))).fst) <*> (Expr.as_value? (reduce Red (DCC (C₁ x₁))).fst)
        match ← (guard_type_error (DCC (∘ y' (Fst #((reduce Red (DCC (C₁ x₁))).fst)))).infer) with
        | ⟨(DCC ((Π (`⊤ A₃) (`⊤ (Π B₃ C₃))) ∗)), ht₃⟩ =>
          let hv₅ ← Expr.as_value? C₃
          return ⟨_, _, .sigma_mk h₁ h₂ ht₁ ht₂ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ hv₃ hv₄ ht₃ hv₅⟩
        | _ => raise_error (.unexpected () ())
      | x, y => raise_error (.unexpected () ())
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | .share u A x =>
    match Γ with
    | ⟨DCC (! Γ), hn_Γ⟩ =>
      return ⟨_, _, .share (← seek_to x ⟨Γ, hn_Γ.bang₀⟩ (Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ x)).2.2⟩
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | .share_ty u A =>
    match Γ with
    | ⟨DCC (! Γ), hn_Γ⟩ =>
      return ⟨_, _, .share_ty (← seek_to A ⟨Γ, hn_Γ.bang₀⟩ (Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ A)).2.2⟩
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
      let ⟨B', hv₁, h₁⟩ ← (seek_to A ⟨Γ, hn_Γ.bang₀⟩ (Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ A))
      let ⟨C', hv₂, h₂⟩ ← (seek_to B ⟨(DCC (Σ Γ B')), .sigma hn_Γ.bang₀ hv₁⟩ (Ctx.abstract ⟨(DCC (Σ Γ B')), .sigma hn_Γ.bang₀ hv₁⟩ B))
      return ⟨DCC (Σ' B' C'), .points₂ (by point_arity) hv₁ hv₂, .sigma h₁ h₂⟩
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | (.lam (.share_ty _u A) M) =>
    match Γ with
    | ⟨DCC (! Γ), hn_Γ⟩ => do
      let ⟨A', hv₁, h₁⟩ ← (seek_to A ⟨Γ, hn_Γ.bang₀⟩ (Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ A))
      let ⟨M', hv₂, h₂⟩ ← (seek_to M ⟨(DCC (! (Σ Γ A'))), .bang (.sigma hn_Γ.bang₀ hv₁)⟩ (Ctx.abstract ⟨(DCC (! (Σ Γ A'))), .bang (.sigma hn_Γ.bang₀ hv₁)⟩ M))
      return ⟨_, _, .lam h₁ h₂⟩
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | (.lam A M) =>
    match Γ with
    | ⟨Γ, hn_Γ⟩ => do
      let ⟨A', hv₁, h₁⟩ ← (seek_to A ⟨Γ, hn_Γ⟩ (Ctx.abstract ⟨Γ, hn_Γ⟩ A))
      let ⟨M', hv₂, h₂⟩ ← (seek_to M ⟨(DCC (Σ Γ A')), (.sigma hn_Γ hv₁)⟩ (Ctx.abstract ⟨(DCC (Σ Γ A')), (.sigma hn_Γ hv₁)⟩ M))
      return ⟨_, _, .lam' h₁ h₂⟩
  | (.forallE A B) =>
    if heq₁ : (Lean.Expr.hasLooseBVar A.to_expr 0 = false ∧ Lean.Expr.hasLooseBVar B.to_expr 1 = false) then
      let ⟨A', hv₁, h₁⟩ ← (seek_to A ⟨(DCC (! ⊤)), (.bang .unit)⟩ (Ctx.abstract ⟨(DCC (! ⊤)), (.bang .unit)⟩ A))
      let ⟨B', hv₂, h₂⟩ ← (seek_to B ⟨(DCC (! ⊤)), (.bang .unit)⟩ (Ctx.abstract ⟨(DCC (! ⊤)), (.bang .unit)⟩ B))
      let hv₃ ← Expr.as_value? (reduce Red (DCC (A' (& ∗)))).fst
      let hv₄ ← Expr.as_value? (reduce Red (DCC (B' (& ∗)))).fst
      return ⟨_, _, .forallE' heq₁ h₁ h₂ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ hv₃ hv₄⟩
    else
      have heq₂ : (Lean.Expr.hasLooseBVar A.to_expr 0 = true ∨ Lean.Expr.hasLooseBVar B.to_expr 1 = true) := by
        grind
      match A, Γ with
      | .share_ty _u A, ⟨DCC (! Γ), hn_Γ⟩ =>
        let ⟨A', hv₁, h₁⟩ ← (seek_to A ⟨(DCC (! Γ)), hn_Γ⟩ (Ctx.abstract ⟨(DCC (! Γ)), hn_Γ⟩ A))
        let ⟨B', hv₂, h₂⟩ ← (seek_to B ⟨(DCC (! (Σ Γ A'))), (.bang (.sigma hn_Γ.bang₀ hv₁))⟩ (Ctx.abstract ⟨(DCC (! (Σ Γ A'))), (.bang (.sigma hn_Γ.bang₀ hv₁))⟩ B))
        return ⟨_, _, .forallE heq₂ h₁ h₂⟩
      | A, ⟨Γ, hn_Γ⟩ =>
        let ⟨A', hv₁, h₁⟩ ← (seek_to A ⟨(DCC Γ), hn_Γ⟩ (Ctx.abstract ⟨(DCC Γ), hn_Γ⟩ A))
        let ⟨B', hv₂, h₂⟩ ← (seek_to B ⟨(DCC (Σ Γ A')), (.sigma hn_Γ hv₁)⟩ (Ctx.abstract ⟨(DCC (Σ Γ A')), (.sigma hn_Γ hv₁)⟩ B))
        return ⟨_, _, .forallE'' heq₂ h₁ h₂⟩
  | .app x y =>
    match Γ with
    | ⟨DCC (! Γ), hn_Γ⟩ =>
      let (⟨x', hv₁, h₁⟩, ⟨y', hv₂, h₂⟩) ← Prod.mk <$> (seek_to x ⟨Γ, hn_Γ.bang₀⟩ (Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ x))
        <*> (seek_to y ⟨Γ, hn_Γ.bang₀⟩ (Ctx.abstract ⟨Γ, hn_Γ.bang₀⟩ y))
      let (⟨τ₁, ht₁⟩, ⟨τ₂, ht₂⟩) ← Prod.mk <$> (seek_to x ⟨Γ, hn_Γ.bang₀⟩ (guard_type_error x'.infer)) <*> (seek_to y ⟨Γ, hn_Γ.bang₀⟩ (guard_type_error y'.infer))
      match τ₁, τ₂ with
      | (DCC ((Π B₁ C₁) x₁)), (DCC ((Π B₂ C₂) x₂)) =>
        let (hv₃, hv₄) ← Prod.mk <$> (seek_to x ⟨Γ, hn_Γ.bang₀⟩ (Expr.as_value? (reduce Red (DCC (B₁ x₁))).fst)) <*> (seek_to y ⟨Γ, hn_Γ.bang₀⟩ (Expr.as_value? (reduce Red (DCC (C₂ x₂))).fst))
        match ← (guard_type_error (DCC (Λ Γ (`Γ Γ) (∘ y' (Fst (`Γ Γ))))).infer) with
        | ⟨(DCC ((Π B₃ C₃) x₃)), ht₃⟩ =>
          match heq : Expr.reduce_all (DCC (C₃ x₃ (hole C₃.max_hole.succ))) with
          | DCC ((Π B₄ C₄) x₄) =>
            let hv₅ ← Expr.as_value? C₄
            return ⟨_, _, .app h₁ h₂ ht₁ ht₂ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ hv₃ hv₄ ht₃ (Expr.reduce_reduces heq) hv₅⟩
          | x => raise_error (.unexpected () ())
        | _ => raise_error (.unexpected () ())
      | x, y => raise_error (.unexpected () ())
    | ⟨Γ, hn_Γ⟩ => raise_error (.expected_bang () Γ ())
  | e => raise_error (.unexpected () ())

def cc_const (c : LConst) : Σ (e' : Expr) (hv : Value e'), CcConst c e' hv :=
  match c with
  | .bool_true => ⟨_, _, .bool_true⟩
  | .bool_false => ⟨_, _, .bool_false⟩
  | .bool => ⟨_, _, .bool⟩
  | .sort _u => ⟨_, _, .sort⟩
  | .true => ⟨_, _, .true⟩
  | .false => ⟨_, _, .false⟩
  | .true_intro => ⟨_, _, .true_intro⟩

/-
TODO: need to add seek_to's for error messasges
-/

def cc (e : LExpr) : SeekM (Σ (e' : Expr), Cc e e') := open Dsl in do
  match e with
  | .const c => return ⟨(cc_const c).1, .const (cc_const c).2.2⟩
  | .share_ty _u A => (⟨_, .share_ty ·.2⟩) <$> (cc A)
  | .share _u _A x => (⟨_, .share ·.2⟩) <$> (cc x)
  | .lam (.share_ty _u A) M =>
    let ⟨A', hv₁, h₁⟩   ← (seek_to A ⟨.top, .unit⟩ (Ctx.abstract ⟨.top, .unit⟩ A))
    let ⟨_M', _hv₂, h₂⟩ ← (seek_to M ⟨(DCC (! (Σ ⊤ A'))), .bang (.sigma .unit hv₁)⟩ (Ctx.abstract ⟨(DCC (! (Σ ⊤ A'))), .bang (.sigma .unit hv₁)⟩ M))
    return ⟨_, .lam h₁ h₂⟩
  | .lam A M =>
    let ⟨A', hv₁, h₁⟩   ← (seek_to A ⟨.top, .unit⟩ (Ctx.abstract ⟨.top, .unit⟩ A))
    let ⟨_M', _hv₂, h₂⟩ ← (seek_to M ⟨(DCC (Σ ⊤ A')), (.sigma .unit hv₁)⟩ (Ctx.abstract ⟨(DCC (Σ ⊤ A')), (.sigma .unit hv₁)⟩ M))
    return ⟨_, .lam' h₁ h₂⟩
  | .sigma _u _v (.share_ty _u₂ A) B =>
    let ⟨A', h₁⟩ ← (seek_to A ⟨.top, .unit⟩ (cc A))
    let hv₁ ← Expr.as_value? (reduce Red A').fst
    let ⟨_M', _hv₂, h₂⟩ ← (seek_to B ⟨DCC (! (Σ ⊤ #((reduce Red A').fst))), .bang (.sigma .unit hv₁)⟩ (Ctx.abstract ⟨DCC (! (Σ ⊤ #((reduce Red A').fst))), .bang (.sigma .unit hv₁)⟩ B))
    return ⟨_, .sigma h₁ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ hv₁ h₂⟩
  | .app x y =>
    (fun ⟨_x', h₁⟩ ⟨_y', h₂⟩ => ⟨_, .app h₁ h₂⟩) <$> (seek_to x ⟨(DCC (! ⊤)), .bang .unit⟩ (cc x)) <*> (seek_to y ⟨(DCC (! ⊤)), .bang .unit⟩ (cc y))
  | .forallE (.share_ty _u A) B =>
    let ⟨A', h₁⟩ ← (seek_to A ⟨.top, .unit⟩ (cc A))
    let hv₁ ← Expr.as_value? (reduce Red A').fst
    let ⟨_B', _hv₂, h₂⟩ ← (seek_to B ⟨DCC (! (Σ ⊤ #((reduce Red A').fst))), (.bang (.sigma .unit hv₁))⟩ (Ctx.abstract ⟨DCC (! (Σ ⊤ #((reduce Red A').fst))), (.bang (.sigma .unit hv₁))⟩ B))
    return ⟨_, .forallE h₁ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ hv₁ h₂⟩
  | .forallE A B =>
    let ⟨A', h₁⟩ ← (seek_to A ⟨.top, .unit⟩ (cc A))
    let hv₁ ← Expr.as_value? (reduce Red A').fst
    let ⟨_B', _hv₂, h₂⟩ ← (seek_to B ⟨DCC (Σ ⊤ #((reduce Red A').fst)), (.sigma .unit hv₁)⟩ (Ctx.abstract ⟨DCC (Σ ⊤ #((reduce Red A').fst)), (.sigma .unit hv₁)⟩ B))
    return ⟨_, .forallE' h₁ ⟨reduce_sound_fst rfl, reduce_norm_fst rfl⟩ hv₁ h₂⟩
  | .sigma_mk u v A B x y => (fun ⟨_, _, x⟩ => ⟨_, .sigma_mk x⟩) <$> (Ctx.abstract ⟨.bang .top, .bang .unit⟩ (.sigma_mk u v A B x y))
  | _e => raise_error (.unexpected () ())

def cc' (e : LExpr) : Except CompileError (Σ (e' : Expr), Cc e e') := ((cc e).run ⟨e, .top, .unit⟩).1

/-
The number of times any context in a lean term is used is bounded by
the number of applications and Σ's in the term.

This is highly inefficient.

After calculating this bound "n + 1", we Share.share all top-level arguments
n times and map each binder's type τ to (Share^[(n + 1)] τ)
-/

def LExpr.is_free (e : LExpr) (lv : ℕ) : Bool :=
  match e with
  | .bvar n => n ≠ lv
  | .app x y => (x.is_free lv) ∧ (y.is_free lv)
  | .deref _ x => x.is_free lv
  | .share _ A x => A.is_free lv ∧ x.is_free lv
  | .share_ty _ A => A.is_free lv
  | .sigma_mk _ _ _ _ x y => x.is_free lv ∧ y.is_free lv
  | .sigma _ _ A B => A.is_free lv ∧ B.is_free lv
  | .forallE A bdy => A.is_free lv ∧ bdy.is_free lv.succ
  | .lam A bdy => A.is_free lv ∧ bdy.is_free lv.succ
  | _ => true

/-
Note: this operation is destructive, since it removes
universe levels and type arguments to Shared.
-/
def LExpr.shared_n (n : ℕ) (e : LExpr) : LExpr :=
  match n with
  | .zero => e
  | .succ n => .share_ty 0 (e.shared_n n)

def LExpr.n_uses (e : LExpr) (lv : ℕ) : ℕ :=
  match e with
  | .app x y => if (is_free (.app x y) lv) then 0 else (max (x.n_uses lv) (y.n_uses lv)).succ
  | .deref _ x => x.n_uses lv
  | .share _ _A x => x.n_uses lv
  | .share_ty _ A => A.n_uses lv
  | .sigma_mk _ _ _ _ x y => max (x.n_uses lv) (y.n_uses lv)
  | .sigma _ _ A B => max (A.n_uses lv) (B.n_uses lv)
  | .forallE A bdy => max (A.n_uses lv) (bdy.n_uses lv.succ)
  | .lam A bdy => max (A.n_uses lv) (bdy.n_uses lv.succ)
  | _ => 0

/-
Sharing with context.
The first time a variable is introduced,
it is shared the number of times it occurs under the binderu
but always at least once if it introduced the first time.

If it already exists in the context, it is not shared.

We also output the context so we can determine how many times
to share arguments.

TODO: auto share values from infer on M in M N.
-/
def LExpr.share_ty_lean (e : LExpr) : LExpr :=
  match e with
  | .lam bty bdy =>
    let n := (bdy.n_uses 0)
    let bdy' := bdy.share_ty_lean
    .lam (bty.shared_n n) bdy'
  | .forallE bty bdy =>
    .forallE (bty.shared_n (bdy.n_uses 0)) bdy.share_ty_lean
  | .sigma u v A B => .sigma u v (A.shared_n (B.n_uses 0)) B.share_ty_lean
  | .sigma_mk u v A B x y => .sigma_mk u v A.share_ty_lean B.share_ty_lean x.share_ty_lean y.share_ty_lean
  | .app x y => .app x.share_ty_lean y.share_ty_lean
  | e => e

def LExpr.arg_binder (e : LExpr) (nth_arg : ℕ) : Option LExpr :=
  match nth_arg with
  | .zero => pure e
  | .succ n =>
    match e with
    | .sigma _u _v bty bdy | .forallE bty bdy | .lam bty bdy => (bty.arg_binder nth_arg) <|> (bdy.arg_binder nth_arg)
    | .sigma_mk _u _v _A _B x y => x.arg_binder nth_arg <|> y.arg_binder nth_arg
    | .app x y => (x.arg_binder n) <|> (y.arg_binder nth_arg)
    | e => e

def LExpr.n_shared (e : LExpr) : ℕ :=
  match e with
  | .share_ty _ A => A.n_shared.succ
  | _e => 0

def LExpr.share_n (e : LExpr) (n : ℕ) : LExpr :=
  (List.replicate n (LExpr.share 0 (.const .true))).foldr id e

def LExpr.share_val_lean (e : LExpr) : LExpr :=
  match e with
  | .lam bty bdy => .lam bty.share_val_lean bdy.share_val_lean
  | .forallE bty bdy => .forallE bty.share_val_lean bdy.share_val_lean
  | .sigma u v A B => .sigma u v A.share_val_lean B.share_val_lean
  | .sigma_mk u v A B x y => .sigma_mk u v A.share_val_lean B.share_val_lean x.share_val_lean y.share_val_lean
  | .app x y =>
    match x.arg_binder 0 with
    | .some (.lam bty _bdy) => .app x.share_val_lean (y.share_val_lean.share_n bty.n_shared)
    | _ => .app x.share_val_lean y.share_val_lean
  | e => e

def share_lean (e : Lean.Expr) : Except CompileError LExpr :=
  let e : SeekM LExpr := do
    let l_exp   ← LExpr.of_expr e
    return l_exp.share_ty_lean.share_val_lean
  (e.run ⟨.const .true, .top, .unit⟩).1

def cc_lean (e : Lean.Expr) : Except CompileError Expr :=
  let e : SeekM Expr := do
    let l_exp   ← LExpr.of_expr e
    let l_exp'  := l_exp.share_ty_lean.share_val_lean
    (·.1) <$> cc l_exp'
  (e.run ⟨.const .true, .top, .unit⟩).1

elab "dcc_share" tm:term : term => do
  match ← share_lean <$> (elabTerm tm .none >>= Lean.instantiateMVars) with
  | .ok tm' => return Lean.ToExpr.toExpr tm'
  | .error e => throwError m!"{repr e}"

#eval dcc_share ((fun (α : Sort 2) (x : α) => (fun (x : α) => x) x) (Sort 1))

elab "dcc_compile" tm:term : term => do
  match ← cc_lean <$> (elabTerm tm .none >>= Lean.instantiateMVars) with
  | .ok tm' => return Lean.ToExpr.toExpr tm'
  | .error e => throwError m!"{repr e}"
