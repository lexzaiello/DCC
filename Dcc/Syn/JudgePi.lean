import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Relation
open Std (ToFormat Format)
open Std.ToFormat (format)
open Relation

abbrev Level := ℕ

inductive Expr where
  | Srt    : Level → Expr
  | Pi     : Level → Expr → Expr → Expr -- Pi (α : Syntax (Sort m)) (β : Sort n) : (Sort n)
  | K'     : Level → Level → Expr
  | K      : Level → Level → Expr
  | S      : Level → Level → Level → Expr
  | I      : Level → Expr
  | hole   : Expr
  | next   : Expr
  | read   : Expr
  | assert : Expr
  | app'   : Expr
  | app    : Expr  → Expr → Expr
deriving BEq, Repr, DecidableEq

open Expr

syntax num term : term

syntax "$" : term
syntax "${" term "}" : term
syntax "(Π'" term ")" term "," term : term
syntax "(Π')" : term
syntax "⸨" term* "⸩" : term
syntax "Ty" term : term
syntax "_?" : term

macro_rules
  | `(Ty $n) => `(Expr.Srt ($n + 1))
  | `(_?) => `(Expr.hole)
  | `($n:num $fn:term) =>
    match n.getNat with
    | 0 => `($fn)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(⸨Expr.next ($n':num $fn)⸩)
  | `(${ $t:term }) => `(⸨$ $t⸩)
  | `($) => `(Expr.app')
  | `((Π' $m) $α, $β) => `(Expr.Pi $m $α $β)
  | `(⸨$f:term $x:term⸩) => `(Expr.app $f:term $x:term)
  | `(⸨$f:term $x:term $xs:term*⸩) => `(⸨⸨$f:term $x:term⸩ $xs:term*⸩)

example :  ⸨(Srt 0) (Srt 1) (Srt 2)⸩ = Expr.app (Expr.app (Expr.Srt 0) (Expr.Srt 1)) (Expr.Srt 2) := rfl

def Expr.toFormat : Expr → Format
  | .hole => "_?"
  | Srt m => s!"(Srt {m})"
  | K' m n => s!"(K' {m} {n})"
  | K m n => s!"(K {m} {n})"
  | S m n o => s!"(S {m} {n} {o})"
  | (Π' m) α, β => .paren <| "Π' " ++ (.paren (format m)) ++ " " ++ α.toFormat ++ "," ++ .line ++ β.toFormat
  | I m => s!"(I {m})"
  | .app f x => .bracket "⸨" (f.toFormat ++ (.nest 2 <| .line ++ x.toFormat)) "⸩"
  | .app' => "$"
  | .assert => "assert"
  | .next => "next"
  | .read => "read"

instance : ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ toFormat⟩

namespace Expr

def eval (e : Expr) : Except Format Expr :=
  match e with
  | ⸨(I _m) _α x⸩ => pure x
  | ⸨(K _m _n) _α _β x _y⸩ => pure x
  | ⸨(K' _m _n) _α _β x _y⸩ => pure x
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => return ⸨⸨x z⸩ ⸨y z⸩⸩
  | ⸨((Π' m) α, β) x⸩ => return (Π' m) ⸨α x⸩, ⸨β x⸩
  | ⸨next f _x⸩ => pure f
  | ⸨read e⸩ => pure e
  | ⸨assert e _x⸩ => pure e
  | ⸨${π} f g x⸩ => pure ⸨π ⸨f x⸩ ⸨g x⸩⸩
  | e => .error <| "stuck: " ++ (format e)

abbrev comp (f g : Expr) : Expr :=
  ⸨${read} ⸨assert f⸩ g⸩

infix:30 "∘'" => comp

abbrev assert_n (n : ℕ) (fn : Expr) : Expr :=
  (List.replicate n assert).foldr (fun e acc => (e ∘' acc)) fn

def I.type (m : Level) : Expr :=
  (Π' m) (Srt m), (Π' m) (0 read), (0 assert)

def K'.type (m n : Level) : Expr :=
  (Π' m) (Srt m), (Π' m) ⸨assert (Srt n)⸩, (Π' m) (0 assert), (Π' m) (1 assert), (assert_n 3 (0 read))

def K.type (m n : Level) : Expr :=
    (Π' m) (Srt m)
  , (Π' m) ((Π' n.succ) (0 read), (1 ⸨assert (Srt n)⸩))
  , (Π' m) (0 assert)
  , (Π' m) ⸨${${read}} (1 assert) (2 read)⸩
  , (assert_n 3 read)

def S.type (m n o : Level) : Expr :=
    (Π' o) (Srt m)
  , (Π' o) ((Π' n.succ) (0 read), (1 ⸨assert (Srt n)⸩))
  , (Π' o) ((Π' o.succ) (0 assert)
      , (Π' o.succ) (1 read)
      , (3 ⸨assert (Srt o)⸩))
  , (Π' o) ((Π' o) (assert_n 2 (0 read))
      , (Π' o) (1 assert)
      , (2 read))
   , (Π' o) ((Π' n) (assert_n 3 (0 read))
       , (1 (assert ∘' assert)))
   , (Π' o) (assert_n 4 (0 read))
   , (2 (${read} ∘' assert))

def norm (e : Expr) :=
  match e with
  | ⸨(I _m) _α x⸩ => norm x
  | ⸨(K _m _n) _α _β x _y⸩ => norm x
  | ⸨(K' _m _n) _α _β x _y⸩ => norm x
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => ⸨(norm ⸨x z⸩) (norm ⸨y z⸩)⸩
  | ⸨((Π' m) α, β) x⸩ => (Π' m) (norm ⸨α x⸩), (norm ⸨β x⸩)
  | ⸨next f _x⸩ => norm f
  | ⸨read e⸩ => norm e
  | ⸨assert e _x⸩ => norm e
  | ⸨${π} f g x⸩ => ⸨π (norm ⸨f x⸩) (norm ⸨g x⸩)⸩
  | (Π' m) α, β => (Π' m) (norm α), (norm β)
  | ⸨f x⸩ => ⸨(norm f) (norm x)⸩
  | e => e

def defeq (α β : Expr) (gas : ℕ := 100) : Except Format Unit :=
  match gas, α, β with
  | .succ n, ((Π' _m₁) α₁, β₁), ((Π' _m₂) α₂, β₂) => do
    let _ ← (defeq α₁ α₂ n).mapError (fun e => "while checking Π domain: " ++ e)
    (defeq (norm ⸨β₁ _?⸩) (norm ⸨β₂ _?⸩) n).mapError (fun e => "while checking Π codomain: " ++ e)
  | .succ n, ⸨assert e₁⸩, ⸨assert e₂⸩ => defeq e₁ e₂ n
  | _, e₁, e₂ =>
    let e₁' := norm e₁
    let e₂' := norm e₂
    if e₁' == e₂' then
      pure ()
    else
      .error <| (format α) ++ " ≠ " ++ (format β)

def infer : Expr → Except Format Expr
  | I m => return I.type m
  | K m n => return K.type m n
  | K' m n => return K'.type m n
  | S m n o => return S.type m n o
  | Srt m => return Srt m.succ
  | (Π' m) _α, _β => return Srt m
  | ⸨f x⸩ => do match ← norm <$> infer f, ← norm <$> infer x with
    | ((Π' _m) α₁, β), α₂ => do
      let _ ← (defeq α₁ α₂).mapError
        (fun e => "argument mismatch in app " ++ (format ⸨f x⸩) ++ ":" ++ .line ++ e)
      pure <| norm ⸨β x⸩
    | t₁, _t₂ =>
      .error <| "not a function type: " ++ (.nest 2 <| .line ++ (format t₁))
  | e => .error <| "not well-typed: " ++ (.nest 2 <| .line ++ (format e))

#eval infer ⸨(I 2) (Srt 1) (Srt 0)⸩
#eval infer ⸨(K 3 2) (Srt 2) ⸨(I 3) (Srt 2)⸩ (Srt 1) (Srt 0)⸩

syntax "(" "~>" term ")" term "," term : term

macro_rules
  | `((~> $m:term) $α:term, $β:term) => `((Π' $m) $α, ⸨assert $β⸩)

def mk_I (α : Expr) (m : Level) : Expr :=
  let α := α
  let y := ⸨(K' 2 m) (Srt 1) α (Srt 0)⸩
  let x := ⸨(K' m 2) α (Srt 1)⸩

  let β := ⸨(K' 3 m) (Srt 2) α (Srt 1)⸩
  let γ := ⸨(K' m.succ m) ((~> m.succ) (Srt 1), (Srt m)) α ⸨(K' m.succ 2) (Srt m) (Srt 1) α⸩⸩

  ⸨(S m 2 m) α β γ x y⸩

#eval infer <| mk_I (Srt 1) 2
#eval infer <| ⸨(mk_I (Srt 1) 2) (Srt 0)⸩

inductive Whnf : Expr → Prop where
  | I₀      : Whnf (I m)
  | I₁      : Whnf ⸨(I m) α⸩
  | K₀      : Whnf (K m n)
  | K₁      : Whnf ⸨(K m n) α⸩
  | K₂      : Whnf ⸨(K m n) α β⸩
  | K₃      : Whnf ⸨(K m n) α β x⸩
  | K'₀     : Whnf (K' m n)
  | K'₁     : Whnf ⸨(K' m n) α⸩
  | K'₂     : Whnf ⸨(K' m n) α β⸩
  | K'₃     : Whnf ⸨(K' m n) α β x⸩
  | S₀      : Whnf (S m n o)
  | S₁      : Whnf ⸨(S m n o) α⸩
  | S₂      : Whnf ⸨(S m n o) α β⸩
  | S₃      : Whnf ⸨(S m n o) α β γ⸩
  | S₄      : Whnf ⸨(S m n o) α β γ x⸩
  | S₅      : Whnf ⸨(S m n o) α β γ x y⸩
  | Pi      : Whnf ((Π' m) α, β)
  | Srt     : Whnf (Srt m)
  | next₀   : Whnf next
  | next₁   : Whnf ⸨next f⸩
  | read    : Whnf read
  | assert₀ : Whnf assert
  | assert₁ : Whnf ⸨assert e⸩
  | app'₀   : Whnf $
  | app'₁   : Whnf ⸨$ a⸩
  | app'₂   : Whnf ⸨$ a b⸩
  | app'₃   : Whnf ⸨$ a b c⸩

inductive Nf : Expr → Prop where
  | I₀      : Nf (I m)
  | I₁      : Nf α → Nf ⸨(I m) α⸩
  | K₀      : Nf (K m n)
  | K₁      : Nf α → Nf ⸨(K m n) α⸩
  | K₂      : Nf α → Nf β → Nf ⸨(K m n) α β⸩
  | K₃      : Nf α → Nf β → Nf x → Nf ⸨(K m n) α β x⸩
  | K'₀     : Nf (K' m n)
  | K'₁     : Nf α → Nf ⸨(K' m n) α⸩
  | K'₂     : Nf β → Nf ⸨(K' m n) α β⸩
  | K'₃     : Nf α → Nf β → Nf x → Nf ⸨(K' m n) α β x⸩
  | S₀      : Nf (S m n o)
  | S₁      : Nf α → Nf ⸨(S m n o) α⸩
  | S₂      : Nf α → Nf β → Nf ⸨(S m n o) α β⸩
  | S₃      : Nf α → Nf β → Nf γ → Nf ⸨(S m n o) α β γ⸩
  | S₄      : Nf α → Nf β → Nf γ → Nf x → Nf ⸨(S m n o) α β γ x⸩
  | S₅      : Nf α → Nf β → Nf γ → Nf x → Nf y → Nf ⸨(S m n o) α β γ x y⸩
  | Pi      : Nf α → Nf β → Nf ((Π' m) α, β)
  | Srt     : Nf (Srt m)
  | next₀   : Nf next
  | next₁   : Nf f → Nf ⸨next f⸩
  | read    : Nf read
  | assert₀ : Nf assert
  | assert₁ : Nf e → Nf ⸨assert e⸩
  | app'₀   : Nf $
  | app'₁   : Nf a → Nf ⸨$ a⸩
  | app'₂   : Nf a → Nf b → Nf ⸨$ a b⸩
  | app'₃   : Nf ⸨$ a b c⸩


inductive Red : Expr → Expr → Prop
  | I      : Red ⸨(I _m) _α x⸩ x
  | K      : Red ⸨(K _m _n) _α _β x _y⸩ x
  | K'     : Red ⸨(K' _m _n) _α _β x _y⸩ x
  | S      : Red ⸨(S _m _n _o) _α _β _γ x y z⸩ ⸨⸨x z⸩ ⸨y z⸩⸩
  | Pi     : Red ⸨((Π' m) α, β) x⸩ ((Π' m) ⸨α x⸩, ⸨β x⸩)
  | next   : Red ⸨next f _x⸩ f
  | read   : Red ⸨read e⸩ e
  | assert : Red ⸨assert e _x⸩ e
  | app'   : Red ⸨${π} f g x⸩ ⸨π ⸨f x⸩ ⸨g x⸩⸩

inductive StepStar : Expr → Expr → Prop
  | Red    : Red a b → StepStar a b
  | refl   : StepStar a a
  | app    : StepStar f f' → StepStar x x' → StepStar ⸨f x⸩ ⸨f' x'⸩
  | pi     : StepStar α α' → StepStar β β' → StepStar ((Π' m) α, β) ((Π' m) α', β')

inductive StepPlus : Expr → Expr → Prop
  | Red    : Red a b → StepPlus a b
  | app    : StepPlus f f' → StepPlus x x' → StepPlus ⸨f x⸩ ⸨f' x'⸩
  | pi     : StepPlus α α' → StepPlus β β' → StepPlus ((Π' m) α, β) ((Π' m) α', β')

inductive Judge : Expr → Expr → Prop
  | I   : Judge (I.type m) (I m)
  | K   : Judge (K.type m n) (K m n)
  | K'  : Judge (K'.type m n) (K' m n)
  | S   : Judge (S.type m n o) (S m n o)
  | Srt : Judge (Srt m.succ) (Srt m)
  | Pi  : Judge (Srt m) ((Π' m) _α, _β)
  | app : Judge ((Π' _m) α, β) f
    → Judge α x
    → Judge ⸨β x⸩ ⸨f x⸩
  | conv : Judge A x → (∃ C, StepStar A C ∧ StepStar B C) → Judge B x

theorem confluence : Red a b → Red a c → ∃ d, StepStar b d ∧ StepStar c d := by
  intro hb hc
  cases hb
  repeat (cases hc; exact ⟨_, StepStar.refl, StepStar.refl⟩)

theorem Whnf.no_step : Whnf e → ¬ ∃ e', Red e e' := by
  intro h
  cases h
  repeat (intro ⟨e', hstep⟩; contradiction)

theorem Whnf.left : Whnf ⸨f x⸩ → Whnf f := by
  intro h
  cases h
  exact Whnf.I₀
  exact Whnf.K₀
  exact Whnf.K₁
  exact Whnf.K₂
  exact Whnf.K'₀
  exact Whnf.K'₁
  exact Whnf.K'₂
  exact Whnf.S₀
  exact Whnf.S₁
  exact Whnf.S₂
  exact Whnf.S₃
  exact Whnf.S₄
  exact Whnf.next₀
  exact Whnf.assert₀
  exact Whnf.app'₀
  exact Whnf.app'₁
  exact Whnf.app'₂

theorem step_left_or_whole : Red ⸨f x⸩ e' → (∃ f', Red f f' ∧ e' = ⸨f' x⸩) ∨ Whnf f := by
  intro h_step
  cases h_step
  exact Or.inr Whnf.I₁
  exact Or.inr Whnf.K₃
  exact Or.inr Whnf.K'₃
  exact Or.inr Whnf.S₅
  exact Or.inr Whnf.Pi
  exact Or.inr Whnf.next₁
  exact Or.inr Whnf.read
  exact Or.inr Whnf.assert₁
  exact Or.inr Whnf.app'₃

theorem step_whole : Red ⸨f x⸩ e' → Whnf f ∨ Whnf ⸨f x⸩ := by
  intro h_r
  cases h_r
  exact Or.inl Whnf.I₁
  exact Or.inl Whnf.K₃
  exact Or.inl Whnf.K'₃
  exact Or.inl Whnf.S₅
  exact Or.inl Whnf.Pi
  exact Or.inl Whnf.next₁
  exact Or.inl Whnf.read
  exact Or.inl Whnf.assert₁
  exact Or.inl Whnf.app'₃

theorem Step.sound (e₁ e₂) : Red e₁ e₂ → eval e₁ = .ok e₂ := by
  intro h_r
  induction h_r
  repeat rfl

theorem Step.complete (e₁ e₂) : eval e₁ = .ok e₂ → Red e₁ e₂ := by
  intro h_e
  unfold eval at h_e
  induction e₁
  repeat simp at h_e
  case app f x ih =>
    rename_i a
    split at h_e
    rename_i heq
    cases heq
    cases h_e
    exact Red.I
    rename_i heq
    cases heq
    cases h_e
    exact Red.K
    rename_i heq
    cases heq
    cases h_e
    exact Red.K'
    rename_i heq
    cases heq
    cases h_e
    exact Red.S
    rename_i heq
    cases heq
    cases h_e
    exact Red.Pi
    rename_i heq
    cases heq
    cases h_e
    exact Red.next
    rename_i heq
    cases heq
    cases h_e
    exact Red.read
    rename_i heq
    cases heq
    cases h_e
    exact Red.assert
    rename_i heq
    cases heq
    cases h_e
    exact Red.app'
    simp_all

theorem diamond' : StepPlus a b → StepPlus a c → ∃ d, StepStar b d ∧ StepStar c d := by
  intro hb hc
  induction hb generalizing c with
  | Red h_r_b =>
    rename_i a₁ b₁
    induction hc generalizing b₁
    apply confluence
    repeat assumption
    case Red.app f f' x x' hp₁ hp₂ ih₁ ih₂ =>
      cases hp₁
      rename_i ha
      have h := ih₁ ha
      
      sorry
  |  _ => sorry

theorem inv : Judge ((Π' m) α, β) f → Judge α x → Judge ⸨β x⸩ ⸨f x⸩ := by
  apply Judge.app

theorem Judge_I_par {h_t_α : Judge (Srt m) α} : Judge ((Π' m) α, ⸨assert α⸩) ⸨(I m) α⸩ := by
  apply Judge.conv
  apply Judge.conv
  apply Judge.app
  apply Judge.I
  assumption
  exact ⟨(Π' m) ⸨read α⸩, ⸨assert α⸩, StepStar.Red Red.Pi, StepStar.refl⟩
  refine ⟨(Π' m) α, ⸨assert α⸩, ?_, StepStar.refl⟩
  apply StepStar.pi
  apply StepStar.Red
  exact Red.read
  exact StepStar.refl

theorem Judge_I {h_t_α : Judge (Srt m) α} {h_t_x : Judge α x} : Judge α ⸨(I m) α x⸩ := by
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.conv
  apply Judge.app
  apply Judge.I
  exact h_t_α
  exact ⟨(Π' m) ⸨read α⸩, ⸨assert α⸩, StepStar.Red Red.Pi, StepStar.refl⟩
  exact ⟨(Π' m) α, ⸨assert α⸩, StepStar.pi (StepStar.Red Red.read) StepStar.refl, StepStar.refl⟩
  assumption
  exact ⟨α, StepStar.Red Red.assert, StepStar.refl⟩

theorem preservation (h_t : Judge α x) (h_step : Red x x') : Judge α x' := by
  induction h_t generalizing x'
  repeat contradiction
  case app _m α β f x h_t_f h_t_x ih₁ ih₂ =>
    cases h_step
    cases h_t_f
    rename_i h
    cases h
    rename_i h _ _
    cases h
    rename_i h_c
    have ⟨C, heq₁, heq₂⟩ := h_c
    cases heq₁
    rename_i h
    cases h
    cases heq₂
    contradiction
    apply Judge.conv
    assumption
    exact ⟨_, StepStar.Red Red.read, StepStar.Red Red.assert⟩
    apply Judge.conv
    assumption
    rename_i h₁ h₂
    rename_i _α _
    refine ⟨_α, by sorry, StepStar.trans (StepStar.app h₂ StepStar.refl) (StepStar.Red Red.assert)⟩
    
    /-cases h_t_f
    rename_i α₀ x₀ _m₁ _α A h_c h
    cases h
    rename_i _m₂ α₂ β₂ h_j₂ h_j₃
    have h' := inv h_j₂ (by assumption)
    have h_judge₂ : Judge (Pi _m α β) ((I _m₁).app _α) := Judge.conv h' h_c
    have h'' := inv h_judge₂ (by assumption)
    cases h_j₂-/
    
    sorry

example : Judge (Srt 1) ⸨(I 2) (Srt 1) (Srt 0)⸩ := by
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.app
  apply Judge.I
  exact Judge.Srt
  use (Π' 2) ⸨read (Srt 1)⸩, ⸨assert (Srt 1)⸩
  constructor
  apply StepStar.Red
  apply Red.Pi
  exact StepStar.refl
  apply Judge.conv
  exact Judge.Srt
  exact ⟨Srt 1, StepStar.refl, StepStar.Red Red.read⟩
  exact ⟨Srt 1, StepStar.Red Red.assert, StepStar.refl⟩

end Expr
