import Dcc.Syn.JudgePi
import Dcc.Syn.Gen
import Qq
import Lean
import Lean.Meta
import Lean.Elab

open Std (ToFormat Format)
open Std.ToFormat (format)

open Expr

inductive InferAs : Expr → Expr → Type where
  | I   : InferAs (I.type m) (I m)
  | K   : InferAs (K.type m n) (K m n)
  | K'  : InferAs (K'.type m n) (K' m n)
  | S   : InferAs (S.type m n o) (S m n o)
  | Srt : InferAs (Srt m.succ) (Srt m)
  | Pi  : InferAs (Srt m) ((Π' m) _α, _β)
  | app  : InferAs ((Π' m) α, β) f
    → InferAs α x
    → InferAs ⸨β x⸩ ⸨f x⸩
  | conv : InferAs A x → (∃ C, Reduces A C ∧ Reduces B C) → InferAs B x

inductive NoType : Expr → Type where
  | app'      : NoType app'
  | assert    : NoType assert
  | read      : NoType read
  | next      : NoType next
  | hole      : NoType hole

inductive Err : Expr → Type where
  | no_type  : NoType e → Err e
  | mismatch : InferAs ((Π' m) α, β) f
    → InferAs α₂ x
    → (¬ (∃ C, (gen α).fst = C ∧ (gen α₂).fst = C))
    → Err ⸨f x⸩
  | not_fn   : Expr  → Err ⸨f x⸩
  | appl     : Err f → Err ⸨f x⸩
  | appr     : Err x → Err ⸨f x⸩

inductive Inference : Expr → Expr → Type where
  | ok    : InferAs t e → Inference t e
  | error : Err e       → Inference t e



theorem InferAs.sound : InferAs t e → Judge t e := by
  intro h_t
  induction h_t
  · exact Judge.I
  · exact Judge.K
  · exact Judge.K'
  · exact Judge.S
  · exact Judge.Srt
  · exact Judge.Pi
  · apply Judge.app
    assumption
    exact .refl
    assumption
    exact .refl
  case conv α x β h_t_α heq ih =>
    let ⟨C, heq₁, heq₂⟩ := heq
    apply Judge.conv
    assumption
    exact ⟨C, heq₁.hpar, heq₂.hpar⟩

open Expr in def infer (e : Expr) : (Err e) ⊕ ((t : Expr) × InferAs t e) :=
  match e with
  | Srt m => .inr ⟨Srt m.succ, .Srt⟩
  | Pi m _α _β => .inr ⟨Srt m, .Pi⟩
  | K' m n => .inr ⟨K'.type m n, .K'⟩
  | K m n => .inr ⟨K.type m n, .K⟩
  | S m n o => .inr ⟨S.type m n o, .S⟩
  | I m => .inr ⟨I.type m, .I⟩
  | .app f x =>
    match h_t₀ : infer f, infer x with
    | .inl e, _ => .inl <| .appl e
    | _, .inl e => .inl <| .appr e
    | .inr tf@⟨(Π' _m) α₁, β, heq₁⟩, .inr tx@⟨α₂, heq₂⟩ =>
      if hrw : (gen α₁).fst = (gen α₂).fst then by
        apply Sum.inr
        refine ⟨⸨β x⸩, ?_⟩
        apply InferAs.app
        assumption
        apply InferAs.conv
        assumption
        refine ⟨_, (gen α₂).snd.down, ?_, ?_⟩
        rw [← hrw]
        exact (gen α₁).snd.down.hpar
        rw [← hrw]
        exact (gen α₁).snd.down.hkind
      else
        .inl (.mismatch heq₁ heq₂ (by intro ⟨C, h₁, h₂⟩; exact hrw (h₁.trans h₂.symm)))
    | .inr t, _ => .inl <| .not_fn t.fst
  | _? => .inl <| .no_type .hole
  | app' => .inl <| .no_type .app'
  | .read => .inl <| .no_type .read
  | .assert => .inl <|.no_type .assert
  | .next => .inl <| .no_type .next

theorem infer.sound : infer e = .inr ⟨t, h_infer⟩ → Judge t e := fun _ => h_infer.sound

open Expr in example : ∃ t, infer ⸨(I 2) (Srt 1) (Srt 0)⸩ = t := by
  let h₂ := infer ⸨(I 2) (Srt 1) (Srt 0)⸩
  sorry

/-
this infer function is used to solve lean goals.
-/

syntax "decide_infer" : tactic

def InferAs.render (e : InferAs t x) : Lean.Expr :=
  match e with
  | I => by
    
    sorry

open Qq Lean Meta Elab Tactic in
def do_decide_infer (x : _root_.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  match infer x with
  | .inl _ => throwError "error"
  | .inr ⟨_t, h_infer⟩ =>
    let proof := h_infer.render
    let goal ← getMainGoal
    goal.assign proof

open Qq Lean Meta Elab Tactic in elab "decide_infer" : tactic => do
  let goal ← getMainGoal
  let goalType := ← whnf (← Lean.Meta.reduceAll (← goal.getType))
  match goalType with
  | Lean.Expr.app (.app (.const ``Judge []) _α) x =>
    let tgt_term ← whnf (← Lean.Meta.reduceAll x)
    let e ← _root_.Expr.decode tgt_term
    do_decide_infer e
  | _ => throwError "unsupported"
