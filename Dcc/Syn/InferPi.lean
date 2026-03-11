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
    → ParRed' α α'
    → InferAs α₂ x -- unrelated, but we assume they're the same for the tactic
    → ParRed' ⸨β x⸩ β'
    → InferAs β' ⸨f x⸩
  | conv : InferAs A x → ((C : Expr) × (ParRed' A C) × (ParRed' B C)) → InferAs B x
deriving Repr

inductive NoType : Expr → Type where
  | app'      : NoType app'
  | assert    : NoType assert
  | read      : NoType read
  | next      : NoType next
  | hole      : NoType hole
deriving Repr

inductive Err : Expr → Type where
  | no_type  : NoType e → Err e
  | mismatch : InferAs ((Π' m) α, β) f
    → InferAs α₂ x
    → Err ⸨f x⸩
  | not_fn   : Expr  → Err ⸨f x⸩
  | appl     : Err f → Err ⸨f x⸩
  | appr     : Err x → Err ⸨f x⸩
deriving Repr

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
        refine ⟨(gen ⸨β x⸩).fst, ?_⟩
        apply InferAs.app
        assumption
        exact (gen α₁).snd
        assumption
        exact (gen ⸨β x⸩).snd
      else
        .inl (.mismatch heq₁ heq₂)
    | .inr t, _ => .inl <| .not_fn t.fst
  | _? => .inl <| .no_type .hole
  | app' => .inl <| .no_type .app'
  | .read => .inl <| .no_type .read
  | .assert => .inl <|.no_type .assert
  | .next => .inl <| .no_type .next

open Expr in example : ∃ t, infer ⸨(I 2) (Srt 1) (Srt 0)⸩ = t := by
  let h₂ := infer ⸨(I 2) (Srt 1) (Srt 0)⸩
  sorry

/-
this infer function is used to solve lean goals.
-/

syntax "decide_infer" : tactic

/-
Produces a Lean.Expr representing a Judge proof.
-/
open Qq in def InferAs.render (h : InferAs t x) : Lean.Expr :=
  let e : Q(Judge $t $x) :=
    match h with
    | @I m => q(@Judge.I $m)
    | @K m n => q(@Judge.K $m $n)
    | @K' m n => q(@Judge.K' $m $n)
    | @S m n o => q(@Judge.S $m $n $o)
    | @Srt m => q(@Judge.Srt $m)
    | @Pi m α β => q(@Judge.Pi $m $α $β)
    | @conv A x B hA ⟨C, hA', hB'⟩ =>
      let hA : Q(Judge $A $x) := hA.render
      let hA' : Q(ParRed $A $C) := gen_par_red_proof hA'
      let hB' : Q(ParRed $B $C) := gen_par_red_proof hB'
      q(@Judge.conv $A $x $B $hA ⟨$C, $hA', $hB'⟩)
    | @app m α β f α' α₂ x β' h_t_f h_redα h_t_x h_red_cod =>
      let h_f' : Q(Judge (Expr.Pi $m $α $β) $f) := h_t_f.render
      let h_x' : Q(Judge $α' $x) := h_t_x.render
      let red_proof_dom : Q(ParRed $α $α') := gen_par_red_proof h_redα
      let red_proof_cod : Q(ParRed (Expr.app $β $x) $β') := gen_par_red_proof h_red_cod
      q(@Judge.app $m $α $β $f $α' $x $β' $h_f' $red_proof_dom $h_x' $red_proof_cod)
  e

open Qq Lean Meta Elab Tactic in
def do_decide_infer (x : _root_.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  match infer x with
  | .inl e => throwError s!"error: {repr e}"
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

example : Judge (Srt 1) ⸨(I 2) (Srt 1) (Srt 0)⸩ := by
  decide_infer
