import Dcc.Syn.JudgePi
import Dcc.Syn.Gen
import Qq
import Lean
import Lean.Meta
import Lean.Elab

open Std (ToFormat Format)
open Std.ToFormat (format)

open Expr

/-
We extend our AST with lean expr's to enable
solving via hypotheses in context.
However, the resulting proofs are still of type Judge : Expr → Expr → Prop
-/

open gen in inductive InferAs : MExpr → MExpr → Type where
  | proof : Lean.Expr → InferAs α x
  | I     : InferAs (I.type m).toMeta (.I m)
  | K     : InferAs (K.type m n).toMeta (.K m n)
  | K'    : InferAs (K'.type m n).toMeta (.K' m n)
  | S     : InferAs (S.type m n o).toMeta (.S m n o)
  | Srt   : InferAs (.Srt m.succ) (.Srt m)
  | Pi    : InferAs (.Srt m) (.Pi m _α _β)
  | app   : InferAs (.Pi m α β) f
    → ParRed' α α'
    → InferAs α₂ x -- unrelated, but we assume they're the same for the tactic
    → ParRed' (β.app x) β'
    → InferAs β' (MExpr.app f x)
    -- Axioms supplied from local context for the tactic
  | conv : InferAs A x → ((C : MExpr) × (ParRed' A C) × (ParRed' B C)) → InferAs B x
deriving Repr

inductive NoType : gen.MExpr → Type where
  | app'      : NoType .app'
  | assert    : NoType .assert
  | read      : NoType .read
  | next      : NoType .next
  | hole      : NoType .hole
  | fvar      : NoType (.fvar m)
deriving Repr

inductive Err : gen.MExpr → Type where
  | no_type  : NoType e → Err e
  | mismatch : InferAs (.Pi m α β) f
    → InferAs α₂ x
    → Err *⸨f x⸩
  | not_fn   : gen.MExpr → Err *⸨f x⸩
  | appl     : Err f → Err *⸨f x⸩
  | appr     : Err x → Err *⸨f x⸩
deriving Repr

open Lean Elab Tactic in def infer.matcher (on_e : FVarId) (hyp_type : Lean.Expr) : Bool:=
  match hyp_type with
  | Lean.Expr.app (Lean.Expr.app b (Lean.Expr.fvar _t)) (.fvar e')  =>
    b == (Lean.Expr.const ``Judge []) ∧ e' == on_e
  | _ => false

-- Note: axioms are a generalization of hypotheses in the lean info view
-- consumed by our decide tactic
open Lean Elab Tactic Elab gen in def infer (e : MExpr) : TacticM ((Err e) ⊕ ((t : MExpr) × InferAs t e)) :=
  match e with
  | .lean_e _e => throwError "unsupported"
  | .fvar v => do
    let p? := (← try_first_hyp (infer.matcher v))
    match p? with
    | .some ⟨.app (.app (.const ``Judge []) α) _x, proof⟩ =>
      return .inr ⟨.lean_e α, .proof proof (α := .lean_e α) (x := (.fvar v))⟩
    | _ => throwError "no matching hypothesis"
  | .Srt m => return .inr ⟨.Srt m.succ, .Srt⟩
  | .Pi m _α _β => return .inr ⟨.Srt m, .Pi⟩
  | .K' m n => return .inr ⟨(K'.type m n).toMeta, .K'⟩
  | .K m n => return .inr ⟨(K.type m n).toMeta, .K⟩
  | .S m n o => return .inr ⟨(S.type m n o).toMeta, .S⟩
  | .I m => return .inr ⟨(I.type m).toMeta, .I⟩
  | .app f x => do
    let t_f ← infer f
    let t_x ← infer x
    match t_f, t_x with
    | .inl e, _ => return .inl <| .appl e
    | _, .inl e => return .inl <| .appr e
    | .inr ⟨MExpr.Pi _m α₁ β, heq₁⟩, .inr ⟨α₂, heq₂⟩ => do
      let α' ← (reduce α₁)
      let α₂' ← (reduce α₂)
      let β' ← reduce *⸨β x⸩
      if α'.fst == α₂'.fst then
        return Sum.inr ⟨β'.fst,
          .app (f := f) heq₁ α'.snd (α₂ := α₂'.fst) (.conv heq₂ (⟨α₂'.fst, α₂'.snd, .parred_refl⟩)) β'.snd⟩
      else
        return .inl (.mismatch heq₁ heq₂)
    | .inr t, _ => return .inl <| .not_fn t.fst
  | .hole => return .inl <| .no_type .hole
  | .app' => return .inl <| .no_type .app'
  | .read => return .inl <| .no_type .read
  | .assert => return .inl <|.no_type .assert
  | .next => return .inl <| .no_type .next

/-
this infer function is used to solve lean goals.
-/

syntax "decide_infer" : tactic

/-
Produces a Lean.Expr representing a Judge proof.
-/
open Qq Lean Elab Tactic in def InferAs.render (h : InferAs t x) : TacticM Lean.Expr := do
  match h with
  | @proof α x pf => return pf
  | @I m => return q(@Judge.I $m)
  | @K m n => return q(@Judge.K $m $n)
  | @K' m n => return q(@Judge.K' $m $n)
  | @S m n o => return q(@Judge.S $m $n $o)
  | @Srt m => return q(@Judge.Srt $m)
  | @Pi m α β => do
    let α : Q(_root_.Expr) ← α.unify
    let β : Q(_root_.Expr) ← β.unify
    return q(@Judge.Pi $m $α $β)
  | @conv A x B hA ⟨C, hA', hB'⟩ => do
    let A ← A.unify
    let x ← x.unify
    let C ← C.unify
    let B ← B.unify
    let hA : Q(Judge $A $x) ← hA.render
    let hA' : Q(ParRed $A $C) ← gen_par_red_proof hA'
    let hB' : Q(ParRed $B $C) ← gen_par_red_proof hB'
    return q(@Judge.conv $A $x $B $hA ⟨$C, $hA', $hB'⟩)
  | @app m α β f α' _α₂ x β' h_t_f h_redα h_t_x h_red_cod => do
    let α ← α.unify
    let α' ← α'.unify
    let x ← x.unify
    let β ← β.unify
    let β' ← β'.unify
    let f ← f.unify

    let h_f' : Q(Judge (Expr.Pi $m $α $β) $f) ← h_t_f.render
    let h_x' : Q(Judge $α' $x) ← h_t_x.render
    let red_proof_dom : Q(ParRed $α $α') ← gen_par_red_proof h_redα
    let red_proof_cod : Q(ParRed (Expr.app $β $x) $β') ← gen_par_red_proof h_red_cod
    return q(@Judge.app $m $α $β $f $α' $x $β' $h_f' $red_proof_dom $h_x' $red_proof_cod)

open gen Qq Lean Meta Elab Tactic in
def do_decide_infer (x : MExpr) : Lean.Elab.Tactic.TacticM Unit := do
  match ← infer x with
  | .inl e => throwError s!"error: {repr e}"
  | .inr ⟨_t, h_infer⟩ =>
    let proof ← h_infer.render
    let goal ← getMainGoal
    goal.assign proof

open Qq Lean Meta Elab Tactic in elab "decide_infer" : tactic => do
  let goal ← getMainGoal
  let goalType := ← whnf (← Lean.Meta.reduceAll (← goal.getType))
  match goalType with
  | Lean.Expr.app (.app (.const ``Judge []) _α) x =>
    let tgt_term ← whnf (← Lean.Meta.reduceAll x)
    let e ← gen.MExpr.decode tgt_term
    do_decide_infer e
  | _ => throwError "unsupported"

example : Judge (Srt 1) ⸨(I 2) (Srt 1) (Srt 0)⸩ := by
  decide_infer
