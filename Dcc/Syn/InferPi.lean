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

open Qq gen in abbrev Level.succ (l : Level) : Level :=
  let l : Q(Lean.Level) := l
  q(Lean.Level.succ $l)

namespace gen

open MExpr

syntax "(Π''" term ")" term "," term : term
syntax "(Π'')" : term
syntax "#" num term : term
syntax "$'{" term "}" : term
syntax "$'" : term

macro_rules
  | `((Π'' $m) $α, $β) => `(MExpr.Pi $m $α $β)
  | `(#$n:num $fn:term) =>
    match n.getNat with
    | 0 => `($fn)
    | .succ n =>
      let n' := Lean.Syntax.mkNatLit n
      `(*⸨MExpr.next (# $n':num $fn)⸩)
  | `($') => `(MExpr.app')
  | `($'{ $t:term }) => `(*⸨$' $t⸩)


abbrev comp (f g : MExpr) : MExpr :=
  *⸨$'{read} *⸨assert f⸩ g⸩

infix:30 "∘'" => comp

abbrev assert_n (n : ℕ) (fn : MExpr) : MExpr :=
  (List.replicate n MExpr.assert).foldr (fun e acc => (e ∘' acc)) fn

def I.type (m : Level) : MExpr :=
  (Π'' m) (Srt m), (Π'' m) (# 0 read), (0 assert)

def K'.type (m n : Level) : MExpr :=
  (Π'' m) (Srt m), (Π'' m) *⸨assert (Srt n)⸩, (Π'' m) (0 assert), (Π'' m) (# 1 assert), (assert_n 3 (0 read))

def K.β_arg (_m n : Level) : MExpr :=
  (Π'' (Level.succ n)) (0 read), (# 1 *⸨assert (Srt n)⸩)

def K.x_arg : MExpr := (0 assert)

def K.y_arg : MExpr := *⸨$'{$'{read}} (# 1 assert) (# 2 MExpr.read)⸩

def K.cod : MExpr := (assert_n 3 read)

def K.type (m n : Level) : MExpr :=
    (Π'' m) (Srt m)
  , (Π'' m) (K.β_arg m n)
  , (Π'' m) K.x_arg
  , (Π'' m) K.y_arg
  , K.cod

def S.type (m n o : Level) : MExpr :=
    (Π'' o) (Srt m)
  , (Π'' o) ((Π'' (Level.succ n)) (# 0 read), (# 1 *⸨assert (Srt n)⸩))
  , (Π'' o) ((Π'' (Level.succ o)) (# 0 assert)
      , (Π'' (Level.succ o)) (# 1 read)
      , (# 3 *⸨assert (Srt o)⸩))
  , (Π'' o) ((Π'' o) (assert_n 2 (0 read))
      , (Π'' o) (# 1 assert)
      , (# 2 read))
   , (Π'' o) ((Π'' n) (assert_n 3 (0 read))
       , (# 1 (assert ∘' assert)))
   , (Π'' o) (assert_n 4 (0 read))
   , (# 2 (assert ∘' $'{read}))

end gen

open Qq gen in inductive InferAs : MExpr → MExpr → Type where
  | proof : Lean.Expr → InferAs α x
  | I     : InferAs (gen.I.type m) (.I m)
  | K     : InferAs (gen.K.type m n) (.K m n)
  | K'    : InferAs (gen.K'.type m n) (.K' m n)
  | S     : InferAs (gen.S.type m n o) (.S m n o)
  | Srt   : InferAs (.Srt (Level.succ m)) (.Srt m)
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
  | Lean.Expr.app (Lean.Expr.app b _t) (.fvar e')  =>
    b == (Lean.Expr.const ``Judge []) ∧ e' == on_e
  | _ => false

open Lean Elab Tactic Elab gen in def conv_app_n (t₀ e : MExpr) (h_t : InferAs t₀ e) (max_steps : ℕ := 1000) : TacticM (((β' : MExpr) × InferAs β' e)) := do
  match max_steps with
  | .zero => return ⟨t₀, h_t⟩
  | .succ n =>
    let e' ← reduce t₀
    if e'.fst == t₀ then
      return ⟨t₀, h_t⟩
    else
      let t : InferAs e'.fst e := InferAs.conv (A := t₀) h_t ⟨e'.fst, e'.snd, .parred_refl⟩
      conv_app_n e'.fst e t n

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
  | .Srt m => return .inr ⟨.Srt (Level.succ m), .Srt⟩
  | .Pi m _α _β => return .inr ⟨.Srt m, .Pi⟩
  | .K' m n => return .inr ⟨(gen.K'.type m n), .K'⟩
  | .K m n => return .inr ⟨(gen.K.type m n), .K⟩
  | .S m n o => return .inr ⟨(gen.S.type m n o), .S⟩
  | .I m => return .inr ⟨(gen.I.type m), .I⟩
  | .app f x => do
    let t_f ← infer f
    let t_x ← infer x
    match t_f, t_x with
    | .inl e, _ => return .inl <| .appl e
    | _, .inl e => return .inl <| .appr e
    | .inr ⟨MExpr.Pi _m α₁ β, heq₁⟩, .inr ⟨α₂, heq₂⟩ => do
      let α' ← (reduce α₁)
      let α₂' ← (conv_app_n α₂ x heq₂)
      let β' ← reduce *⸨β x⸩
      if defeq α'.fst α₂'.fst then
        let t₀ := InferAs.app (β' := β'.fst) (f := f) heq₁ α'.snd (α₂ := α'.fst) (.conv heq₂ (⟨α'.fst, .parred_refl, .parred_refl⟩)) β'.snd
        return Sum.inr (← conv_app_n β'.fst *⸨f x⸩ t₀)
      else
        return .inl (.mismatch heq₁ heq₂)
    | .inr t, _ => return .inl <| .not_fn t.fst
  | .hole => return .inl <| .no_type .hole
  | .app' => return .inl <| .no_type .app'
  | .read => return .inl <| .no_type .read
  | .assert => return .inl <|.no_type .assert
  | .next => return .inl <| .no_type .next
where defeq (t₁ t₂ : MExpr) := match t₁, t₂ with
  | MExpr.fvar _e, _t₂ => true
  | _t₁, MExpr.fvar _t₂
  | .lean_e _t₁, _t₂
  | _t₂, .lean_e _t₁ => true
  | t₁, t₂ => t₁ == t₂

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
  | @I m =>
    let m : Q(Lean.Level) := m
    return q(@Judge.I $m)
  | @K m n =>
    let m : Q(Lean.Level) := m
    let n : Q(Lean.Level) := n
    return q(@Judge.K $m $n)
  | @K' m n =>
    let m : Q(Lean.Level) := m
    let n : Q(Lean.Level) := n
    return q(@Judge.K' $m $n)
  | @S m n o =>
    let m : Q(Lean.Level) := m
    let n : Q(Lean.Level) := n
    let o : Q(Lean.Level) := o
    return q(@Judge.S $m $n $o)
  | @Srt m =>
    let m : Q(Lean.Level) := m
    return q(@Judge.Srt $m)
  | @Pi m α β => do
    let α : Q(_root_.Expr) ← α.unify
    let β : Q(_root_.Expr) ← β.unify
    let m : Q(Lean.Level) := m
    return q(@Judge.Pi $m $α $β)
  | @conv A x B hA ⟨C, hA', hB'⟩ => do
    let A ← A.unify
    let x ← x.unify
    let C ← C.unify
    let B ← B.unify
    let hA : Q(Judge $A $x) ← hA.render
    let hA' : Q(ParRed $A $C) ← gen_par_red_proof hA'
    let hB' : Q(ParRed $B $C) ← gen_par_red_proof hB'
    return q(@Judge.conv $A $x $B $hA ⟨$C, ⟨$hA', $hB'⟩⟩)
  | @app m α β f α' _α₂ x β' h_t_f h_redα h_t_x h_red_cod => do
    let α ← α.unify
    let α' ← α'.unify
    let x ← x.unify
    let β ← β.unify
    let β' ← β'.unify
    let f ← f.unify

    let h_x' : Q(Judge $α' $x) ← h_t_x.render
    let red_proof_dom : Q(ParRed $α $α') ← gen_par_red_proof h_redα
    let red_proof_cod : Q(ParRed (Expr.app $β $x) $β') ← gen_par_red_proof h_red_cod
    let h_f' : Q(Judge (Expr.Pi $m $α $β) $f) ← h_t_f.render
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

example (h₁ : Judge (Srt 1) α) (h₂ : Judge α x) : Judge α ⸨(I 1) α x⸩ := by
  decide_infer

example (h₁ : Judge (Srt 1) α) (h₂ : Judge α x) : Judge α ⸨(K' 1 1) α α x x⸩ := by
  decide_infer

example (h₁ : Judge (Srt 1) α) (h₂ : Judge ((~> 3) α, (Srt 2)) β)
  (h₃ : Judge α x) (h₄ : Judge ⸨β x⸩ y) : Judge α ⸨(K 1 2) α β x y⸩ := by
  decide_infer

example (h₁ : Judge (Srt m) α) (h₂ : Judge ((~> n.succ) α, (Srt n)) β)
  (h₃ : Judge α x) (h₄ : Judge ⸨β x⸩ y) : Judge α ⸨(K m n) α β x y⸩ := by
  decide_infer
example (h₁ : Judge (Srt m) α) (h₂ : Judge ((~> n.succ) α, (Srt n)) β)
  (h₃ : Judge ((Π' o.succ) α
      , (Π' o.succ) β
      , ⸨next ⸨assert (Srt o)⸩⸩) γ)
  (h₄ : Judge ((Π' o) α, (Π' o) β, γ) x)
  (h₅ : Judge ((Π' n) α, β) y)
  (h₆ : Judge α z) : Judge ⸨γ z ⸨y z⸩⸩ ⸨(S m n o) α β γ x y z⸩ := by
  decide_infer
