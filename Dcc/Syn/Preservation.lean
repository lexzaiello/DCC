import Dcc.Syn.JudgePi
import Dcc.Syn.Confluence

syntax "gen_reduce" : tactic
syntax "convpi" : tactic
syntax "subst" : tactic

theorem gen_imp_well_typed : Judge α x → (gen α).fst = β → Judge β x := fun h_t h_g =>
  Judge.conv h_t ⟨β, gen.sound h_g, .refl⟩

theorem gen_pi {m : Level} {α β x : Expr} : ∃ α' β', (gen ⸨((Π' m) α, β) x⸩).fst = ((Π' m) α', β') := by
  cases h₁ : (gen ⸨((Π' m) α, β) x⸩).fst with
  | _ =>
    unfold gen at h₁
    repeat split at h₁
    simp_all

inductive gen.eq : Expr → Expr → Prop
  | step  : (gen a).fst = b → gen.eq a b
  | trans : gen.eq a b → gen.eq b c → gen.eq a c

def judge.step_gen : Judge α x → gen.eq α β → Judge β x := by
  intro h_t h_eq
  induction h_eq with
  | step => exact gen_imp_well_typed (by assumption) (by assumption)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ (by assumption))

inductive gen.judge_conv : Expr → Expr → Prop
  | zero : Judge α x → judge_conv α x
  | succ : gen.judge_conv α₂ x → (gen α₁).fst = α₂ → gen.judge_conv α₁ x

def gen.n_norm (n : ℕ) (e : Expr) : ((e' : Expr) × (PLift <| gen.eq e e')) :=
  match n with
  | .zero => ⟨(gen e).fst, ⟨gen.eq.step (a := e) (b := (gen e).fst) rfl⟩⟩
  | .succ n =>
    let ⟨inner, ⟨h⟩⟩ := gen.n_norm n e
    ⟨(gen inner).fst, ⟨gen.eq.trans h (.step (b := (gen inner).fst) rfl)⟩⟩

def gen.judge_conv.judge : gen.judge_conv α x → Judge α x := by
  intro h
  induction h with
  | zero h => exact h
  | succ ih h_gen h_t =>
    apply Judge.conv
    assumption
    case succ α₂ h α₁ =>
      exact ⟨α₂, .refl, gen.sound h_gen⟩

@[simp] theorem judge_self : ∃ C, ParRed a C ∧ ParRed a C :=
  ⟨a, .refl, .refl⟩

macro_rules
  | `(tactic| subst) => `(tactic| exact ⟨_, .app (.app (.Pi .refl .refl .refl) .refl) .refl, .refl⟩)
  | `(tactic| convpi) => `(tactic| exact ⟨_, ParRed.Pi .refl .refl .refl, .refl⟩)
  | `(tactic| gen_reduce) => `(tactic| exact ⟨(gen _).fst, (gen _).snd.down.hpar, by
    unfold gen
    split
    exact ParRed.refl⟩ )

open Expr

theorem I_well_typed (h_α : Judge (Srt m) α) (h_x : Judge α x) : Judge α ⸨(I m) α x⸩ := by
  apply Judge.conv
  apply Judge.app
  apply Judge.conv
  apply Judge.app
  apply Judge.I
  assumption
  refine ⟨Srt m, .refl, .refl⟩
  apply ParRed.Pi .refl .refl
  exact ParRed.refl
  refine ⟨_, .Pival (.read .refl) .refl, .refl⟩
  assumption
  refine ⟨_, .refl, .refl⟩
  exact ParRed.assert .refl
  exact ⟨_, .refl, .refl⟩

@[simp] theorem arrows_well_typed {n : Level} {α β : Expr} : Judge (Srt n) ((~> n) α, β) := by
  apply Judge.conv
  apply Judge.Pi
  exact ⟨_, .refl, .refl⟩

theorem assert_n' {n : ℕ} {fn : Expr} : ∃ e₁ e₂ e₃ e₄, ParRed ⸨(assert_n n.succ fn) x y⸩ e₁ ∧ ParRed e₁ e₂ ∧ ParRed e₂ e₃ ∧ ParRed e₃ e₄ ∧ ParRed e₄ ⸨(assert_n n fn) x⸩ := by
  unfold assert_n
  induction n with
  | zero | succ n h =>
    simp_all
    refine ⟨_, .app (.app' .refl .refl .refl) .refl, ?_⟩
    refine ⟨_, .app (.app (.read .refl) .refl) .refl, ?_⟩
    refine ⟨_, (.app (.app (.assert .refl) .refl) (.refl)), ?_⟩
    exact ⟨_, .assert .refl, .refl⟩

#eval Std.ToFormat.format <| (gen.n_norm 6 ⸨(K.type 2 3) .hole⸩).fst

theorem gen_pi_eq : gen.eq ((Pi m α β).app x) (Pi m (α.app x) (β.app x)) := by
  apply gen.eq.step
  unfold gen
  repeat split
  simp_all
  
  sorry

theorem K.type.eval₁ {m n : Level} {α : Expr} : gen.eq ⸨(K.type m n) α⸩ ((Π' m) ⸨(Srt m) α⸩,
 ((Π' m) ((Π' n.succ) α, ⸨assert (Srt n)⸩),
  ((Π' m) ⸨assert α⸩,
   ((Π' m) ⸨⸨⸨$ read⸩ assert⸩ ⸨next read⸩⸩, ⸨assert ⸨assert ⸨⸨read ⸨⸨assert assert⸩ α⸩⸩ ⸨read α⸩⸩⸩⸩)))) := by
 unfold K.type
 

theorem K.well_typed (h_α : Judge (Srt m) α) (h_β : Judge ((~> n.succ) α, (Srt n)) β)
  (h_x : Judge α x) (h_y : Judge ⸨β x⸩ y) : Judge α ⸨(K m n) α β x y⸩ := by
  have ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ := assert_n' (x := α) (y := β) (n := 2) (fn := .read)
  apply Judge.app
  apply Judge.app
  apply Judge.app
  apply Judge.app
  apply Judge.K
  assumption
  exact judge_self
  exact gen.sound heq₁
  assumption
  refine ⟨_, ?_, .refl⟩
  
