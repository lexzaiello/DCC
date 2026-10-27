import Dcc.Aff.Relation
import Dcc.Aff.Size
import Dcc.Attrs
import Mathlib.Tactic.IntervalCases

namespace Expr

open Dsl in
inductive Red.Head : Expr → Expr → Type
  | dup            : Red.Head (DCC ((Dup B x) (& env) (& y))) (DCC (x env (,(`(B env) (B env)) y y)))
  | bimap          : Red.Head (DCC ((Map A B f g) (,_B x y))) (DCC (,(`A B) (f x) (g y)))
  | assoc          : Red.Head (DCC ((Assoc A B C) (,_B₁ (,_B₂ x y) z))) (DCC (,(`A ((Σ (`⊤ B) (`⊤ (`B C))) ∗)) x (,(`B C) y z)))
  | eql            : Red.Head (DCC ((Eql f_α) env (,B x y))) (DCC (= (f_α env) x y))
  | map            : Red.Head (DCC ((!<> f) (& x))) (DCC (!(f x)))
  | fmap           : Red.Head (DCC (($<> f) (& x))) (DCC (& (f x)))
  | unbox          : Red.Head (DCC ((* A) (& x))) x
  | pair           : Red.Head (DCC ((⟨,⟩β M N) (& x))) (DCC (,(β x) (M x) (N x (M x))))
  | evalc          : Red.Head (DCC ((Eval _α _β x) (,__β y z))) (DCC (x y z))
  | quot           : Red.Head (DCC ((`β x) y)) x
  | id             : Red.Head (DCC ((Id α) x)) x
  | fstc           : Red.Head (DCC ((Fst _β) (,β a b))) a
  | sndc           : Red.Head (DCC ((Snd _β) (,β a b))) b
  | comp           : Red.Head (DCC ((∘ x y) z)) (DCC (x (y z)))
  | curr           : Red.Head (DCC ((Λ α β x) y z)) (DCC (x (,β y z)))
  | curr'          : Red.Head (DCC ((!Λα β x) (& y) (& z))) (DCC (x (& (,β y z))))
  | swap           : Red.Head (DCC ((Swap A B) (,B₂ x y))) (DCC (,(`B A) y x))
  | ind_bool_true  : Red.Head (DCC ((Bool.Rec motive x y) env True)) (DCC (x env True))
  | ind_bool_false : Red.Head (DCC ((Bool.Rec motive x y) env False)) (DCC (y env False))
deriving Repr

instance : Decreasing (Red.Head) := ⟨fun h => by cases h <;> grind⟩
instance : Unique (Red.Head) := ⟨fun h₁ h₂ => by cases h₁ <;> (cases h₂; rfl)⟩
instance : ProofEq (Red.Head) := ⟨fun h₁ h₂ => by cases h₁ <;> (cases h₂; rfl)⟩

@[dcc_force_reduce, dcc_force_aff, aesop unsafe norm (rule_sets := [DccForceReduce])]
def step_head? (e : Expr) : Option (Σ' e', (Red.Head e e')) :=
  open Dsl in match e with
  | (DCC ((Dup _B _x) (& _env) (& _y))) => .some ⟨_, .dup⟩
  | (DCC ((Map _B _C _f _g) (,__B _x _y))) => .some ⟨_, .bimap⟩
  | (DCC ((Assoc _A _B _C) (,_B₁ (,_B₂ _x _y) _z))) => .some ⟨_, .assoc⟩
  | (DCC ((Bool.Rec _motive _x _y) _env True)) =>
    .some ⟨_, .ind_bool_true⟩
  | (DCC ((Bool.Rec _motive _x _y) _env False)) =>
    .some ⟨_, .ind_bool_false⟩
  | DCC ((!<> _f) (& _x))                                 => .some ⟨_, .map⟩
  | DCC (($<> _f) (& _x))                                 => .some ⟨_, .fmap⟩
  | DCC ((* _α) (& _x))                                 => .some ⟨_, .unbox⟩
  | DCC ((⟨,⟩_β _M _N) (& _x))                        => .some ⟨_, .pair⟩
  | (DCC ((Eval _α _β _x) (,__β _y _z)))            => .some ⟨_, .evalc⟩
  | (DCC ((Eql _f_α) _env (,_B _x _y)))              => .some ⟨_, .eql⟩
  | (DCC ((`_β _x) _y))                             => .some ⟨_, .quot⟩
  | (DCC ((Id _α) _x))                                => .some ⟨_, .id⟩
  | (DCC ((Fst _β) (,_γ _a _b)))                     => .some ⟨_, .fstc⟩
  | (DCC ((Swap _B _C) (,_B₂ _a _b)))                 => .some ⟨_, .swap⟩
  | (DCC ((Snd _β) (,_γ _a _b)))                     => .some ⟨_, .sndc⟩
  | (DCC ((∘ _x _y) _z))                              => .some ⟨_, .comp⟩
  | (DCC ((!Λ _α _β _x) (& _y) (& _z)))                => .some ⟨_, .curr'⟩
  | (DCC ((Λ _α _β _x) _y _z)) => .some ⟨_, .curr⟩
  | _ => .none

instance : Run Option (Red.Head) := ⟨step_head?⟩
instance : Complete' Option (Red.Head) := ⟨fun h => by cases h <;> simp [Run.run, step_head?]⟩

inductive HasRed : Expr → Prop
  | head      : Red.Head e e' → HasRed e
  | point₁    : (hp : Points e [x]) → HasRed x → HasRed e
  | point₂₁   : (hp : Points e [x, y]) → HasRed x → HasRed e
  | point₂₂   : (hp : Points e [x, y]) → HasRed y → HasRed e
  | point₃₁   : (hp : Points e [x, y, z]) → HasRed x → HasRed e
  | point₃₂   : (hp : Points e [x, y, z]) → HasRed y → HasRed e
  | point₃₃   : (hp : Points e [x, y, z]) → HasRed z → HasRed e
  | point₄₁   : (hp : Points e [x, y, z, d]) → HasRed x → HasRed e
  | point₄₂   : (hp : Points e [x, y, z, d]) → HasRed y → HasRed e
  | point₄₃   : (hp : Points e [x, y, z, d]) → HasRed z → HasRed e
  | point₄₄   : (hp : Points e [x, y, z, d]) → HasRed d → HasRed e
  | congr_fun : HasRed f → HasRed (DCC (f x))
  | congr_arg : HasRed x → HasRed (DCC (f x))

def has_red? (e : Expr) : Option (PLift (HasRed e)) :=
  match _heq₁ : e, _heq₂ : points e with
  | e, ⟨[], _h⟩ =>
    match e with
    | DCC (f x) =>
      match step_head? (DCC (f x)) with
      | .some ⟨_, h⟩ => .some ⟨.head h⟩
      | .none =>
        match f.has_red?, x.has_red? with
        | .some ⟨h₁⟩, _ => .some ⟨.congr_fun h₁⟩
        | _, .some ⟨h₁⟩ => .some ⟨.congr_arg h₁⟩
        | _, _ => .none
    | _ => .none
  | e, ⟨[x], h⟩ =>
    match has_red? x with
    | .some ⟨h₂⟩ => .some ⟨.point₁ h h₂⟩
    | _ => .none
  | e, ⟨[x, y], h⟩ =>
    match has_red? x, has_red? y with
    | .some ⟨h₂⟩, _ => .some ⟨.point₂₁ h h₂⟩
    | _, .some ⟨h₂⟩ => .some ⟨.point₂₂ h h₂⟩
    | _, _ => .none
  | e, ⟨[x, y, z], h⟩ =>
    match has_red? x, has_red? y, has_red? z with
    | .some ⟨h₂⟩, _, _ => .some ⟨.point₃₁ h h₂⟩
    | _, .some ⟨h₂⟩, _ => .some ⟨.point₃₂ h h₂⟩
    | _, _, .some ⟨h₂⟩ => .some ⟨.point₃₃ h h₂⟩
    | _, _, _ => .none
  | e, ⟨[x, y, z, d], h⟩ =>
    match has_red? x, has_red? y, has_red? z, has_red? d with
    | .some ⟨h₂⟩, _, _, _ => .some ⟨.point₄₁ h h₂⟩
    | _, .some ⟨h₂⟩, _, _ => .some ⟨.point₄₂ h h₂⟩
    | _, _, .some ⟨h₂⟩, _ => .some ⟨.point₄₃ h h₂⟩
    | _, _, _, .some ⟨h₂⟩ => .some ⟨.point₄₄ h h₂⟩
    | _, _, _, _ => .none
  | e, ⟨_, _⟩ => .none
termination_by sizeOf e
decreasing_by
  any_goals (grind)
  any_goals (exact h.sizeOf (n := ⟨0, by grind⟩) rfl)
  any_goals (exact h.sizeOf (n := ⟨1, by grind⟩) rfl)
  any_goals (exact h.sizeOf (n := ⟨2, by grind⟩) rfl)
  any_goals (exact h.sizeOf (n := ⟨3, by grind⟩) rfl)

def Red.Head.no_points (h : Red.Head e e') : Σ' c, points e = ⟨[], c⟩ := by
  cases h <;> exact ⟨_, by constructor⟩

theorem HasRed.complete (h : HasRed e) : has_red? e = .some ⟨h⟩ := by
  induction h
  case head h =>
    cases h <;> (unfold has_red?; simp [points, step_head?])
  any_goals (
    focus
    try (
      expose_names
      cases hp <;> (unfold has_red?; simp_all [points]; try grind))
    done)
  case congr_fun | congr_arg =>
    unfold has_red?
    simp [points]
    split <;> grind

inductive Red : Expr → Expr → Type
  | head      : Red.Head e e' → Red e e'
  | point₁    : (hp : Points e [x]) → Red x x' → WithPoints e [x] hp [x'] rfl e' → Red e e'
  | point₂₁   : (hp : Points e [x, y]) → Red x x' → WithPoints e [x, y] hp [x', y] rfl e' → Red e e'
  | point₂₂   : (hp : Points e [x, y]) → Red y y' → (¬ HasRed x) → WithPoints e [x, y] hp [x, y'] rfl e' → Red e e'
  | point₃₁   : (hp : Points e [x, y, z]) → Red x x' → WithPoints e [x, y, z] hp [x', y, z] rfl e' → Red e e'
  | point₃₂   : (hp : Points e [x, y, z]) → Red y y' → (¬ HasRed x) → WithPoints e [x, y, z] hp [x, y', z] rfl e' → Red e e'
  | point₃₃   : (hp : Points e [x, y, z]) → Red z z' → (¬ HasRed x) → (¬ HasRed y) → WithPoints e [x, y, z] hp [x, y, z'] rfl e' → Red e e'
  | point₄₁   : (hp : Points e [x, y, z, d]) → Red x x' → WithPoints e [x, y, z, d] hp [x', y, z, d] rfl e' → Red e e'
  | point₄₂   : (hp : Points e [x, y, z, d]) → Red y y' → (¬ HasRed x) → WithPoints e [x, y, z, d] hp [x, y', z, d] rfl e' → Red e e'
  | point₄₃   : (hp : Points e [x, y, z, d]) → Red z z' → (¬ HasRed x) → (¬ HasRed y) → WithPoints e [x, y, z, d] hp [x, y, z', d] rfl e' → Red e e'
  | point₄₄   : (hp : Points e [x, y, z, d]) → Red d d' → (¬ HasRed x) → (¬ HasRed y) → (¬ HasRed z) → WithPoints e [x, y, z, d] hp [x, y, z, d'] rfl e' → Red e e'
  | congr_fun : (∀ e', Red.Head (DCC (f x)) e' → False) → (¬ HasRed x) → Red f f' → Red (DCC (f x)) (DCC (f' x))
  | congr_arg : (∀ e', Red.Head (DCC (f x)) e' → False) → Red x x' → Red (DCC (f x)) (DCC (f x'))
deriving Repr

instance : Decreasing (Red) := ⟨fun h => by
  induction h
  case head h => exact decreasing h
  any_goals (
    case _ hset _ =>
      cases hset <;> grind)⟩

def step? (e : Expr) : Option (Σ' e', Red e e') :=
  match _heq₁ : e, _heq₂ : points e with
  | e, ⟨[], _h⟩ =>
    match e with
    | DCC (f x) =>
      match heq : step_head? (DCC (f x)) with
      | .some ⟨_, h⟩ => .some ⟨_, .head h⟩
      | .none =>
        if heq₂ : x.has_red? = .none then
          match f.step? with
          | .some ⟨_, h⟩ =>
            .some ⟨_, .congr_fun (fun _e' h => by
              have heq := Complete'.complete h
              simp [Run.run] at heq
              grind) (fun h => by simp_all [h.complete]) h⟩
          | .none => .none
        else
          match x.step? with
          | .some ⟨_, h⟩ => .some ⟨_, .congr_arg (fun _e' h => by
              have heq := Complete'.complete h
              simp [Run.run] at heq
              grind) h⟩
          | .none => .none
    | _ => .none
  | e, ⟨[x], h⟩ =>
    match step? x with
    | .some ⟨x', hr⟩ =>
      .some ⟨_, .point₁ h hr (with_points e _ h [x'] rfl).2⟩
    | .none => .none
  | e, ⟨[x, y], h⟩ =>
    match step? x with
    | .some ⟨x', hr⟩ =>
      .some ⟨_, .point₂₁ h hr (with_points e _ h [x', y] rfl).2⟩
    | .none =>
      if heq : x.has_red? = .none then
        match step? y with
        | .some ⟨y', hr⟩ =>
          .some ⟨_, .point₂₂ h hr (fun h => by simp_all [h.complete]) (with_points e _ h [x, y'] rfl).2⟩
        | .none => .none
      else .none
  | e, ⟨[x, y, z], h⟩ =>
    match step? x with
    | .some ⟨x', hr⟩ =>
      .some ⟨_, .point₃₁ h hr (with_points e _ h [x', y, z] rfl).2⟩
    | .none =>
      if heq : x.has_red? = .none then
        match step? y with
        | .some ⟨y', hr⟩ =>
          .some ⟨_, .point₃₂ h hr (fun h => by simp_all [h.complete]) (with_points e _ h [x, y', z] rfl).2⟩
        | .none =>
          if heq : y.has_red? = .none then
            match step? z with
            | .some ⟨z', hr⟩ =>
              .some ⟨_, .point₃₃ h hr (fun h => by simp_all [h.complete]) (fun h => by simp_all [h.complete]) (with_points e _ h [x, y, z'] rfl).2⟩
            | .none => .none
          else .none
      else .none
  | e, ⟨[x, y, z, d], h⟩ =>
    match step? x with
    | .some ⟨x', hr⟩ =>
      .some ⟨_, .point₄₁ h hr (with_points e _ h [x', y, z, d] rfl).2⟩
    | .none =>
      if heq : x.has_red? = .none then
        match step? y with
        | .some ⟨y', hr⟩ =>
          .some ⟨_, .point₄₂ h hr (fun h => by simp_all [h.complete]) (with_points e _ h [x, y', z, d] rfl).2⟩
        | .none =>
          if heq : y.has_red? = .none then
            match step? z with
            | .some ⟨z', hr⟩ =>
              .some ⟨_, .point₄₃ h hr (fun h => by simp_all [h.complete]) (fun h => by simp_all [h.complete]) (with_points e _ h [x, y, z', d] rfl).2⟩
            | .none =>
              if heq : z.has_red? = .none then
                match step? d with
                | .some ⟨d', hr⟩ =>
                  .some ⟨_, .point₄₄ h hr (fun h => by simp_all [h.complete]) (fun h => by simp_all [h.complete]) (fun h => by simp_all [h.complete]) (with_points e _ h [x, y, z, d'] rfl).2⟩
                | .none => .none
              else .none
          else .none
      else .none
  | e, ⟨_, _⟩ => .none
termination_by sizeOf e
decreasing_by
  any_goals (grind)
  any_goals (exact h.sizeOf (n := ⟨0, by grind⟩) rfl)
  any_goals (exact h.sizeOf (n := ⟨1, by grind⟩) rfl)
  any_goals (exact h.sizeOf (n := ⟨2, by grind⟩) rfl)
  any_goals (exact h.sizeOf (n := ⟨3, by grind⟩) rfl)

def Red.has_red (h : Red e e') : HasRed e := by
  induction h
  case head hr => exact .head hr
  case point₁ =>
    expose_names
    exact HasRed.point₁ (by assumption) (by assumption)
  case point₂₁ =>
    expose_names
    exact HasRed.point₂₁ (by assumption) (by assumption)
  case point₂₂ =>
    expose_names
    exact HasRed.point₂₂ (by assumption) (by assumption)
  case point₃₁ =>
    expose_names
    exact HasRed.point₃₁ (by assumption) (by assumption)
  case point₃₂ =>
    expose_names
    exact HasRed.point₃₂ (by assumption) (by assumption)
  case point₃₃ =>
    expose_names
    exact HasRed.point₃₃ (by assumption) (by assumption)
  case point₄₁ =>
    expose_names
    exact HasRed.point₄₁ (by assumption) (by assumption)
  case point₄₂ =>
    expose_names
    exact HasRed.point₄₂ (by assumption) (by assumption)
  case point₄₃ =>
    expose_names
    exact HasRed.point₄₃ (by assumption) (by assumption)
  case point₄₄ =>
    expose_names
    exact HasRed.point₄₄ (by assumption) (by assumption)
  case congr_fun =>
    exact HasRed.congr_fun (by assumption)
  case congr_arg =>
    exact HasRed.congr_arg (by assumption)

def HasRed.none_complete (hn : ¬ HasRed e) : step? e = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨_, h⟩ heq
  exact hn h.has_red

def HasRed.none_complete' (hn : ¬ HasRed e) : has_red? e = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨h⟩
  exact (hn h).elim

instance : Run Option (Red) := ⟨step?⟩

set_option maxHeartbeats 2000000 in
instance : Complete' Option (Red) := ⟨fun h => by
  induction h
  case congr_arg =>
    expose_names
    simp_all [Run.run]
    unfold step?
    simp [points]
    split
    case h_1 => exact (h _ (by assumption)).elim
    case h_2 => simp [a.has_red.complete, a_ih]
  case congr_fun =>
    expose_names
    simp_all [Run.run]
    unfold step?
    simp [points]
    split
    case h_1 => exact (h _ (by assumption)).elim
    case h_2 => simp [HasRed.none_complete' (by assumption), a_ih]
  case point₄₄ =>
    expose_names
    simp_all [Run.run]
    cases a_1; (
      unfold step?
      simp [points]
      have heq₁ := HasRed.none_complete h
      have heq₂ := HasRed.none_complete' h
      have heq₃ := HasRed.none_complete h_1
      have heq₄ := HasRed.none_complete' h_1
      have heq₅ := HasRed.none_complete h_2
      have heq₆ := HasRed.none_complete' h_2
      simp [heq₁, heq₂, heq₃, heq₄, heq₅, heq₆, a_ih, with_points])
  case point₃₃ | point₄₃ =>
    expose_names
    simp_all [Run.run]
    cases a_1 <;> (
      unfold step?
      simp [points]
      have heq₁ := HasRed.none_complete h
      have heq₂ := HasRed.none_complete' h
      have heq₃ := HasRed.none_complete h_1
      have heq₄ := HasRed.none_complete' h_1
      simp [heq₁, heq₂, heq₃, heq₄, a_ih, with_points])
  case point₂₂ | point₃₂ | point₄₂ =>
    expose_names
    simp_all [Run.run]
    cases a_1 <;> (
      unfold step?
      simp [points]
      have heq₁ := HasRed.none_complete (by assumption)
      have heq₂ := HasRed.none_complete' (by assumption)
      simp [heq₁, heq₂, a_ih, with_points])
  case head hr =>
    cases hr <;> (simp [Run.run]; unfold step?; simp [points, step_head?])
  case point₁ | point₂₁ | point₃₁ | point₄₁ =>
    expose_names
    simp_all [Run.run]
    cases a_1 <;> (unfold step?; simp [points, a_ih, with_points])
  ⟩

instance : ProofEq (Red) := ⟨fun h₁ h₂ => by
  have heq₁ := complete h₁
  have heq₂ := complete h₂
  grind⟩
instance : Unique (Red) := ⟨fun h₁ h₂ => by
  have heq₁ := complete h₁
  have heq₂ := complete h₂
  grind⟩

#check conf_global (r := Red)

syntax gen_dcc "→ᵦ" gen_dcc  : term

macro_rules
  | `($A:gen_dcc →ᵦ $B:gen_dcc) => `(AndNorm RedChoiceStar Red (DCC $A) (DCC $B))

instance : Decidable (HasRed e) :=
  match heq : has_red? e with
  | .some ⟨h⟩ => .isTrue h
  | .none => .isFalse (fun h => by simp_all [h.complete])

def IsNorm.head (hn : IsNorm Red e) : ∀ e', Red.Head e e' → False := fun e' hr => hn (.head (by assumption))

set_option maxHeartbeats 2000000 in
theorem HasRed.get (h : HasRed e) : ∃ e' h, (step? e) = .some ⟨e', h⟩ := by
  cases h
  case congr_fun h =>
    have ⟨e', h, heq⟩ := h.get
    unfold step?
    simp [points]
    split
    · exact ⟨_, _, rfl⟩
    · split
      · simp [heq]
      · split
        · exact ⟨_, _, rfl⟩
        · expose_names
          have h_some : x.has_red?.isSome := Option.isSome_iff_ne_none.mpr (by assumption)
          have h : x.HasRed := (x.has_red?.get (by assumption)).down
          have h := h.get
          grind
  case congr_arg h =>
    have ⟨e', hr, heq⟩ := h.get
    unfold step?
    simp [points]
    split
    · exact ⟨_, _, rfl⟩
    · simp [h.complete, heq]
  case head hr =>
    cases hr <;> (unfold step?; simp [points, step_head?])
  case point₁ | point₂₁ | point₃₁ | point₄₁ =>
    expose_names
    cases hp <;> (
      unfold step?
      have ⟨e', h, heq⟩ := h.get
      simp [points, heq])
  case point₂₂ | point₃₂ | point₄₂ =>
    expose_names
    cases hp <;> (
      unfold step?
      simp [points]
      split
      · grind
      · split
        · have ⟨e', h, heq⟩ := h.get
          simp [heq]
        · expose_names
          have h_some : x.has_red?.isSome := Option.isSome_iff_ne_none.mpr h_1
          have h := ((has_red? x).get h_some).down.get
          grind)
  case point₃₃ | point₄₃ =>
    expose_names
    cases hp
    <;> (
      unfold step?
      simp [points]
      split
      · grind
      · split
        · split
          · grind
          · split
            · split
              · grind
              · expose_names
                have ⟨e', h, heq⟩ := h.get
                have h_some : z.has_red?.isSome := Option.isSome_iff_ne_none.mpr (by grind)
                have h := ((has_red? z).get h_some).down.get
                grind
            · expose_names
              have heq := h.complete
              have h_some : y.has_red?.isSome := Option.isSome_iff_ne_none.mpr (by grind)
              have h := ((has_red? y).get h_some).down.get
              grind
        · expose_names
          have heq := h.complete
          have h_some : x.has_red?.isSome := Option.isSome_iff_ne_none.mpr (by grind)
          have h := ((has_red? x).get h_some).down.get
          grind)
  case point₄₄ =>
    expose_names
    cases hp
    · unfold step?
      simp [points]
      split
      · grind
      · split
        · split
          · grind
          · split
            · split
              · grind
              · split
                · have ⟨e', h, heq⟩ := h.get
                  simp [heq]
                · expose_names
                  have h_some : z.has_red?.isSome := Option.isSome_iff_ne_none.mpr (by grind)
                  have h := ((has_red? z).get h_some).down.get
                  grind
            · expose_names
              have h_some : y.has_red?.isSome := Option.isSome_iff_ne_none.mpr (by grind)
              have h := ((has_red? y).get h_some).down.get
              grind
        · expose_names
          have heq := h.complete
          have h_some : x.has_red?.isSome := Option.isSome_iff_ne_none.mpr (by grind)
          have h := ((has_red? x).get h_some).down.get
          grind

def IsNorm.congr_fun (hn : IsNorm Red (DCC? (f x))) : IsNorm Red f := fun _f' hr =>
  if h : (HasRed x) then
    have ⟨_x', hr, _heq⟩ := h.get
    hn (.congr_arg hn.head hr)
  else
    hn (.congr_fun hn.head h hr)

def IsNorm.congr_arg (hn : IsNorm Red (DCC? (f x))) : IsNorm Red x := fun _ hr =>
  hn (.congr_arg hn.head hr)

def IsNorm.point (hn : IsNorm Red e) (hp : Points e ps := by constructor) (heq : p = ps.get n := by simp; try rfl) : IsNorm Red p := fun _ hr => by
  cases heq
  cases hp
  all_goals (fin_cases n)
  any_goals (
    focus
    try (
      simp at hr
      first | exact (hn (.point₂₁ (by constructor) (by assumption) (by constructor)))
            | exact (hn (.point₁ (by constructor) (by assumption) (by constructor)))
            | exact (hn (.point₃₁ (by constructor) (by assumption) (by constructor)))
            | exact (hn (.point₄₁ (by constructor) (by assumption) (by constructor))))
    done)
  any_goals (
    focus
    try (
      simp at hr
      first
      | exact (hn (.point₂₂ (by constructor) hr (fun h => by
        have ⟨_, hr, heq⟩ := h.get
        exact (hn (.point₂₁ (by constructor) hr (by constructor)))) (by constructor)))
      | exact (hn (.point₃₂ (by constructor) hr (fun h => by
        have ⟨_, hr, heq⟩ := h.get
        exact (hn (.point₃₁ (by constructor) hr (by constructor)))) (by constructor)))
      | exact (hn (.point₄₂ (by constructor) hr (fun h => by
        have ⟨_, hr, heq⟩ := h.get
        exact (hn (.point₄₁ (by constructor) hr (by constructor)))) (by constructor))))
    done)
  any_goals (
    focus
    try (
      simp at hr
      first
      | exact (hn (.point₃₃ (by constructor) hr
        (fun h => by
          have ⟨_, hr, heq⟩ := h.get
          exact (hn (.point₃₁ (by constructor) hr (by constructor))))
        (fun h => by
          have ⟨_, hr, heq⟩ := h.get
          exact (hn (.point₃₂ (by constructor) hr (fun h => by
            have ⟨_, hr, heq⟩ := h.get
            exact (hn (.point₃₁ (by constructor) hr (by constructor)))) (by constructor))))
        (by constructor)))
      | exact (hn (.point₄₃ (by constructor) hr
        (fun h => by
          have ⟨_, hr, heq⟩ := h.get
          exact (hn (.point₄₁ (by constructor) hr (by constructor))))
        (fun h => by
          have ⟨_, hr, heq⟩ := h.get
          exact (hn (.point₄₂ (by constructor) hr (fun h => by
            have ⟨_, hr, heq⟩ := h.get
            exact (hn (.point₄₁ (by constructor) hr (by constructor)))) (by constructor))))
        (by constructor))))
    done)
  · simp at hr
    exact (hn (.point₄₄ (by constructor) hr
        (fun h => by
          have ⟨_, hr, heq⟩ := h.get
          exact (hn (.point₄₁ (by constructor) hr (by constructor))))
        (fun h => by
          have ⟨_, hr, heq⟩ := h.get
          exact (hn (.point₄₂ (by constructor) hr (fun h => by
            have ⟨_, hr, heq⟩ := h.get
            exact (hn (.point₄₁ (by constructor) hr (by constructor)))) (by constructor))))
        (fun h => by
          have ⟨_, hr, heq⟩ := h.get
          refine (hn (.point₄₃ (by constructor) hr ?_ ?_ (by constructor)))
          · intro h
            have ⟨_, hr, heq⟩ := h.get
            exact (hn (.point₄₁ (by constructor) hr (by constructor)))
          · intro h
            have ⟨_, hr, heq⟩ := h.get
            refine (hn (.point₄₂ (by constructor) hr ?_ (by constructor)))
            · intro h
              have ⟨_, hr, heq⟩ := h.get
              exact (hn (.point₄₁ (by constructor) hr (by constructor))))
        (by constructor)))

def mk_norm_congr (hn_head : ∀ e', Red.Head (DCC (f x)) e' → False) (hn_f : IsNorm Red f) (hn_x : IsNorm Red x) : IsNorm Red (DCC (f x)) := by
  intro _ h
  cases h
  case head h =>
    exact hn_head _ h
  any_goals (
    focus
    try (
      expose_names
      cases hp)
    done)
  case congr_fun =>
    expose_names
    exact hn_f (by assumption)
  case congr_arg =>
    expose_names
    exact hn_x (by assumption)

def mk_norm₁ (hn₁ : IsNorm Red x) (hp : Points e [x] := by constructor) : IsNorm Red e := fun _ h => by
  cases h
  case head h => cases hp <;> cases h
  case point₁ =>
    expose_names
    cases hp <;> (cases hp_1; exact hn₁ (by assumption))
  any_goals (expose_names; cases hp_1.complete.symm.trans hp.complete)
  case congr_fun | congr_arg => cases hp

def mk_norm₂ (hn₁ : IsNorm Red x) (hn₂ : IsNorm Red y) (hp : Points e [x, y] := by constructor) : IsNorm Red e := fun _ h => by
  cases h
  case head h => cases hp <;> cases h
  case point₂₁ =>
    expose_names
    cases hp <;> (cases hp_1; exact hn₁ (by assumption))
  case point₂₂ =>
    expose_names
    cases hp <;> (cases hp_1; exact hn₂ (by assumption))
  any_goals (expose_names; cases hp_1.complete.symm.trans hp.complete)
  case congr_fun | congr_arg => cases hp

def mk_norm₃ (hn₁ : IsNorm Red x) (hn₂ : IsNorm Red y) (hn₃ : IsNorm Red z) (hp : Points e [x, y, z] := by constructor) : IsNorm Red e := fun _ h => by
  cases h
  case head h => cases hp <;> cases h
  case point₃₁ =>
    expose_names
    cases hp <;> (cases hp_1; exact hn₁ (by assumption))
  case point₃₂ =>
    expose_names
    cases hp <;> (cases hp_1; exact hn₂ (by assumption))
  case point₃₃ =>
    expose_names
    cases hp <;> (cases hp_1; exact hn₃ (by assumption))
  any_goals (expose_names; cases hp_1.complete.symm.trans hp.complete)
  case congr_fun | congr_arg => cases hp

def mk_norm₄ (hn₁ : IsNorm Red x) (hn₂ : IsNorm Red y) (hn₃ : IsNorm Red z) (hn₄ : IsNorm Red d) (hp : Points e [x, y, z, d] := by constructor) : IsNorm Red e := fun _ h => by
  cases h
  case head h => cases hp; cases h
  case point₄₁ =>
    expose_names
    cases hp; (cases hp_1; exact hn₁ (by assumption))
  case point₄₂ =>
    expose_names
    cases hp; (cases hp_1; exact hn₂ (by assumption))
  case point₄₃ =>
    expose_names
    cases hp; (cases hp_1; exact hn₃ (by assumption))
  case point₄₄ =>
    expose_names
    cases hp; (cases hp_1; exact hn₄ (by assumption))
  any_goals (expose_names; cases hp_1.complete.symm.trans hp.complete)
  case congr_fun | congr_arg => cases hp

theorem step_none_no_red (h : step? e = .none) : ¬ e.HasRed := fun h => by
  have ⟨_, _, heq⟩ := h.get
  grind

theorem no_red_norm (hn : ¬ e.HasRed) : IsNorm Red e := fun _ h => by
  have heq := Complete'.complete h
  have h := HasRed.none_complete hn
  simp [Run.run, pure] at heq
  grind

def mk_norm_top : IsNorm Red (DCC ⊤) := fun _ h => by
  cases h
  case head h => nomatch h
  any_goals (
    focus
    expose_names
    cases hp)

def mk_norm_tintro : IsNorm Red (DCC ∗) := fun _ h => by
  cases h
  case head h => nomatch h
  any_goals (
    focus
    expose_names
    cases hp)

def mk_norm_bot : IsNorm Red (DCC ⊥) := fun _ h => by
  cases h
  case head h => nomatch h
  any_goals (
    focus
    expose_names
    cases hp)

def mk_norm_sort : IsNorm Red (DCC Sort m) := fun _ h => by
  cases h
  case head h => nomatch h
  any_goals (
    focus
    expose_names
    cases hp)

/-
Congruences for points and value semantics must be recovered with metatheorems,
since we do not assume them and reduction order is deterministic.

Reduction always proceeds in the following order:

If the expression is an application:
1. Head reduction (e.g., ((Id A) x) = x)
2. Argument reduction (e.g., x →ᵦ x' in (f x) →ᵦ (f x'))
3. Function reduction (e.g., f →ᵦ f' in (f x) →ᵦ (f' x))

If the expression is not an application, reduce the points of the term
from leftmost to rightmost.

The most important congruence to recover is congrArg, since this is common in subject
reduction and other metatheorems related to judgments.

However, this requires deriving all of them.
This is probably possible with mutual recursion.
-/

def RedChoiceStar.point₁
  (hr₁ : RedChoiceStar Red e e')
  (hp : Points e [x])
  (hr₂ : RedChoiceStar Red x x')
  (hp' : WithPoints e [x] hp [x'] rfl C) : Σ (D : Expr), RedChoiceStar Red e D × RedChoiceStar Red C D := by
  sorry

def RedChoiceStar.point
  (hr₁ : RedChoiceStar Red e e')
  (hp : Points e ps)
  (n : ℕ)
  (hlt : n < ps.length)
  (hr₂ : RedChoiceStar Red (ps.get ⟨n, hlt⟩) x')
  (hp' : WithPoints e ps hp (ps.set n x') (by grind) C) : Σ (D : Expr), RedChoiceStar Red e D × RedChoiceStar Red C D := by
  sorry

def Red.argD (h : Red x x') : Σ e', Red (DCC (f x)) e' :=
  match heq : step_head? (DCC (f x)) with
  | .some ⟨e', h⟩ => ⟨_, .head h⟩
  | .none => ⟨_, .congr_arg (fun _ h => by simp_all [complete' h]) h⟩

def Red.next_point (hr : Red y y') (h : Points e (x::y::xs) := by constructor) : Σ e', Red e e' :=
  match heq : step? x with
  | .some ⟨x', hr⟩ => by
    cases h <;> (
      first
      | exact ⟨_, .point₂₁ (by constructor) (by assumption) (by constructor)⟩
      | exact ⟨_, .point₃₁ (by constructor) (by assumption) (by constructor)⟩
      | exact ⟨_, .point₄₁ (by constructor) (by assumption) (by constructor)⟩)
  | .none => by
    have hn : ¬ x.HasRed := step_none_no_red (by assumption)
    cases h <;> (
      first
      | exact ⟨_, .point₂₂ (by constructor) hr hn (by constructor)⟩
      | exact ⟨_, .point₃₂ (by constructor) hr hn (by constructor)⟩
      | exact ⟨_, .point₄₂ (by constructor) hr hn (by constructor)⟩)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
def Red.nth_point (n : ℕ) (hr : Red x₀ x') (h : Points e (x::xs) := by constructor) (hlt : n < (x::xs).length := by grind) (heq : ((x::xs).get ⟨n, hlt⟩) = x₀ := by rfl) : Σ e', Red e e' := by
  cases heq
  cases h
  all_goals (simp at hlt; simp at hr)
  any_goals (
    focus
    try (
      interval_cases n
      <;> (
        first
        | exact ⟨_, .point₁ (by constructor) (by assumption) (by constructor)⟩
        | exact ⟨_, .point₂₁ (by constructor) (by assumption) (by constructor)⟩
        | exact ⟨_, .point₃₁ (by constructor) (by assumption) (by constructor)⟩
        | exact ⟨_, .point₄₁ (by constructor) (by assumption) (by constructor)⟩
        | exact hr.next_point))
    done)
  any_goals (exact ⟨_, .point₁ (by constructor) hr (by constructor)⟩)
  any_goals (
    focus
    try (
      interval_cases n
      · first
        | exact ⟨_, .point₁ (by constructor) (by assumption) (by constructor)⟩
        | exact ⟨_, .point₂₁ (by constructor) (by assumption) (by constructor)⟩
        | exact ⟨_, .point₃₁ (by constructor) (by assumption) (by constructor)⟩
        | exact ⟨_, .point₄₁ (by constructor) (by assumption) (by constructor)⟩
      · exact hr.next_point
      · expose_names
        match heq₁ : step? x with
        | .some ⟨x', hr₀⟩ =>
          first
          | exact ⟨_, .point₁ (by constructor) (by assumption) (by constructor)⟩
          | exact ⟨_, .point₂₁ (by constructor) (by assumption) (by constructor)⟩
          | exact ⟨_, .point₃₁ (by constructor) (by assumption) (by constructor)⟩
          | exact ⟨_, .point₄₁ (by constructor) (by assumption) (by constructor)⟩
        | .none =>
          have hn : ¬ x.HasRed := step_none_no_red (by assumption)
          match heq₂ : step? x_1 with
          | .some ⟨x', hr₀⟩ => exact hr₀.next_point
          | .none =>
            have hn : ¬ x_1.HasRed := step_none_no_red (by assumption)
            first
            | exact ⟨_, .point₃₃ (by constructor) hr (by assumption) (by assumption) (by constructor)⟩
            | exact ⟨_, .point₄₃ (by constructor) hr (by assumption) (by assumption) (by constructor)⟩
      try (
        case _ =>
          expose_names
          match heq₁ : step? x with
          | .some ⟨x', hr₀⟩ =>
            first
            | exact ⟨_, .point₁ (by constructor) (by assumption) (by constructor)⟩
            | exact ⟨_, .point₂₁ (by constructor) (by assumption) (by constructor)⟩
            | exact ⟨_, .point₃₁ (by constructor) (by assumption) (by constructor)⟩
            | exact ⟨_, .point₄₁ (by constructor) (by assumption) (by constructor)⟩
          | .none =>
            have hn : ¬ x.HasRed := step_none_no_red (by assumption)
            match heq₂ : step? x_1 with
            | .some ⟨x', hr₀⟩ => exact hr₀.next_point
            | .none =>
              have hn : ¬ x_1.HasRed := step_none_no_red (by assumption)
              match heq₃ : step? x_2 with
              | .some ⟨x', hr₀⟩ =>
                first
                | exact ⟨_, .point₃₃ (by constructor) (by assumption) (by assumption) (by assumption) (by constructor)⟩
                | exact ⟨_, .point₄₃ (by constructor) (by assumption) (by assumption) (by assumption) (by constructor)⟩
              | .none =>
                have hn : ¬ x_2.HasRed := step_none_no_red (by assumption)
                first
                | exact ⟨_, .point₄₄ (by constructor) (by assumption) (by assumption) (by assumption) (by assumption) (by constructor)⟩
      )))

def Red.nth_point_fst (n : ℕ) (hr : Red x₀ x') (h : Points e (x::xs) := by constructor) (hlt : n < (x::xs).length := by grind) (heq : ((x::xs).get ⟨n, hlt⟩) = x₀ := by rfl) : Red e (Red.nth_point n hr h hlt heq).fst := (Red.nth_point n hr h hlt heq).snd

def Red.funD (h : Red f f') : Σ e', Red (DCC (f x)) e' :=
  match heq : step_head? (DCC (f x)) with
  | .some ⟨e', h⟩ => ⟨_, .head h⟩
  | .none =>
    match heq₂ : step? x with
    | .some ⟨x', h⟩ => ⟨_, .congr_arg (fun _ h => by simp_all [complete' h]) h⟩
    | .none => ⟨_, .congr_fun (fun _ h => by simp_all [complete' h]) (step_none_no_red heq₂) h⟩

theorem Red.step_some (h : Red e e') : (step? e).isSome := by
  have h := complete' h
  grind

def Red.get_point₁ (hr : Red e e') (hp : Points e [x] := by constructor) : Σ (x' : Expr) (_hp' : Points e' [x']), Red x x' := by
  cases hp <;> (
    cases hr
    any_goals (grind [Points])
    case head h => nomatch h
    expose_names
    cases hp
    cases a_1
    exact ⟨_, by constructor, by assumption⟩)

def Red.get_point (hr : Red e e') (hp : Points e (x::xs) := by constructor) : Σ' (n : ℕ) (hlt : n < (x::xs).length) (x' : Expr)
  (_hp' : WithPoints e (x::xs) hp ((x::xs).set n x') (by grind) e'), Red ((x::xs).get ⟨n, hlt⟩) x' := by
  cases hp <;> (
    cases hr
    any_goals (grind [Points])
    case head h => nomatch h
    any_goals (
      expose_names
      cases hp
      cases a_1
      first
      | exact ⟨0, by grind, _, by constructor, a⟩
      | exact ⟨1, by grind, _, by constructor, a⟩
      | exact ⟨2, by grind, _, by constructor, a⟩
      | exact ⟨3, by grind, _, by constructor, a⟩))

def Red.get_point₁_fst (hr : Red e e') (hp : Points e [x] := by constructor) : Red x (Red.get_point₁ hr hp).fst := (Red.get_point₁ hr hp).snd.snd

end Expr
