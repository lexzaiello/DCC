import Dcc.Ast2

inductive Expr.IsRedexTm : Expr → Prop
  | k' : IsRedexTm (SK (K'.{[m, n]} α β x y))
  | k  : IsRedexTm (SK (K.{[m, n]} α β x y))
  | s  : IsRedexTm (SK (S.{[m, n, o]} α β γ x y z))

inductive Expr.HasRedexTm : Expr → Prop
  | single : Expr.IsRedexTm a → HasRedexTm a
  | left   : HasRedexTm f     → HasRedexTm (SK (f x))
  | right  : HasRedexTm x     → HasRedexTm (SK (f x))

inductive Expr.RedTm : Expr → Expr → Prop
  | k        : RedTm (SK (K.{[m, n]} α β x y)) x
  | k'       : RedTm (SK (K'.{[m, n]} α β x y)) x
  | s        : RedTm (SK (S.{[m, n, o]} α β γ x y z)) (SK ((x z) (y z)))
  | congrFun  : ¬ Expr.HasRedexTm x
    → ¬ Expr.IsRedexTm (SK (f x))
    → Expr.RedTm f f'
    → Expr.RedTm (SK (f x)) (SK (f' x))
  | congrArg  : ¬ Expr.IsRedexTm (SK (f x))
    → Expr.RedTm x x'
    → Expr.RedTm (SK (f x)) (SK (f x'))

def Expr.is_redex_tm (e : Expr) : Option (PLift e.IsRedexTm) :=
  match _heq : e with
  | (SK (K'.{[_m, _n]} _α _β _x _y)) => .some ⟨.k'⟩
  | (SK (K.{[_m, _n]} _α _β _x _y)) => .some ⟨.k⟩
  | (SK (S.{[_m, _n, _o]} _α _β _γ _x _y _z)) => .some ⟨.s⟩
  | _ => .none

theorem Expr.IsRedexTm.sound (_h : Expr.is_redex_tm e = .some he) : Expr.IsRedexTm e := he.down

theorem Expr.IsRedexTm.complete (h : Expr.IsRedexTm e) : Expr.is_redex_tm e = .some (.up h) := by
  match h with
  | s | k | k' =>
    simp only [Expr.is_redex_tm]

theorem Expr.IsRedexTm.sound' (_h : Expr.is_redex_tm e = .none) : ¬ Expr.IsRedexTm e := fun h => by
  have h := h.complete
  simp_all only [reduceCtorEq]

instance Expr.IsRedexTm.instDecidable : Decidable (Expr.IsRedexTm e) :=
  if h : e.is_redex_tm.isSome then
    .isTrue (e.is_redex_tm.get h).down
  else
    .isFalse (fun h => absurd h (Expr.IsRedexTm.sound' (by simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none])))

def Expr.has_redex_tm (e : Expr) : Option (PLift e.HasRedexTm) :=
  match _heq : e.is_redex_tm with
  | .some ⟨h⟩ => .some ⟨.single h⟩
  | .none => match e with
    | (SK (f x)) => match _heq₂ : f.has_redex_tm, _heq₃ : x.has_redex_tm with
      | .some ⟨h⟩, _ => .some ⟨.left h⟩
      | _, .some ⟨h⟩ => .some ⟨.right h⟩
      | _, _ => .none
    | _e => .none

theorem Expr.HasRedexTm.complete (h : Expr.HasRedexTm e) : Expr.has_redex_tm e = .some (.up h) := by
  unfold Expr.has_redex_tm
  split
  · simp_all only
  case h_2 =>
    cases heq : h with
    | left =>
      rename_i ha _
      have heq := ha.complete
      simp_all only
      split
      · repeat rfl
      · repeat rfl
      · rename_i ih₁ ih₂
        exact False.elim <| ih₁ ha heq
    | right =>
      rename_i ha _
      have heq := ha.complete
      simp_all only
      split
      · repeat rfl
      · repeat rfl
      · rename_i ih₁ ih₂
        exact False.elim <| ih₂ ha heq
    | single =>
      rename_i h
      have h := h.complete
      simp_all only [reduceCtorEq]

@[simp] theorem Expr.HasRedexTm.sound' (_h : Expr.has_redex_tm e = .none) : ¬ Expr.HasRedexTm e := fun h => by
  have h := h.complete
  simp_all only [reduceCtorEq]

instance Expr.HasRedexTm.instDecidable : Decidable (Expr.HasRedexTm e) :=
  if h : e.has_redex_tm.isSome then
    .isTrue (e.has_redex_tm.get h).down
  else
    .isFalse (fun h => absurd h (Expr.HasRedexTm.sound' (by simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, sound'])))

def Expr.step_tm? (e : Expr) : Option ((e' : Expr) × (PLift (e.RedTm e'))) :=
  if h_redex : e.IsRedexTm then
    match _heq : e with
    | (SK (K.{[_m, _n]} _α _β x _y)) => .some ⟨x, ⟨.k⟩⟩
    | (SK (K'.{[_m, _n]} _α _β x _y)) => .some ⟨x, ⟨.k'⟩⟩
    | (SK (S.{[_m, _n, _o]} _α _β _γ x y z)) => .some ⟨(SK ((x z) (y z))), ⟨.s⟩⟩
  else
    match e with
    | (SK (f x)) =>
      if h₀ : ¬ (SK (f x)).IsRedexTm then
        if h₁ : (SK (f x)).HasRedexTm then
          if h : x.has_redex_tm.isNone then
            match f.step_tm? with
            | .some ⟨f', ⟨hf⟩⟩ => .some ⟨(SK (f' x)), ⟨.congrFun (fun h => by
              have h := h.complete
              simp_all only [Option.isNone_iff_eq_none, reduceCtorEq]
              ) h₀ hf⟩⟩
            | .none => .none
          else match x.step_tm? with
            | .some ⟨x', ⟨hx⟩⟩ => .some ⟨(SK (f x')), ⟨.congrArg h₀ hx⟩⟩
            | .none => .none
        else .none
      else .none
    | _a => .none

def Expr.step_tm?_sound (_h : Expr.step_tm? e = .some ⟨e', he⟩) : Expr.RedTm e e' := he.down
