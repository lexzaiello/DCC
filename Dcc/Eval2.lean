import Dcc.Ast2

/-
Need more equations for dpair.

flip probably necessary.
-/

inductive Expr.IsRedex : Expr → Prop
  | appe      : IsRedex (SK (App (f, x)))
  | ide       : IsRedex (SK (id e))
  | flip      : IsRedex (SK (flip (a, b)))
  | flip'     : IsRedex (SK (flip ⟨a, b⟩))
  | quoted    : IsRedex (SK ((quot e) y))
  | comp      : IsRedex (SK ((x ∘ y) z))
  | fst       : IsRedex (SK (fst (x, y)))
  | snd       : IsRedex (SK (snd (x, y)))
  | curr      : IsRedex (SK (Λ(x) y z))
  | dpair     : IsRedex (SK (⟨f, g⟩ (a, b)))

inductive Expr.HasRedex : Expr → Prop
  | single : Expr.IsRedex a → HasRedex a
  | left   : HasRedex f → HasRedex (SK (f x))
  | right  : HasRedex x → HasRedex (SK (f x))
  | coupl  : HasRedex a → HasRedex (SK (a, b))
  | coupr  : HasRedex b → HasRedex (SK (a, b))

def Expr.is_redex (e : Expr) : Option (PLift e.IsRedex) :=
  match _heq : e with
  | (SK (App (_f, _x))) => .some ⟨.appe⟩
  | (SK (id _e)) => .some ⟨.ide⟩
  | (SK (flip (_a, _b))) => .some ⟨.flip⟩
  | (SK (flip ⟨_a, _b⟩)) => .some ⟨.flip'⟩
  | (SK ((quot _e) _y)) => .some ⟨.quoted⟩
  | (SK ((_x ∘ _y) _z)) => .some ⟨.comp⟩
  | (SK (fst (_x, _y))) => .some ⟨.fst⟩
  | (SK (snd (_x, _y))) => .some ⟨.snd⟩
  | (SK (Λ(_x) _y _z)) => .some ⟨.curr⟩
  | (SK (⟨_f, _g⟩ (_a, _b))) => .some ⟨.dpair⟩
  | _ => .none

def Expr.has_redex (e : Expr) : Option (PLift e.HasRedex) :=
  match _heq : e.is_redex with
  | .some ⟨h⟩ => .some ⟨.single h⟩
  | .none => match e with
    | (SK (f, x)) => match _heq₂ : f.has_redex, _heq₃ : x.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.coupl h⟩
      | _, .some ⟨h⟩ => .some ⟨.coupr h⟩
      | _, _ => .none
    | (SK (f x)) => match _heq₂ : f.has_redex, _heq₃ : x.has_redex with
      | .some ⟨h⟩, _ => .some ⟨.left h⟩
      | _, .some ⟨h⟩ => .some ⟨.right h⟩
      | _, _ => .none
    | _e => .none

@[simp] theorem Expr.HasRedex.sound (_h : Expr.has_redex e = .some he) : Expr.HasRedex e := he.down

theorem Expr.IsRedex.sound (_h : Expr.is_redex e = .some he) : Expr.IsRedex e := he.down

theorem Expr.IsRedex.complete (h : Expr.IsRedex e) : Expr.is_redex e = .some (.up h) := by
  unfold Expr.is_redex
  split
  repeat rfl
  cases h
  repeat simp_all
  · rename_i f g a b h
    exact h _ _ _ _ rfl rfl rfl rfl

theorem Expr.HasRedex.complete (h : Expr.HasRedex e) : Expr.has_redex e = .some (.up h) := by
  unfold Expr.has_redex
  split
  · simp_all only
  case h_2 =>
    cases heq : h with
    | coupl | left =>
      rename_i ha _
      have heq := ha.complete
      simp_all only
      split
      · repeat rfl
      · repeat rfl
      · rename_i ih₁ ih₂
        exact False.elim <| ih₁ ha heq
    | coupr | right =>
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

@[simp] theorem Expr.HasRedex.sound' (_h : Expr.has_redex e = .none) : ¬ Expr.HasRedex e := fun h => by
  have h := h.complete
  simp_all only [reduceCtorEq]

theorem Expr.IsRedex.sound' (_h : Expr.is_redex e = .none) : ¬ Expr.IsRedex e := fun h => by
  have h := h.complete
  simp_all only [reduceCtorEq]

instance Expr.IsRedex.instDecidable : Decidable (Expr.IsRedex e) :=
  if h : e.is_redex.isSome then
    .isTrue (e.is_redex.get h).down
  else
    .isFalse (fun h => absurd h (Expr.IsRedex.sound' (by simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none])))

instance Expr.HasRedex.instDecidable : Decidable (Expr.HasRedex e) :=
  if h : e.has_redex.isSome then
    .isTrue (e.has_redex.get h).down
  else
    .isFalse (fun h => absurd h (Expr.HasRedex.sound' (by simp_all only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, sound'])))

@[simp] theorem Expr.HasRedex.some_complete (h : Expr.HasRedex e) : (Expr.has_redex e).isSome := by
  have heq := h.complete
  simp_all only [Option.isSome_some]

@[simp] theorem Expr.HasRedex.complete' (h : ¬ Expr.HasRedex e) : Expr.has_redex e = .none := by
  have h : ¬ ∃ h, e.has_redex = .some ⟨h⟩ := fun ⟨hp, heq⟩ => by
    have h : e.HasRedex := Expr.HasRedex.sound heq
    contradiction
  cases h₂ : e.has_redex with
  | none => rfl
  | some val => exfalso; exact h ⟨val.down, by simp_all only [IsEmpty.exists_iff, not_false_eq_true]⟩

-- Decreasing measure
-- function arity decreases with each argument
inductive Expr.TySize : Expr → ℕ → Prop
  | appe   : Expr.TySize (SK App) 1
  | ide    : Expr.TySize (SK id) 1
  | quoted : Expr.TySize (SK quot) 1
  | flip   : Expr.TySize (SK flip) 1
  | fst    : Expr.TySize (SK fst) 1
  | snd    : Expr.TySize (SK snd) 1
  | compe  : Expr.TySize (SK (∘)) 1
  | coup   : Expr.TySize a m
    → Expr.TySize b n
    → Expr.TySize (SK (a, b)) (m + n)
  | dpair  : Expr.TySize (SK pair) 1
  | curr   : Expr.TySize (SK (Λ)) 1
  | nil    : Expr.TySize (SK nil) 0
  | comb   : Expr.TySize (.comb c) 0
  | hole   : Expr.TySize (SK __ ∶ t) 0
  | srt    : Expr.TySize (SK Sort m) 0
  | app    : Expr.TySize f n
    → Expr.TySize x m
    → Expr.TySize (SK (f x)) (n + m)

inductive Expr.RedTy : Expr → Expr → Prop
  | coup      : Expr.RedTy x x'
    → Expr.RedTy (SK (x, y)) (SK (x', y))
  | coup'     : (¬ Expr.HasRedex x)
    → Expr.RedTy y y'
    → Expr.RedTy (SK (x, y)) (SK (x, y'))
  | appe      : Expr.RedTy (SK (App (f, x))) (SK (f x))
  | ide       : Expr.RedTy (SK (id e)) e
  | flip      : Expr.RedTy (SK (flip (a, b))) (SK (b, a))
  | flip'     : Expr.RedTy (SK (flip ⟨a, b⟩)) (SK ⟨b, a⟩)
  | quoted    : Expr.RedTy (SK ((quot e) y)) e
  | comp      : Expr.RedTy (SK ((x ∘ y) z)) (SK (x (y z)))
  | fst       : Expr.RedTy (SK (fst (x, y))) x
  | snd       : Expr.RedTy (SK (snd (x, y))) y
  | curr      : Expr.RedTy (SK ((Λ(x) y z))) (SK (x (y, z)))
  | dpair     : Expr.RedTy (SK (⟨f, g⟩ (a, b))) (SK ((f a), (g b)))
  | congrFun  : ¬ Expr.HasRedex x
    → ¬ Expr.IsRedex (SK (f x))
    → Expr.RedTy f f'
    → Expr.RedTy (SK (f x)) (SK (f' x))
  | congrArg  : ¬ Expr.IsRedex (SK (f x))
    → Expr.RedTy x x'
    → Expr.RedTy (SK (f x)) (SK (f x'))

theorem Expr.all_size : ∃ n, Expr.TySize e n := by
  induction e
  · exact ⟨0, .hole⟩
  · exact ⟨0, .srt⟩
  · exact ⟨0, .comb⟩
  case app f x ih₁ ih₂ =>
    have ⟨n, hn⟩ := ih₁
    have ⟨m, hm⟩ := ih₂
    exact ⟨n + m, .app hn hm⟩
  case compe => exact ⟨1, .compe⟩
  · exact ⟨1, .appe⟩
  · exact ⟨0, .nil⟩
  · exact ⟨1, .quoted⟩
  · exact ⟨1, .flip⟩
  · exact ⟨1, .ide⟩
  · exact ⟨1, .fst⟩
  · exact ⟨1, .snd⟩
  · exact ⟨1, .curr⟩
  case coup a b ih₁ ih₂ =>
    have ⟨m, h₁⟩ := ih₁
    have ⟨n, h₂⟩ := ih₂
    exact ⟨m + n, .coup h₁ h₂⟩
  case dpair => exact ⟨1, .dpair⟩

theorem Expr.TySize.unique (h₁ : Expr.TySize e n) (h₂ : e.TySize m) : m = n := by
  induction h₁ generalizing m with
  | quoted | curr | app | coup =>
    cases h₂; grind only
  | _ => cases h₂; rfl

-- Compute the size of an expression
def Expr.ty_size : Expr → ℕ
  | .curr | .App | .id | .flip | .quot | .compe | .dpair | .fst | .snd => 1
  | .coup a b =>
    let m := a.ty_size
    let n := b.ty_size
    (m + n)
  | .nil | .comb _c | .tyhole _m | .Srt _m => 0
  | .app f x =>
    let m := f.ty_size
    let n := x.ty_size
    m + n

theorem Expr.TySize.sound : Expr.ty_size e = n → Expr.TySize e n := by
  intro h
  unfold Expr.ty_size at h
  rw [← h]
  split at h
  · exact .curr
  · exact .appe
  · exact .ide
  · exact .flip
  · exact .quoted
  · exact .compe
  · exact .dpair
  · exact .fst
  · exact .snd
  · rename_i a b
    exact .coup (Expr.TySize.sound (e := a) rfl) (Expr.TySize.sound (e := b) rfl)
  · exact .nil
  · exact .comb
  · exact .hole
  · exact .srt
  · rename_i x₁ f x
    exact .app (Expr.TySize.sound (e := f) rfl) (Expr.TySize.sound (e := x) rfl)

theorem Expr.TySize.complete : Expr.TySize e n → Expr.ty_size e = n := by
  intro h
  induction h with
  | coup hf hx ih₁ ih₂ | app hf hx ih₁ ih₂ =>
    rw [← ih₁, ← ih₂]
    rfl
  | _ => rfl

theorem Expr.RedTy.decreasing (h_red : Expr.RedTy e e') (h_size : e.TySize n) : ∃ m, e'.TySize m ∧ m < n :=
  match heq : h_red with
  | .coup' (x := x) (y := y) h_n_r h_r_y =>
    let ⟨n_x', h_size_y', h_lt⟩ := h_r_y.decreasing (TySize.sound rfl)
    let h := Expr.TySize.sound (e := y) rfl
    match h_size with
    | .coup h_n_x h_n_y =>
      let h := TySize.unique (e := y) h h_n_y
      ⟨_, .coup h_n_x h_size_y', by simp_all only [heq_eq_eq, add_lt_add_iff_left]⟩
  | .coup (x := x) (y := y) h_r_x =>
    let ⟨n_x', h_size_x', h_lt⟩ := h_r_x.decreasing (TySize.sound rfl)
    let h := Expr.TySize.sound (e := x) rfl
    match h_size with
    | .coup h_n_x h_n_y =>
      let h := TySize.unique (e := x) h h_n_x
      ⟨_, .coup h_size_x' h_n_y, by simp_all only [heq_eq_eq, add_lt_add_iff_right]⟩
  | .appe (f := f) (x := x) =>
    match h_size with
    | .app .appe (.coup h_t_f h_t_x) =>
      ⟨_, .app h_t_f h_t_x, by grind only⟩
  | .ide (e := e) =>
    match h_size with
    | .app .ide h_t_e =>
      ⟨_, h_t_e, by grind only⟩
  | .flip' (a := a) (b := b) =>
    match h_size with
    | .app .flip (.app (.app .dpair h_t_a) h_t_b) =>
      ⟨_, .app (.app .dpair h_t_b) h_t_a, by grind only⟩
  | .flip (a := a) (b := b) =>
    match h_size with
    | .app .flip (.coup h_t_a h_t_b) =>
      ⟨_, .coup h_t_b h_t_a, by grind only⟩
  | .quoted (e := e) =>
    match h_size with
    | .app (.app .quoted h_t_x) _ => ⟨_, h_t_x, by grind only⟩
  | .comp (x := x) (y := y) (z := z) =>
     match h_size with
     | .app (.app (.app .compe h_t_x) h_t_y) h_t_z => ⟨_, Expr.TySize.app h_t_x (.app h_t_y h_t_z), by grind only⟩
  | .fst =>
    match h_size with
    | .app .fst (.coup h_t_a h_t_b) => ⟨_, h_t_a, by grind only⟩
  | .snd =>
    match h_size with
    | .app .snd (.coup h_t_a h_t_b) => ⟨_, h_t_b, by grind only⟩
  | .dpair (f := f) (g := g) (a := a) (b := b) =>
    match h_size with
    | .app (.app (.app .dpair h_t_f) h_t_g) (.coup h_t_a h_t_b) =>
      ⟨_, .coup (.app h_t_f h_t_a) (.app h_t_g h_t_b), by grind only⟩
  | .curr (x := x) (y := y) (z := z) =>
    match h_size with
    | .app (.app (.app .curr h_t_x) h_t_y) h_t_z =>
      ⟨_, .app h_t_x (.coup h_t_y h_t_z), by grind only⟩
  | .congrArg (f := f) (x := x) (x' := x') h_n_r_all h_r_x =>
    match h_size with
    | .app hn_f hn_x (n := m) =>
      have ⟨n', hx, h₁⟩ := h_r_x.decreasing hn_x
      ⟨m + n', .app hn_f hx, by simp_all only [heq_eq_eq, add_lt_add_iff_left]⟩
  | .congrFun (f := f) (f' := f') h_n_r_all h_n_r_x h_r_f =>
    match h_size with
    | .app hn_f hn_x (m := n) =>
      have ⟨m, hf, h₁⟩ := h_r_f.decreasing hn_f
      ⟨m + n, .app hf hn_x, by simp_all only [heq_eq_eq, add_lt_add_iff_right]⟩

def Expr.RedTyTrans := Relation.TransGen Expr.RedTy

theorem Expr.RedTyTrans.decreasing (h_red : Expr.RedTyTrans a b) (hn : a.TySize n) : ∃ m, b.TySize m ∧ m < n := by
  induction h_red
  · rename_i hr
    exact hr.decreasing hn
  · rename_i b c htrans hr ih
    have ⟨m, hbm₁, hbm₂⟩ := ih
    have ⟨mc, hcm₁, hcm₂⟩ := hr.decreasing hbm₁
    exact ⟨mc, hcm₁, by grind only⟩

theorem Expr.RedTy.decreasing' (h_red : Expr.RedTy e e') : e'.ty_size < e.ty_size := by
  have ⟨m, h, hp⟩ := Expr.RedTy.decreasing h_red (Expr.TySize.sound (e := e) (n := e.ty_size) rfl)
  exact h.complete.symm ▸ hp

theorem Expr.RedTyTrans.decreasing' (h_red : Expr.RedTyTrans e e') : e'.ty_size < e.ty_size := by
  have ⟨m, h, hp⟩ := Expr.RedTyTrans.decreasing h_red (Expr.TySize.sound (e := e) (n := e.ty_size) rfl)
  exact h.complete.symm ▸ hp

instance : WellFoundedRelation Expr := ⟨fun x y => x.ty_size < y.ty_size, (measure (fun e => Expr.ty_size e)).wf⟩

def Expr.RedTyReflTrans := Relation.ReflTransGen Expr.RedTy

def Expr.IsNorm (e : Expr) : Prop := ¬ ∃ e', RedTy e e'

def Expr.step? (e : Expr) : Option ((e' : Expr) × (PLift (e.RedTy e'))) :=
  if h : e.IsRedex then
    match _heq : e with
    | (SK (App (f, x))) => .some ⟨SK (f x), ⟨.appe⟩⟩
    | (SK (id e)) => .some ⟨e, ⟨.ide⟩⟩
    | (SK (flip (a, b))) => .some ⟨SK (b, a), ⟨.flip⟩⟩
    | (SK (flip ⟨a, b⟩)) => .some ⟨SK ⟨b, a⟩, ⟨.flip'⟩⟩
    | (SK ((quot e) _y)) => .some ⟨e, ⟨.quoted⟩⟩
    | (SK ((x ∘ y) z)) => .some ⟨(SK (x (y z))), ⟨.comp⟩⟩
    | (SK (fst (x, _y))) => .some ⟨x, ⟨.fst⟩⟩
    | (SK (snd (_x, y))) => .some ⟨y, ⟨.snd⟩⟩
    | (SK ((Λ(x) y z))) => .some ⟨SK (x (y, z)), ⟨.curr⟩⟩
    | (SK (⟨f, g⟩ (a, b))) => .some ⟨(SK ((f a), (g b))), ⟨.dpair⟩⟩
  else
    match e with
    | (SK (a, b)) =>
      if h : ¬ a.HasRedex then
        match b.step? with
        | .some ⟨b', ⟨hr⟩⟩ => .some ⟨SK (a, b'), ⟨.coup' (fun h => by
          simp_all only [not_true_eq_false]) hr⟩⟩
        | .none => .none
      else match a.step? with
        | .some ⟨a', ⟨hr⟩⟩ => .some ⟨SK (a', b), ⟨.coup hr⟩⟩
        | .none => .none
    | (SK (f x)) =>
      if h₀ : ¬ (SK (f x)).IsRedex then
        if h₁ : (SK (f x)).HasRedex then
          if h : x.has_redex.isNone then
            match f.step? with
            | .some ⟨f', ⟨hf⟩⟩ => .some ⟨(SK (f' x)), ⟨.congrFun (fun h => by
              have h := h.complete
              simp_all only [Option.isNone_iff_eq_none, reduceCtorEq]
              ) h₀ hf⟩⟩
            | .none => .none
          else match x.step? with
            | .some ⟨x', ⟨hx⟩⟩ => .some ⟨(SK (f x')), ⟨.congrArg h₀ hx⟩⟩
            | .none => .none
        else .none
      else .none
    | _a => .none

def Expr.step?_sound (_h : Expr.step? e = .some ⟨e', he⟩) : Expr.RedTy e e' := he.down

-- Full beta-reduction. We use our decreasing measure to recurse.
-- termination_by e is also possible. It infers ty_size due to our WellfoundedRelation
-- instance.
def Expr.reduce (e : Expr) : Expr :=
  match _heq : step? e with
  | .some ⟨e', ⟨hr⟩⟩ =>
    -- This hypothesis allows the recursion. Easy to prove.
    have _h_size : e'.ty_size < e.ty_size := hr.decreasing'
    e'.reduce
  | .none => e
termination_by e.ty_size

-- Every reduction corresponds to a constructor of reflexive transitive closure of single-step reduction
theorem reduce_sound : Expr.reduce e = e' → Expr.RedTyReflTrans e e' := by
  intro h
  unfold Expr.reduce at h
  split at h
  · simp_all only
    rename_i e'' hr heq
    have _h_size : e''.ty_size < e.ty_size := (Expr.step?_sound heq).decreasing'
    exact .trans (.single (Expr.step?_sound heq)) (reduce_sound h)
  · rename_i heq
    exact h.symm ▸ .refl
termination_by e.ty_size

-- Congruence implies that the size of the entire expression decreases.
theorem app_step_size_decrease : Expr.RedTy f f' → Expr.RedTy x x' → (SK (f' x')).ty_size < (SK (f x)).ty_size := by
  intro ha hb
  have h : f'.ty_size < f.ty_size := ha.decreasing'
  have h : x'.ty_size < x.ty_size := hb.decreasing'
  induction ha generalizing x'
  repeat (unfold Expr.ty_size; grind)

theorem step?_decreasing (_h_step : Expr.step? e = .some ⟨e', h⟩) : e'.ty_size < e.ty_size :=
  h.down.decreasing'

@[simp] theorem no_redex_appl : ¬ Expr.HasRedex (SK (f x)) → ¬ f.HasRedex := fun h hno => by
  exact h (Expr.HasRedex.left hno (x := x))

@[simp] theorem no_redex_appr : ¬ Expr.HasRedex (SK (f x)) → ¬ x.HasRedex := fun h hno => by
  exact h (Expr.HasRedex.right hno (x := x))

@[simp] theorem no_redex_coupl : ¬ Expr.HasRedex (SK (f, x)) → ¬ f.HasRedex := fun h hno => by
  exact h (Expr.HasRedex.coupl hno (a := f))

@[simp] theorem no_redex_coupr : ¬ Expr.HasRedex (SK (f, x)) → ¬ x.HasRedex := fun h hno => by
  exact h (Expr.HasRedex.coupr hno (b := x))

@[simp] theorem no_redex_appl_contra : ¬ Expr.HasRedex (SK (f x)) → f.HasRedex → False := fun h hf => by
  exact absurd hf (no_redex_appl h)

@[simp] theorem no_redex_appr_contra : ¬ Expr.HasRedex (SK (f x)) → x.HasRedex → False := fun h hf => by
  exact absurd hf (no_redex_appr h)

@[simp] theorem no_redex_coupl_contra : ¬ Expr.HasRedex (SK (f, x)) → f.HasRedex → False := fun h hf => by
  exact absurd hf (no_redex_coupl h)

@[simp] theorem no_redex_coupr_contra : ¬ Expr.HasRedex (SK (f, x)) → x.HasRedex → False := fun h hf => by
  exact absurd hf (no_redex_coupr h)

@[simp] theorem no_redex_no_step : ¬ Expr.HasRedex e → ¬ ∃ e', e.RedTy e' := by
  intro h ⟨e', hr⟩
  induction hr
  · simp_all only [imp_false, not_not]
    exact no_redex_coupl_contra h (by assumption)
  · simp_all only [imp_false, not_not]
    exact no_redex_coupr_contra h (by assumption)
  · exact h (.single .appe)
  · exact h (.single .ide)
  · exact h (.single .flip)
  · exact h (.single .flip')
  · exact h (.single .quoted)
  · exact h (.single .comp)
  · exact h (.single .fst)
  · exact h (.single .snd)
  · exact h (.single .curr)
  · exact h (.single .dpair)
  · rename_i x f f' hrx hrf ih
    simp_all only [imp_false, not_not]
    exact no_redex_appl_contra h (by assumption)
  · rename_i x x' f hrx hrf ih
    simp_all only [imp_false, not_not]
    exact no_redex_appr_contra h (by assumption)

@[simp] theorem no_redex_no_step' : ¬ Expr.HasRedex e → ∀ e', ¬ e.RedTy e' := by
  intro h e' hr
  exact no_redex_no_step h ⟨e', hr⟩

@[simp] theorem no_redex_step_none : ¬ Expr.HasRedex e → Expr.step? e = .none := fun h => by
  have h := no_redex_no_step h
  cases heq : e.step?
  · simp_all only [not_false_eq_true, no_redex_no_step', exists_false]
  · rename_i h' val
    have ⟨e', ⟨hp⟩⟩ := val
    exact False.elim <| h ⟨e', hp⟩

@[simp] theorem Expr.RedTy.has_redex : Expr.RedTy e e' → e.HasRedex := fun h => by
  induction h
  · exact Expr.HasRedex.coupl (by assumption)
  · exact Expr.HasRedex.coupr (by assumption)
  · exact .single .appe
  · exact .single .ide
  · exact .single .flip
  · exact .single .flip'
  · exact .single .quoted
  · exact .single .comp
  · exact .single .fst
  · exact .single .snd
  · exact .single .curr
  · exact .single .dpair
  · exact Expr.HasRedex.left (by assumption)
  · exact Expr.HasRedex.right (by assumption)

theorem Expr.IsRedex.can_step : Expr.IsRedex e → ∃ e', e.RedTy e' := by
  intro h
  cases h
  · exact ⟨_, .appe⟩
  · exact ⟨_, .ide⟩
  · exact ⟨_, .flip⟩
  · exact ⟨_, .flip'⟩
  · exact ⟨_, .quoted⟩
  · exact ⟨_, .comp⟩
  · exact ⟨_, .fst⟩
  · exact ⟨_, .snd⟩
  · exact ⟨_, .curr⟩
  · exact ⟨_, .dpair⟩

theorem Expr.RedTy.size_pos (h_step : Expr.RedTy e e') : 0 < e.ty_size := by
  have h := h_step.decreasing'
  omega

def Expr.RedTy.complete (h_step : Expr.RedTy e e') : Expr.step? e = .some ⟨e', ⟨h_step⟩⟩ := by
  if h_top_red : e.IsRedex then
    induction h_step
    case congrArg =>
      contradiction
    case congrFun =>
      contradiction
    · contradiction
    · contradiction
    repeat rfl
  else
    match e with
    | SK (a, b) =>
      have h : ¬ (SK (a, b)).IsRedex := fun h => by cases h
      have h₁ := h_step.has_redex
      unfold Expr.step?
      simp [h]
      cases h_step : h_step
      cases h_red : h₁
      · rename_i h_redex
        simp_all
      · rename_i h_redex
        simp_all
        rename_i h
        simp [h.complete]
      rename_i h _ _
      simp [h.has_redex, h.complete]
      simp_all
      rename_i h
      simp [h.complete]
    | SK (a b) =>
      cases h_step
      · exfalso; exact h_top_red .appe
      · exfalso; exact h_top_red .ide
      · exfalso; exact h_top_red .flip
      · exfalso; exact h_top_red .flip'
      · exfalso; exact h_top_red .quoted
      · exfalso; exact h_top_red .comp
      · exfalso; exact h_top_red .fst
      · exfalso; exact h_top_red .snd
      · exfalso; exact h_top_red .curr
      · exfalso; exact h_top_red .dpair
      case congrFun f' h_f'' h_n_red h_n_e_red =>
        unfold Expr.step?
        simp [h_n_e_red]
        constructor
        apply HasRedex.left
        exact h_f''.has_redex
        have h := Expr.HasRedex.complete' h_n_red
        simp [h, h_f''.complete]
      case congrArg x h_r_x h_n_e_red =>
        unfold Expr.step?
        simp [h_n_e_red]
        constructor
        apply HasRedex.right
        exact h_r_x.has_redex
        have h := HasRedex.complete h_r_x.has_redex
        simp [h, h_r_x.complete]

theorem Expr.RedTy.unique : Expr.RedTy a b → Expr.RedTy a c → b = c := by
  intro hr₁ hr₂
  have heq₁ := hr₁.complete
  have heq₂ := hr₂.complete
  simp_all

-- Normal forms reduce to themselves
theorem Expr.IsNorm.reduce_rfl : Expr.IsNorm e → e.reduce = e := by
  intro h_norm
  unfold Expr.reduce
  split
  · rename_i heq
    have h := Expr.step?_sound heq
    rename_i e''
    exfalso
    exact h_norm ⟨_, h⟩
  rfl

-- Single-step reduct of a reduces to the reduction of a
theorem Expr.RedTy.reduce_same : Expr.RedTy a b → reduce a = reduce b := by
  intro ha
  conv =>
    left
    unfold reduce
    rfl
  split
  · rename_i e' heq
    simp [ha.unique (Expr.step?_sound heq)]
  · have h := ha.complete
    simp_all

-- Church-rosser for our reduction function. Implies church-rosser for the predicate version, since we have soundness.
theorem Expr.RedTyTrans.reduce_same : Expr.RedTyTrans a b → Expr.RedTyTrans a c → reduce b = reduce c := by
  intro h₁ h₂
  induction h₁ generalizing c
  · induction h₂ generalizing b
    · rename_i b₁ hr₁ b₂ hr₂
      have ha := hr₁.reduce_same
      have hb := hr₂.reduce_same
      simp_all
    · rename_i b₁ hrr₁ b₂ c htrans hb₂ ih
      rw [ih]
      exact hb₂.reduce_same
      exact b₂
  · rename_i b₁ c₁ htrans hr₂ ih
    have h := ih h₂
    rw [← h]
    have h := hr₂.reduce_same
    simp_all

theorem Expr.RedTyTrans.complete : Expr.RedTyTrans a b → Expr.reduce a = Expr.reduce b := by
  intro h
  induction h
  · exact Expr.RedTy.reduce_same (by assumption)
  · rename_i h _
    have h := h.reduce_same
    simp_all

-- This proof shows that if the reduct under transitive closure of b is a normal form,
-- then reduce produces the same result.
theorem Expr.RedTyTrans.complete' : Expr.RedTyTrans a b → IsNorm b → Expr.reduce a = b := by
  intro ha hnorm
  induction ha
  · rename_i _ hr
    simp [hr.reduce_same]
    unfold Expr.reduce
    split
    · exfalso
      exact hnorm ⟨_, Expr.step?_sound (by assumption)⟩
    · rfl
  · rename_i b₂ c htrans hrb ih
    have h := hrb.complete
    change Expr.RedTyTrans a b₂ at htrans
    rw [htrans.complete]
    unfold Expr.reduce
    split
    · simp_all
      unfold Expr.reduce
      split
      · simp
        exfalso
        exact hnorm ⟨_, Expr.step?_sound (by assumption)⟩
      · rfl
    simp_all

theorem reduce_norm : Expr.reduce e = e' → Expr.IsNorm e' := by
  intro h ⟨e'', hr⟩
  unfold Expr.reduce at h
  split at h
  · rename_i e'' heq h_step
    have h_dec : e''.ty_size < e.ty_size:= (Expr.step?_sound h_step).decreasing'
    exact reduce_norm h (⟨_, hr⟩)
  · rename_i hstep
    rw [h] at hstep
    have h := hr.complete
    simp_all only [reduceCtorEq]
termination_by e.ty_size

-- Strong normalization of single-step reduction using our decreasing measure.
def Expr.RedTy.SN (e : Expr) : Acc (fun b a => Expr.RedTy a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing'
  exact Expr.RedTy.SN e')
termination_by e.ty_size

-- Strong normalization of transitive closure of single-step reduction using our decreasing measure.
def Expr.RedTyTrans.SN (e : Expr) : Acc (fun b a => Expr.RedTyTrans a b) e := Acc.intro e (fun e' hr => by
  have h := hr.decreasing'
  exact Expr.RedTyTrans.SN e')
termination_by e.ty_size

theorem no_ty_step_norm : Expr.step? t = .none → Expr.IsNorm t := by
  intro h
  exact (fun ⟨e', hn⟩ => by have h := hn.complete; simp_all only [reduceCtorEq])

theorem Expr.RedTyTrans.no_step? : Expr.step? t = .none → ¬ Expr.RedTyTrans t t' := by
  intro h
  have h := no_ty_step_norm h
  exact (fun h => by
    induction h
    · exact h ⟨_, by assumption⟩
    · assumption)
