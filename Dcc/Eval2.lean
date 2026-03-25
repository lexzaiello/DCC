import Dcc.Ast2

/-
Need more equations for dpair.

flip probably necessary.
-/

inductive Expr.HasRedex : Expr → Prop
  | appe      : HasRedex (SK (App (f, x)))
  | ide       : HasRedex (SK (id e))
  | flip      : HasRedex (SK (flip (a, b)))
  | quoted    : HasRedex (SK ((quot e) y))
  | comp      : HasRedex (SK ((x ∘ y) z))
  | fst       : HasRedex (SK (fst (x, y)))
  | snd       : HasRedex (SK (snd (x, y)))
  | curr      : HasRedex (SK (Λ(x) y z))
  | dpair     : HasRedex (SK (⟨f, g⟩ (a, b)))
  | left      : HasRedex f → HasRedex (SK (f x))

def Expr.has_redex (e : Expr) : Option (PLift e.HasRedex) :=
  match _heq : e with
  | (SK (App (_f, _x))) => .some ⟨.appe⟩
  | (SK (id _e)) => .some ⟨.ide⟩
  | (SK (flip (_a, _b))) => .some ⟨.flip⟩
  | (SK ((quot _e) _y)) => .some ⟨.quoted⟩
  | (SK ((_x ∘ _y) _z)) => .some ⟨.comp⟩
  | (SK (fst (_x, _y))) => .some ⟨.fst⟩
  | (SK (snd (_x, _y))) => .some ⟨.snd⟩
  | (SK (Λ(_x) _y _z)) => .some ⟨.curr⟩
  | (SK (⟨_f, _g⟩ (_a, _b))) => .some ⟨.dpair⟩
  | (SK (f _x)) => match _heq₂ : f.has_redex with
    | .some ⟨h⟩ => .some ⟨.left h⟩
    | .none => .none
  | _e => .none

theorem Expr.HasRedex.sound (_h : Expr.has_redex e = .some he) : Expr.HasRedex e := he.down

theorem Expr.HasRedex.complete (h : Expr.HasRedex e) : Expr.has_redex e = .some (.up h) := by
  unfold Expr.has_redex
  split
  repeat rfl
  case h_10 =>
    cases heq : h with
    | dpair =>
      cases h
      · simp_all only [reduceCtorEq, app.injEq, false_and, true_and, implies_true, coup.injEq, imp_false, not_and,
    and_imp]
        rename_i h
        exact False.elim <| h _ _ _ _ rfl rfl rfl rfl
      · simp_all only [reduceCtorEq, app.injEq, false_and, true_and, implies_true, coup.injEq, imp_false, not_and,
    and_imp]
        rename_i h
        exact False.elim <| h _ _ _ _ rfl rfl rfl rfl
    | left _ =>
      rename_i hf
      rw [hf.complete]
    | _ => simp_all
  cases h
  repeat simp_all

-- Decreasing measure
-- function arity decreases with each argument
inductive Expr.TySize : Expr → ℕ → Prop
  | appe   : Expr.TySize (SK App) 1
  | ide    : Expr.TySize (SK id) 1
  | quoted : Expr.TySize (SK quot) 1
  | flip   : Expr.TySize (SK flip) 1
  | fst    : Expr.TySize (SK fst) 1
  | snd    : Expr.TySize (SK snd) 1
  | compe  : Expr.TySize (SK comp) 1
  | coup   : Expr.TySize a m
    → Expr.TySize b n
    → Expr.TySize (SK (a, b)) (m + n)
  | dpair  : Expr.TySize (SK pair) 1
  | curr   : Expr.TySize x m
    → Expr.TySize (SK Λ(x)) m.succ
  | nil    : Expr.TySize (SK nil) 0
  | comb   : Expr.TySize (.comb c) 0
  | hole   : Expr.TySize (SK __ ∶ t) 0
  | srt    : Expr.TySize (SK Sort m) 0
  | app    : Expr.TySize f n
    → Expr.TySize x m
    → Expr.TySize (SK (f x)) (n + m)

inductive Expr.RedTy : Expr → Expr → Prop
  | coup      : ¬ Expr.HasRedex y
    → Expr.RedTy x x'
    → Expr.RedTy (SK (x, y)) (SK (x', y))
  | coup'     : ¬ Expr.HasRedex x
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
    → Expr.RedTy f f'
    → Expr.RedTy (SK (f x)) (SK (f' x))
  | congrArg  : ¬ Expr.HasRedex f
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
  · rename_i ih
    let ⟨_, ih⟩ := ih
    exact ⟨_, .curr ih⟩
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
  | .App | .id | .flip | .quot | .compe | .dpair | .fst | .snd => 1
  | .curr x =>
    let m := x.ty_size
    m.succ
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
  · exact .appe
  · exact .ide
  · exact .flip
  · exact .quoted
  · exact .compe
  · exact .dpair
  · exact .fst
  · exact .snd
  · rename_i x
    exact .curr (Expr.TySize.sound (e := x) rfl)
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
  | curr _a ih₁ => rw [← ih₁]; rfl
  | _ => rfl

theorem Expr.RedTy.decreasing (h_red : Expr.RedTy e e') (h_size : e.TySize n) : ∃ m, e'.TySize m ∧ m < n :=
  match heq : h_red with
  | .coup' (x := x) (y := y) h_r_y h_r_x =>
    let ⟨n_x', h_size_y', h_lt⟩ := h_r_x.decreasing (TySize.sound rfl)
    let h := Expr.TySize.sound (e := y) rfl
    match h_size with
    | .coup h_n_x h_n_y =>
      let h := TySize.unique (e := y) h h_n_y
      ⟨_, .coup h_n_x h_size_y', by simp_all only [heq_eq_eq, add_lt_add_iff_left]⟩
  | .coup (x := x) (y := y) h_r_y h_r_x =>
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
    | .app (.app (.curr h_t_x) h_t_y) h_t_z =>
      ⟨_, .app h_t_x (.coup h_t_y h_t_z), by grind only⟩
  | .congrArg (f := f) (x := x) (x' := x') h_n_r_f h_r_x =>
    match h_size with
    | .app hn_f hn_x (n := m) =>
      have ⟨n', hx, h₁⟩ := h_r_x.decreasing hn_x
      ⟨m + n', .app hn_f hx, by simp_all only [heq_eq_eq, add_lt_add_iff_left]⟩
  | .congrFun (f := f) (f' := f') h_n_r_x h_r_f =>
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

def Expr.step? (e : Expr) : Option Expr :=
  match e with
  | (SK (a, b)) =>
    match a.step? with
    | .some a' => .some (SK (a', b))
    | .none => match b.step? with
      | .some b' => .some (SK (a, b'))
      | .none => .none
  | (SK (App (f, x))) => (SK (f x))
  | (SK (id e)) => e
  | (SK (flip (a, b))) => (SK (b, a))
  | (SK (flip ⟨a, b⟩)) => (SK ⟨b, a⟩)
  | (SK ((quot e) _y)) => e
  | (SK ((x ∘ y) z)) => (SK (x (y z)))
  | (SK (fst (x, _y))) => x
  | (SK (snd (_x, y))) => y
  | (SK ((Λ(x) y z))) => (SK (x (y, z)))
  | (SK (⟨f, g⟩ (a, b))) => (SK ((f a), (g b)))
  | (SK (f x)) =>
    match f.step? with
    | .some f' => (SK (f' x))
    | .none => match x.step? with
      | .some x' => (SK (f x'))
      | .none => .none
  | _a => .none

def Expr.step?_sound : Expr.step? e = .some e' → Expr.RedTy e e' := by
  unfold Expr.step?
  split
  · intro h;
    split at h
    · rename_i h_e_step
      simp at h; rw [← h]
      exact RedTy.coup (Expr.step?_sound h_e_step)
    · contradiction
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.appe
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.ide
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.flip
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.flip'
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.quoted
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.comp
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.fst
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.snd
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.curr
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.dpair
  · intro h
    split at h
    · simp_all only [imp_false, Option.some.injEq]
      rename_i fheq
      exact h.symm ▸ (RedTy.congrFun (Expr.step?_sound fheq))
    · contradiction
  · intro h; contradiction

-- Full beta-reduction. We use our decreasing measure to recurse.
-- termination_by e is also possible. It infers ty_size due to our WellfoundedRelation
-- instance.
def Expr.reduce (e : Expr) : Expr :=
  match heq : step? e with
  | .some e' =>
    -- This hypothesis allows the recursion. Easy to prove.
    have _h_size : e'.ty_size < e.ty_size := (Expr.step?_sound heq).decreasing'
    e'.reduce
  | .none => e
termination_by e.ty_size

-- Every reduction corresponds to a constructor of reflexive transitive closure of single-step reduction
theorem reduce_sound : Expr.reduce e = e' → Expr.RedTyReflTrans e e' := by
  intro h
  unfold Expr.reduce at h
  split at h
  · rename_i e'' heq
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

theorem step?_decreasing : Expr.step? e = .some e' → e'.ty_size < e.ty_size := fun h =>
  (Expr.step?_sound h).decreasing'

def Expr.RedTy.step?_complete : Expr.RedTy e e' → Expr.step? e = .some e' := fun h => by
  induction h with
  | congrFun h_r_f ih =>
    unfold Expr.step?
    split
    · rename_i heq
      cases heq
    repeat (rename_i heq; cases heq; cases ih)
    · rename_i heq
      cases heq
      simp_all only [imp_false]
    simp_all only [reduceCtorEq, implies_true, app.injEq, imp_false, not_and, forall_apply_eq_imp_iff, forall_eq']
  | _ => unfold Expr.step?; simp_all only

theorem Expr.RedTy.unique : Expr.RedTy a b → Expr.RedTy a c → b = c := by
  intro hr₁ hr₂
  have heq₁ := hr₁.step?_complete
  have heq₂ := hr₂.step?_complete
  simp_all

-- Normal forms reduce to themselves
theorem Expr.IsNorm.reduce_rfl : Expr.IsNorm e → e.reduce = e := by
  intro h
  unfold Expr.reduce
  split
  · rename_i heq
    have h := Expr.step?_sound heq
    rename_i h_norm e''
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
  · have h := ha.step?_complete
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
    have h := hrb.step?_complete
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
  · rename_i e'' h_step
    have h_dec : e''.ty_size < e.ty_size:= (Expr.step?_sound h_step).decreasing'
    exact reduce_norm h (⟨_, hr⟩)
  · rename_i hstep
    have h := hr.step?_complete
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
  exact (fun ⟨e', hn⟩ => by have h := hn.step?_complete; simp_all only [reduceCtorEq])

theorem Expr.RedTyTrans.no_step? : Expr.step? t = .none → ¬ Expr.RedTyTrans t t' := by
  intro h
  have h := no_ty_step_norm h
  exact (fun h => by
    induction h
    · exact h ⟨_, by assumption⟩
    · assumption)
