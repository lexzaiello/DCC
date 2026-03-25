import Dcc.Ast2

/-
Need more equations for dpair.

flip probably necessary.
-/

-- Decreasing measure
-- function arity decreases with each argument
inductive Expr.TySize : Expr → ℕ → Prop
  | quoted : Expr.TySize (SK quot) 1
  | flip   : Expr.TySize (SK flip) 1
  | fst    : Expr.TySize (SK fst) 1
  | snd    : Expr.TySize (SK snd) 1
  | comp   : Expr.TySize (SK B) 1
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
  | flip      : Expr.RedTy (SK (flip (a, b))) (SK (b, a))
  | quoted    : Expr.RedTy (SK ((quot e) y)) e
  | comp      : Expr.RedTy (SK ((x ∘ y) z)) (SK (x (y z)))
  | fst       : Expr.RedTy (SK (fst (x, y))) x
  | snd       : Expr.RedTy (SK (snd (x, y))) y
  | curr      : Expr.RedTy (SK ((Λ(x) y z))) (SK (x (y, z)))
  | pair      : Expr.RedTy (SK (⟨f, g⟩ (a, b))) (SK ((f a), (g b)))
  | congrFun  : Expr.RedTy f f'
    → Expr.RedTy (SK (f x)) (SK (f' x))

theorem Expr.all_size : ∃ n, Expr.TySize e n := by
  induction e
  · exact ⟨0, .hole⟩
  · exact ⟨0, .srt⟩
  · exact ⟨0, .comb⟩
  case app f x ih₁ ih₂ =>
    have ⟨n, hn⟩ := ih₁
    have ⟨m, hm⟩ := ih₂
    exact ⟨n + m, .app hn hm⟩
  case comp => exact ⟨1, .comp⟩
  · exact ⟨0, .nil⟩
  · exact ⟨1, .quoted⟩
  · exact ⟨1, .flip⟩
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
  | .flip | .quot | .comp | .dpair | .fst | .snd => 1
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
  · exact .flip
  · exact .quoted
  · exact .comp
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
  | .flip (a := a) (b := b) =>
    match h_size with
    | .app .flip (.coup h_t_a h_t_b) =>
      ⟨_, .coup h_t_b h_t_a, by grind only⟩
  | .quoted (e := e) =>
    match h_size with
    | .app (.app .quoted h_t_x) _ => ⟨_, h_t_x, by grind only⟩
  | .comp (x := x) (y := y) (z := z) =>
     match h_size with
     | .app (.app (.app .comp h_t_x) h_t_y) h_t_z => ⟨_, Expr.TySize.app h_t_x (.app h_t_y h_t_z), by grind only⟩
  | .fst =>
    match h_size with
    | .app .fst (.coup h_t_a h_t_b) => ⟨_, h_t_a, by grind only⟩
  | .snd =>
    match h_size with
    | .app .snd (.coup h_t_a h_t_b) => ⟨_, h_t_b, by grind only⟩
  | .pair (f := f) (g := g) (a := a) (b := b) =>
    match h_size with
    | .app (.app (.app .dpair h_t_f) h_t_g) (.coup h_t_a h_t_b) =>
      ⟨_, .coup (.app h_t_f h_t_a) (.app h_t_g h_t_b), by grind only⟩
  | .curr (x := x) (y := y) (z := z) =>
    match h_size with
    | .app (.app (.curr h_t_x) h_t_y) h_t_z =>
      ⟨_, .app h_t_x (.coup h_t_y h_t_z), by grind only⟩
  | .congrFun (f := f) (f' := f') h_r_f =>
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
  | (SK (flip (a, b))) => (SK (b, a))
  | (SK ((quot e) _y)) => e
  | (SK ((x ∘ y) z)) => (SK (x (y z)))
  | (SK (fst (x, _y))) => x
  | (SK (snd (_x, y))) => y
  | (SK ((Λ(x) y z))) => (SK (x (y, z)))
  | (SK (⟨f, g⟩ (a, b))) => (SK ((f a), (g b)))
  | (SK (f x)) =>
    match f.step? with
    | .some f' => (SK (f' x))
    | .none => .none
  | _a => .none

def Expr.step?_sound : Expr.step? e = .some e' → Expr.RedTy e e' := by
  unfold Expr.step?
  split
  · intro h; simp only [Option.some.injEq] at h
    rw [← h]
    exact RedTy.flip
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
    exact RedTy.pair
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
  unfold Expr.step?
  split
  · cases h
    · rfl
    · rename_i h
      cases h
  · cases h
    · rfl
    · rename_i h
      cases h
      rename_i h
      cases h
  · cases h
    · rfl
    · rename_i h
      cases h
      · rename_i h
        cases h
        · rename_i h
          cases h
  · cases h
    · rfl
    · rename_i h
      cases h
  · cases h
    · rfl
    · rename_i h
      cases h
  · cases h
    · rfl
    · rename_i h
      cases h
      rename_i h
      cases h
  · cases h
    · rfl
    · rename_i h
      cases h
      rename_i h
      · cases h
        rename_i h
        cases h
  · cases h
    repeat simp_all
    · rename_i ih
      exact False.elim <| ih _ _ _ _ rfl rfl rfl rfl
    · rename_i h_r_f
      simp only [h_r_f.step?_complete]
  · cases h; repeat simp_all

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
