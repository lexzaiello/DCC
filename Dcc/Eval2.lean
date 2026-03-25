import Dcc.Ast2

  -- Decreasing measure
-- function arity decreases with each argument
inductive Expr.TySize : Expr → ℕ → Prop
  | fst  : Expr.TySize (SK fst) 1
  | snd  : Expr.TySize (SK snd) 1
  | comp : Expr.TySize f m
    → Expr.TySize g n
    → Expr.TySize (SK f ∘ g) (m + n).succ
  | coup  : Expr.TySize a m
    → Expr.TySize b n
    → Expr.TySize (SK (a, b)) (m + n)
  | pair  : Expr.TySize a m
    → Expr.TySize b n
    → Expr.TySize (SK ⟨a, b⟩) (m + n).succ
  | curr  : Expr.TySize x m
    → Expr.TySize (SK Λ(x)) m.succ
  | nil   : Expr.TySize (SK nil) 0
  | comb  : Expr.TySize (.comb c) 0
  | hole  : Expr.TySize (SK __ ∶ t) 0
  | srt   : Expr.TySize (SK Sort m) 0
  | app   : Expr.TySize f n
    → Expr.TySize x m
    → Expr.TySize (SK (f x)) (n + m)

inductive Expr.RedTy : Expr → Expr → Prop
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
  case comp f g ih₁ ih₂ =>
    have ⟨m, h₁⟩ := ih₁
    have ⟨n, h₂⟩ := ih₂
    exact ⟨(m + n).succ, .comp h₁ h₂⟩
  · exact ⟨0, .nil⟩
  · exact ⟨1, .fst⟩
  · exact ⟨1, .snd⟩
  case curr f ih =>
    have ⟨m, h₁⟩ := ih
    exact ⟨m.succ, .curr h₁⟩
  case coup a b ih₁ ih₂ =>
    have ⟨m, h₁⟩ := ih₁
    have ⟨n, h₂⟩ := ih₂
    exact ⟨m + n, .coup h₁ h₂⟩
  case pair f g ih₁ ih₂ =>
    have ⟨m, h₁⟩ := ih₁
    have ⟨n, h₂⟩ := ih₂
    exact ⟨(m + n).succ, .pair h₁ h₂⟩

theorem Expr.TySize.unique (h₁ : Expr.TySize e n) (h₂ : e.TySize m) : m = n := by
  induction h₁ generalizing m with
  | pair | curr | app | comp | coup =>
    cases h₂; grind only
  | _ => cases h₂; rfl

-- Compute the size of an expression
def Expr.ty_size : Expr → ℕ
  | .fst | .snd => 1
  | .pair f g | .comp f g =>
    let m := f.ty_size
    let n := g.ty_size
    (m + n).succ
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
  · exact .fst
  · exact .snd
  · rename_i x f g
    exact .pair (Expr.TySize.sound (e := f) rfl) (Expr.TySize.sound (e := g) rfl)
  · rename_i x f g
    exact .comp (Expr.TySize.sound (e := f) rfl) (Expr.TySize.sound (e := g) rfl)
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
  | coup hf hx ih₁ ih₂ | pair hf hx ih₁ ih₂ | comp hf hx ih₁ ih₂ | app hf hx ih₁ ih₂ =>
    rw [← ih₁, ← ih₂]
    rfl
  | curr _a ih₁ => rw [← ih₁]; rfl
  | _ => rfl

theorem Expr.RedTy.decreasing (h_red : Expr.RedTy e e') (h_size : e.TySize n) : ∃ m, e'.TySize m ∧ m < n :=
  match heq : h_red with
  | .comp (x := x) (y := y) (z := z) =>
     match h_size with
     | .app (.comp h_t_x h_t_y) h_t_z => ⟨_, Expr.TySize.app h_t_x (.app h_t_y h_t_z), by grind only⟩
  | .fst =>
    match h_size with
    | .app .fst (.coup h_t_a h_t_b) => ⟨_, h_t_a, by grind only⟩
  | .snd =>
    match h_size with
    | .app .snd (.coup h_t_a h_t_b) => ⟨_, h_t_b, by grind only⟩
  | .pair (f := f) (g := g) (a := a) (b := b) =>
    match h_size with
    | .app (.pair h_t_f h_t_g) (.coup h_t_a h_t_b) =>
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

