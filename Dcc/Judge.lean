import Dcc.Attrs
import Dcc.Ast
import Dcc.Types
import Dcc.Aff.Red
import Dcc.Eta.Red
import Dcc.Relation
import Mathlib.Logic.Relation

namespace Expr

inductive Reduces : Expr → Expr → Prop
  | mk : Relation.ReflTransGen RedAff A B
    → IsNorm RedAff B
    → Relation.ReflTransGen RedEta B C
    → IsNorm RedEta C
    → Reduces A C

def reduce_all := reduce' RedEta ∘ reduce' RedAff

@[dcc_reduce, aesop safe forward (rule_sets := [DccReduce])] theorem Reduces.unique : Reduces A B → Reduces A C → B = C := fun ⟨a, b, c, d⟩ ⟨g, h, i, j⟩ => by
  have ha := norm_unique a b g h
  exact norm_unique c d (ha ▸ i) j

@[aesop safe destruct (rule_sets := [DccReduce])] theorem Reduces.unique' (h₁ : Reduces A B) (h₂ : Reduces A C) : h₁ ≍ h₂ := by
  have h := h₁.unique h₂
  cases h
  congr

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])] theorem Reduces.complete : Reduces A B → reduce_all A = B :=
  fun ⟨ha, hb, hc, hd⟩ => by
    unfold reduce_all
    unfold reduce'
    cases reduce_complete_fst ha hb; cases reduce_complete_fst hc hd; rfl

--@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])] theorem

def reduce_reduces (h : reduce_all A = B) : Reduces A B := ⟨
  reduce_sound rfl,
  reduce_norm rfl,
  h ▸ (reduce_sound rfl),
  h ▸ (reduce_norm rfl)⟩

def reduce_reduces' : Reduces A (reduce_all A) := reduce_reduces rfl

@[dcc_judge, inline] abbrev arrow.matcher (t : Expr) : Option ((α β : Expr) × (m : Level) × PULift.{1, 0} (t = (DCC (α : Sort m) → β))) :=
  match heq₀ : t with
  | DCC (Π(Id(Sort m), Λ(_a, _b, `(_c, β))) α) =>
    if heq₁ : t = (DCC (α : Sort m) → β) then
      .some ⟨α, β, m, ⟨by rw [← heq₀, heq₁]⟩⟩
    else
      .none
  | _ => .none

def is_arrow (e : Expr) : Bool :=
  (arrow.matcher e).isSome

@[dcc_judge, inline] abbrev fst.f_β.type.matcher (t : Expr) : Option ((α δ : Expr) × (m n o : Level) × (PULift.{1, 0} (t = fst.f_β.type α δ m n o))) :=
  match arrow.matcher t with
  | .some ⟨δ, arr', o, ⟨h_arr⟩⟩ =>
    match arrow.matcher arr' with
    | .some ⟨α, DCC Sort n, m, ⟨h_arr₂⟩⟩ =>
      .some ⟨α, δ, m, n, o, ⟨by rw [h_arr, h_arr₂]⟩⟩
    | _ => .none
  | _ => .none

#eval Std.format <| pair.β.type (DCC (Sort 30)) 10 20

/-

-/

@[dcc_judge, inline] abbrev pair.β.type.matcher (t α : Expr) (m : Level) : Option ((n : Level) × (PULift.{1, 0} (t = pair.β.type α m n))) :=
  match arrow.matcher t with
  | .some ⟨_srt, t', _mm,  ⟨_heq⟩⟩ =>
    match arrow.matcher t' with
    | .some ⟨_α₂, DCC Sort n, _m, ⟨_heq₂⟩⟩ =>
      if h : t = pair.β.type α m n then
        .some ⟨n, ⟨h⟩⟩
      else .none
    | _ => .none
  | _ => .none

@[dcc_judge, inline] abbrev curr.β.type.matcher (t : Expr) : Option
  ((α : Expr) × (m n : Level) × (PULift.{1, 0} (t = curr.β.type α m n))) :=
  match arrow.matcher t with
  | .some ⟨α, DCC Sort n, m, ⟨h_arr⟩⟩ =>
    .some ⟨α, m, n, ⟨by rw [h_arr]⟩⟩
  | _ => .none

inductive Judge : Expr → Expr → Prop where
  | id     : Judge α (DCC Sort m)
    → Reduces (id.type α m) τ
    → Judge (DCC Id(α)) τ
  | comp'  : Judge g (DCC ((α : Sort m) → β))
    → Judge f (DCC (Π(Id(Sort n), γ) β))
    → Reduces (comp'.type α β γ g m) τ
    → Judge (DCC f ∘ g) τ
  /-
    f_β δ : α → Sort n
    Fst(f_β, δ) : Σ(f_β) δ → α
  -/
  | fst    : Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (fst.type α f_β δ o) τ
    → Judge (DCC Fst(f_β)) τ
  /-
    f_β δ : α → Sort n
    Snd(f_β, δ) : ∀ (s : Σ(f_β) δ), f_β δ ∘ Fst
  -/
  | snd    : Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (snd.type f_β δ o) τ
    → Judge (DCC Snd(f_β)) τ
  | sigma   : Judge f_β (fst.f_β.type α δ m n o)
    → Reduces (Sigma.type δ m n o) τ
    → Judge (DCC Σ(f_β)) τ
  | snd'   : Judge α (DCC Sort m)
    → Judge β (DCC Sort n)
    → Reduces (snd'.type α β m n) τ
    → Judge (DCC Snd'(α, β)) τ
  | coup   : Judge x α
    → Judge y τ₂
    → Judge β (curr.β.type α m n)
    → Reduces (DCC (β x)) τ₂
    → Reduces (coup.type β) τ
    → Judge (DCC ⟦β⟧(x, y)) τ
  /-
    Λ(β, x)
    β receives (α, x)
    β : Coup(Sort m, Id(Sort m)) → Sort n
  -/
  | curr   : Judge β (curr.β.type α m n)
    → Judge x (DCC (Π(f_α, γ) x_α))
    → Reduces (DCC Coup(β)) τα
    → Reduces (DCC (f_α x_α)) τα
    → Reduces (curr.type α β (DCC (γ x_α)) m) τ
    → Judge (DCC Λ(α, β, x)) τ
  | quot   : Judge x α
    → Judge β (DCC Sort n)
    → Reduces (quot.type α β n) τ
    → Judge (DCC `(β, x)) τ
  | pair   : Judge f (DCC (Π(Id(Sort m), β) α))
    → Judge g (DCC (Π(Id(Sort m), γ) α))
    → Reduces (pair.type α β γ m) τ
    → Judge (DCC ⟨f, g⟩) τ
  -- TODO: Change all occurrences of `(δ, α) to just f_α. Needs to depend on the environment
  | subst₁ : Judge x (DCC (Π(Id(Sort o), Λ(Sort o, Id(Sort o), Π(`(δ, α), γ)) ∘ Snd'(Sort o, δ)) δ))
    → Reduces (Subst₁.type β γ δ o) τ
    → Judge (DCC Subst(x, Fst(β))) τ
  /-
    x : ∀ (env : δ) (y : f_t_snd env), β(env, y)
    Subst(x, Snd(f_β)) env (y, z) = x env z
  -/
  | subst₂ : Judge x (Subst₂.x.type f_t_snd β δ o)
    → Reduces (Subst₂.type f_α f_t_snd β δ o) τ
    → Judge (DCC (Subst(x, Snd(Λ(δ, f_α, f_t_snd ∘ Fstc(f_α)))))) τ
  | appl   : Judge f_α (arrow δ (DCC Sort m) o)
    → Judge f_β (Pi.f_β.type f_α δ o n)
    → Reduces (App.type f_α f_β δ o) τ
    → Judge (DCC App(f_α, f_β)) τ
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge f_α (arrow α (DCC Sort n) m)
    → Judge f_β (Pi.f_β.type f_α α m o)
    → Reduces (Pi.type α m o) τ
    → Judge (DCC Π(f_α, f_β)) τ
  | sort   : Judge (DCC Sort m) (DCC Sort m.succ)
  | top    : Judge (DCC ⊤) Top.type
  | bot    : Judge (DCC ⊥) Bot.type
  | tintro : Judge (DCC ∗) Tintro.type
  | app    : Judge f (DCC (Π(f_α, f_β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge x α
    → Reduces (DCC (f_β x_α x)) τ
    → Judge (DCC (f x)) τ

def with_red (h : Option ((t : Expr) × PULift.{1, 0} (Judge e t))) :
  Option ((τ₁ τ₂ : Expr) × PULift.{1, 0} (Judge e τ₁) × PULift.{1, 0} (Reduces τ₁ τ₂)) :=
  match h with
  | .some ⟨t, h⟩ => .some ⟨t, reduce_all t, h, ⟨reduce_reduces rfl⟩⟩
  | _ => .none

@[dcc_judge] def with_arr (h : Option ((t : Expr) × PULift.{1, 0} (Judge e t))) :
  Option ((τ α β : Expr) × (m : Level) × PULift.{1, 0} (Judge e τ) × PULift.{1, 0} (τ = arrow α β m)) :=
    match h with
    | .some ⟨t, h⟩ => match arrow.matcher t with
      | .some ⟨α, β, m, h_arr⟩ => .some ⟨t, α, β, m, h, h_arr⟩
      | _ => .none
    | _ => .none

@[dcc_judge] def with_fst_fβ_type (h : Option ((t : Expr) × PULift.{1, 0} (Judge e t))) :
  Option ((τ α δ : Expr) × (m n o : Level) × PULift.{1, 0} (Judge e τ) × (PULift.{1, 0} (τ = fst.f_β.type α δ m n o))) :=
  match h with
  | .some ⟨t, h⟩ => match fst.f_β.type.matcher t with
    | .some ⟨α, δ, m, n, o, h₂⟩ => .some ⟨t, α, δ, m, n, o, h, h₂⟩
    | _ => .none
  | _ => none

@[dcc_judge] def with_pair_β_type (h : Option ((t : Expr) × PULift.{1, 0} (Judge e t))) (α : Expr) (m : Level) :
  Option ((τ : Expr) × (n : Level) × PULift.{1, 0} (Judge e τ) × (PULift.{1, 0} (τ = pair.β.type α m n))) :=
  match h with
  | .some ⟨t, h⟩ => match pair.β.type.matcher t α m with
    | .some ⟨n, h₂⟩ => .some ⟨t, n, h, h₂⟩
    | _ => .none
  | _ => .none

@[dcc_judge] def with_curr_β_type (h : Option ((t : Expr) × PULift.{1, 0} (Judge e t))) :
  Option ((τ : Expr) × (α : Expr) × (m n : Level) × PULift.{1, 0} (Judge e τ) × (PULift.{1, 0} (τ = curr.β.type α m n))) :=
  match h with
  | .some ⟨t, h⟩ => match curr.β.type.matcher t with
    | .some ⟨α, m, n, h₂⟩ => .some ⟨t, α, m, n, h, h₂⟩
    | _ => .none
  | _ => none

def infer (e : Expr) : Option ((t : Expr) × PULift.{1, 0} (Judge e t)) :=
  match e with
  | DCC ⊤ => .some ⟨_, ⟨.top⟩⟩
  | DCC ⊥ => .some ⟨_, ⟨.bot⟩⟩
  | DCC ∗ => .some ⟨_, ⟨.tintro⟩⟩
  | DCC Sort _m => .some ⟨_, ⟨.sort⟩⟩
  | DCC (Id(α)) =>
    match infer α with
    | .some ⟨DCC Sort _m, ⟨ht⟩⟩ => .some ⟨_, ⟨.id ht (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC (f ∘ g) =>
    match with_arr (infer g) with
    | .some ⟨_, _α, β, _m, ⟨ht₁⟩, ⟨harr₁⟩⟩ =>
      match (infer f) with
      | .some ⟨(DCC (Π(Id(Sort _n₂), _γ) β₂)), ⟨ht₂⟩⟩ =>
        if heq : β₂ = β then
          .some ⟨_, ⟨.comp' (harr₁ ▸ ht₁) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Fst(f_β) =>
     match with_fst_fβ_type (infer f_β) with
     | .some ⟨_τ₁, _α, δ₂, m, n, o, ⟨ht₂⟩, ⟨harr⟩⟩ =>
       .some ⟨_, ⟨.fst (harr ▸ ht₂) (reduce_reduces rfl)⟩⟩
     | _ => .none
  | DCC Snd(f_β) =>
     match with_fst_fβ_type (infer f_β) with
     | .some ⟨_τ₁, _α, δ₂, m, n, o, ⟨ht₂⟩, ⟨harr⟩⟩ =>
       .some ⟨_, ⟨.snd (harr ▸ ht₂) (reduce_reduces rfl)⟩⟩
     | _ => .none
  | DCC Σ(β) =>
    match with_fst_fβ_type (infer β) with
    | .some ⟨_τ₁, _α, _δ, _m, _n, _o, ⟨ht⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.sigma (harr ▸ ht) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC Snd'(α, β) =>
    match infer α with
    | .some ⟨DCC Sort _m, ⟨ht₁⟩⟩ =>
      match (infer β) with
      | .some ⟨DCC Sort _n, ⟨ht₂⟩⟩ =>
        .some ⟨_, ⟨.snd' ht₁ ht₂ (reduce_reduces rfl)⟩⟩
      | _ => .none
    | _ => .none
  | DCC ⟦β⟧(x, y) =>
    match infer x with
    | .some ⟨α, ⟨ht₁⟩⟩ =>
      match infer y with
      | .some ⟨βxm, ⟨ht₂⟩⟩ =>
        match with_curr_β_type (infer β) with
        | .some ⟨_, α₂, m, n, ⟨ht₃⟩, ⟨harr⟩⟩ =>
          if heq : reduce_all (DCC (β x)) = βxm then
            if heq₂ : α = α₂ then
              .some ⟨_, ⟨.coup ht₁ ht₂ (heq₂ ▸ harr ▸ ht₃) (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
            else .none
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC Λ(α, β, x) =>
    match with_curr_β_type (infer β) with
    | .some ⟨_, α₂, m, n, ⟨htβ⟩, ⟨harrβ⟩⟩ =>
      match infer x with
      | .some ⟨DCC (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : reduce_all (DCC (f_α x_α)) = reduce_all (DCC Coup(β)) then
          if heq₂ : α = α₂ then
            .some ⟨_, ⟨.curr (heq₂ ▸ harrβ ▸ htβ) ht₂ (reduce_reduces heq.symm)
              (reduce_reduces rfl)
              (reduce_reduces rfl)⟩⟩
          else .none
        else .none
      | _ => .none
    | _ => .none
  | DCC `(β, x) =>
    match infer x, infer β with
    | .some ⟨_α, ⟨ht₁⟩⟩, .some ⟨DCC Sort _n, ⟨ht₂⟩⟩ =>
      .some ⟨_, ⟨.quot ht₁ ht₂ (reduce_reduces rfl)⟩⟩
    | _, _ => .none
  | DCC ⟨f, g⟩ =>
    match infer f, infer g with
    | .some ⟨DCC (Π(Id(Sort m), f_β) α), ⟨ht₁⟩⟩, .some ⟨DCC (Π(Id(Sort m₂), f_γ) α₂), ⟨ht₂⟩⟩ =>
      if heq : α = α₂ ∧ m = m₂ then
        have ⟨h₁, h₂⟩ := heq
        .some ⟨_, ⟨.pair
          ht₁
          (h₁.symm ▸ h₂.symm ▸ ht₂)
          (reduce_reduces rfl)⟩⟩
      else .none
    | _, _ => .none
  | DCC Subst(x, Fst(β)) =>
    match infer x with
    | .some ⟨(DCC (Π(Id(Sort o), Λ(Sort o₂, Id(Sort o₃), Π(`(δ, α), γ)) ∘ Snd'(Sort o₄, δ₂)) δ₃)), ⟨ht⟩⟩ =>
      if heq : o₂ = o ∧ o₃ = o ∧ o₄ = o ∧ δ₂ = δ ∧ δ₃ = δ then
        have ⟨ha, hb, hc, hd, he⟩ := heq
        .some ⟨_, ⟨.subst₁ (ha ▸ hb ▸ hc ▸ hd ▸ he ▸ ht) (reduce_reduces rfl)⟩⟩
      else .none
    | _ => .none
  | DCC Subst(x, Snd(Λ(δ, f_α, f_t_snd ∘ Fstc(f_α₂)))) =>
    match infer x with
    | .some ⟨DCC (Π(Id(Sort o), `(_b, Π(_c, β))) _d), ⟨ht⟩⟩ =>
      if heq : f_α₂ = f_α then
        if heq₂ : DCC (Π(Id(Sort o), `(_b, Π(_c, β))) _d) = Subst₂.x.type f_t_snd β δ o then by
          rw [heq]
          exact .some ⟨_, ⟨.subst₂ (heq₂ ▸ ht) (reduce_reduces rfl)⟩⟩
        else .none
      else .none
    | _ => .none
  | DCC App(f_α, f_β) =>
    match with_arr (infer f_α) with
    | .some ⟨_τ₁, δ, DCC Sort m, o, ⟨ht₁⟩, ⟨harr⟩⟩ =>
      match (infer f_β) with
      | .some ⟨(DCC (Π(_a, `(_b, Π(_c, Λ(_d, _e, `(_f, Sort n))))) _j)), ⟨ht₂⟩⟩ =>
        if heqa : (DCC (Π(_a, `(_b, Π(_c, Λ(_d, _e, `(_f, Sort n))))) _j)) = (Pi.f_β.type f_α δ o n) then
          .some ⟨_, ⟨.appl (harr ▸ ht₁) (heqa ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Π(f_α, f_β) =>
    match with_arr (infer f_α) with
    | .some ⟨_τ₁, α, DCC Sort _n, m, ⟨ht₁⟩, ⟨harr⟩⟩ =>
      match infer f_β with
      | .some ⟨DCC (Π(_a, `(_b, Π(_c, Λ(_d, _e, `(_f, Sort o))))) _g), ⟨ht₂⟩⟩ =>
        if heq : (DCC (Π(_a, `(_b, Π(_c, Λ(_d, _e, `(_f, Sort o))))) _g)) = Pi.f_β.type f_α α m o then
          .some ⟨_, ⟨.pi (harr ▸ ht₁) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC (f x) =>
    match infer f, infer x with
    | .some ⟨DCC (Π(f_α, _f_β) x_α), ⟨ht₁⟩⟩, .some ⟨τ₂', ⟨ht₂⟩⟩ =>
      if heq : reduce_all (DCC (f_α x_α)) = τ₂' then
        .some ⟨_, ⟨.app ht₁ (reduce_reduces rfl) (by rw [heq]; exact ht₂) (reduce_reduces rfl)⟩⟩
      else .none
    | _, _ => .none
  | _ => .none

def test_pair_comp : Option Expr := do
  match ← (DCC Id(Sort 1)).infer with
  | ⟨DCC (Π(_f_α, _β) _x), _⟩ =>
    let e := DCC (⟨Id(Sort 1), Id(Sort 1)⟩)
    Sigma.fst <$> e.infer
  | _ => .none

#eval test_pair_comp

def test_id_nested : Option Expr := do
  let ⟨t, _⟩ ← (DCC Id(Sort 1)).infer
  Sigma.fst <$> (DCC (Id(t) Id(Sort 1) (Sort 0))).infer

--#eval (DCC (Π(Id(Sort 3), `(Sort 3, Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), (`(⊤, `(Coup(Id(Sort 2)), Sort 2)) ∗))))) Sort 2)).reduce_η

#eval test_id_nested

--#eval .reduce_η

@[dcc_rel, aesop norm (rule_sets := [DccRel])] instance Judge.instRel : Rel (fun x y => PULift.{1, 0} (Judge x y)) (m := Option) where
  run := infer

end Expr
