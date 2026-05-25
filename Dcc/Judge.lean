import Dcc.Attrs
import Dcc.Ast
import Dcc.Types
import Dcc.Aff.Red
import Dcc.Eta.Red
import Dcc.Relation
import Mathlib.Logic.Relation

namespace Expr

inductive Reduced : Expr → Expr → Prop
  | mk : Relation.TransGen RedAff A B
    → IsNorm RedAff B
    → Relation.ReflTransGen RedEta B C
    → IsNorm RedEta C
    → Reduced A C

@[grind ., grind →]
theorem Reduced.decreasing (h : Reduced A B) : B.size < A.size :=
  match h with
  | ⟨hr₁, hn₁, hr₂, hn₂⟩ => by
    have hb := decreasing? RedEta hr₂
    rename_i B'
    induction hr₁  using Relation.TransGen.head_induction_on generalizing B with
    | single hr =>
      have ha := RedAff.instRedRel.decreasing hr
      grind
    | head hr hrt h =>
      rename_i ih
      have h := RedAff.instRedRel.decreasing hr
      have h := Reduced.mk hrt hn₁ hr₂ (by assumption)
      have h := ih h hr₂ hn₂ (by assumption)
      grind

def reduce_all? (e : Expr) : Option ((e' : Expr) × PLift (Reduced e e')) :=
  if h_some : (reduce? RedAff e).isSome then
    .some ⟨reduce' RedEta ((reduce? RedAff e).get h_some).fst, ⟨by
      have hn := reduce?_norm RedAff (A := e) (B := ((reduce? RedAff e).get h_some).fst)
        (by simp_all) (by simp_all)
      exact ⟨((reduce? RedAff e).get h_some).snd.down, hn, reduce_sound rfl, reduce_norm rfl⟩⟩⟩
  else
    .none
    /-sorry
  match heq : reduce? RedAff e with
  | .some ⟨e', ⟨h⟩⟩ =>
    have hn := reduce?_norm RedAff (A := e) (B := e') (by simp_all) (by simp_all)
    .some ⟨reduce' RedEta e', ⟨h, hn, reduce_sound rfl, reduce_norm rfl⟩⟩
  | _ => .none-/

theorem Reduced.unique : Reduced A B → Reduced A C → B = C := fun ⟨a, b, c, d⟩ ⟨g, h, i, j⟩ => by
  have ha := norm_unique a.to_reflTransGen b g.to_reflTransGen h
  exact norm_unique c d (ha ▸ i) j

theorem Reduced.unique' (h₁ : Reduced A B) (h₂ : Reduced A C) : h₁ ≍ h₂ := by
  have h := h₁.unique h₂
  cases h
  congr

def Reduced.norm_eta (h : Reduced A B) : IsNorm RedEta B :=
  match h with
  | ⟨_, _, _, h⟩ => h

theorem reduce_all?_reduces (h_some : (reduce_all? A).isSome) (h : ((reduce_all? A).get h_some).fst = B) : Reduced A B :=
  h ▸ ((reduce_all? A).get h_some).snd.down

inductive Reduces : Expr → Expr → Prop
  | mk : Relation.ReflTransGen RedAff A B
    → IsNorm RedAff B
    → Relation.ReflTransGen RedEta B C
    → IsNorm RedEta C
    → Reduces A C

notation A "≡" B => ∃ C, Reduces A C ∧ Reduces B C

@[dcc_force_reduce]
def reduce_all := reduce' RedEta ∘ reduce' RedAff

@[dcc_reduce, aesop safe forward (rule_sets := [DccReduce])]
theorem Reduces.unique : Reduces A B → Reduces A C → B = C := fun ⟨a, b, c, d⟩ ⟨g, h, i, j⟩ => by
  have ha := norm_unique a b g h
  exact norm_unique c d (ha ▸ i) j

@[aesop safe destruct (rule_sets := [DccReduce]), aesop safe apply (rule_sets := [DccReduce])]
theorem Reduces.unique' (h₁ : Reduces A B) (h₂ : Reduces A C) : h₁ ≍ h₂ := by
  have h := h₁.unique h₂
  cases h
  congr

@[dcc_reduce]
def Reduces.norm_eta (h : Reduces A B) : IsNorm RedEta B :=
  match h with
  | ⟨_, _, _, h⟩ => h

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
theorem Reduces.complete : Reduces A B → reduce_all A = B :=
  fun ⟨ha, hb, hc, hd⟩ => by
    unfold reduce_all
    unfold reduce'
    cases reduce_complete_fst ha hb; cases reduce_complete_fst hc hd; rfl

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
theorem Reduced.complete : Reduced A B → ∃ h, reduce_all? A = .some ⟨B, h⟩ :=
  fun ⟨ha, hb, hc, hd⟩ => by
    rename_i h₀ _
    unfold reduce_all?
    unfold reduce?
    split
    case isTrue h =>
      simp_all
      constructor
      have h := Reduces.complete ⟨ha.to_reflTransGen, hb, hc, hd⟩
      · change reduce' RedEta (reduce' RedAff A) = B
        exact h
      · congr
        simp_all
        · have h := Reduces.complete ⟨ha.to_reflTransGen, hb, hc, hd⟩
          change reduce' RedEta (reduce' RedAff A) = B
          exact h
        · grind
    case isFalse heq =>
      simp_all
      have h := reduce_norm_fst heq.symm
      cases ha using Relation.TransGen.head_induction_on with
      | single hr => exact h ⟨_, heq.symm ▸ hr⟩
      | head h =>
        rename_i h_norm _ _ _
        exact h_norm ⟨_, heq.symm ▸ h⟩

--@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])] theorem

def reduce_reduces (h : reduce_all A = B) : Reduces A B := ⟨
  reduce_sound rfl,
  reduce_norm rfl,
  h ▸ (reduce_sound rfl),
  h ▸ (reduce_norm rfl)⟩

def reduce_reduces' : Reduces A (reduce_all A) := reduce_reduces rfl

@[dcc_judge, inline] abbrev fst.f_β.type.matcher (t : Expr) : Option ((α δ : Expr) × (m n o : Level) × (PULift.{1, 0} (t = fst.f_β.type α δ m n o))) :=
  match arrow.matcher t with
  | .some ⟨δ, arr', o, ⟨h_arr⟩⟩ =>
    match arrow.matcher arr' with
    | .some ⟨α, DCC Sort n, m, ⟨h_arr₂⟩⟩ =>
      .some ⟨α, δ, m, n, o, ⟨by rw [h_arr, h_arr₂]⟩⟩
    | _ => .none
  | _ => .none

#eval Std.format <| pair.β.type (DCC (Sort 30)) 10 20

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
  ((f_α x_α : Expr) × (m n : Level) × (PULift.{1, 0} (t = curr.β.type f_α x_α m n))) :=
  match t with
  | DCC (Π(f_α, Λ(Sort m, _a, `(_b, Sort n))) x_α) =>
    if h : (DCC (Π(f_α, Λ(Sort m, _a, `(_b, Sort n))) x_α)) = curr.β.type f_α x_α m n then
      .some ⟨f_α, x_α, m, n, ⟨h⟩⟩
    else .none
  | _ => .none

inductive Judge : Expr → Expr → Prop where
  | eq     : Judge x α
    → Judge y α
    → Judge (DCC x = y) (DCC Sort 0)
  | refl   : Judge f_α (DCC (δ : Sort o) → Sort m)
    → Reduces (DCC (Π(Id(Sort o), `(Sort o, Π(f_α, Eql(f_α) ∘ Id(Sort o)))) δ)) τ
    → Judge (DCC refl(f_α)) τ
  | eql    : Judge f_α (DCC (δ : Sort o) → Sort m)
    → Reduces (DCC (Π(Id(Sort o), `(Sort o, Π(f_α, Λ(δ, f_α, Π(Id(Sort m), `(Coup(Id(Sort m)), Sort 0)))))) δ)) τ
    → Judge (DCC Eql(f_α)) τ
  | id     : Judge α (DCC Sort m)
    → Reduces (id.type α m) τ
    → Judge (DCC Id(α)) τ
  | comp   : Judge g (comp.g.type α f_β m)
    → Judge f (comp.f.type f_β f_γ n)
    → Reduces (DCC (f_γ Coup(f_β))) γ
    → Reduces (comp.type α γ g m) τ
    → Judge (DCC (f ∘ g)) τ
  | comp'  : Judge g (DCC (Π(Id(Sort m), f_β₀) α))
    → Reduces (DCC (f_β₀ α)) (DCC (`(α, β)))
    → Judge f (DCC (Π(f_β, f_γ) x_β))
    → Reduces (DCC (f_β x_β)) β
    → Reduces (DCC (f_γ x_β)) γ
    → Reduces (comp'.type α γ g m) τ
    → Judge (DCC f ∘' g) τ
  | coup   : Judge β (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) (DCC `(α, Sort n))
    → Reduces (Coup.type m n) τ
    → Judge (DCC Coup(β)) τ
  | fstc   : Judge β (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) (DCC `(α, Sort n))
    → Reduces (fstc.type α β m n) τ
    → Judge (DCC Fstc(β)) τ
  | sndc    : Judge β (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) (DCC `(α, Sort n))
    → Reduces (sndc.type β m n) τ
    → Judge (DCC Sndc(β)) τ
  | sigma   : Judge f_α (DCC ((δ : Sort o) → Sort m))
    → Judge f_β (Pi.f_β.type f_α δ o n)
    → Reduces (Sigma.type δ m n o) τ
    → Judge (DCC Σ(f_α, f_β)) τ
  | mk     : Judge x α
    → Judge y τ₂
    → Judge β (curr.β.type f_α x_α m n)
    → Reduces (DCC (f_α x_α)) α
    → Reduces (DCC (β x)) τ₂
    → Reduces (DCC Coup(β)) τ
    → Judge (DCC ⟦β⟧(x, y)) τ
  /-
    Λ(β, x)
    β receives (α, x)
    β : Coup(Sort m, Id(Sort m)) → Sort n
  -/
  | curr   : Judge α (DCC Sort m)
    → Judge x (DCC (Π(f_α, γ) x_α))
    → Reduces (DCC Coup(β)) τα
    → Reduces (DCC (f_α x_α)) τα
    → Reduces (DCC (γ x_α)) γ'
    → Reduces (curr.type α β γ' m) τ
    → Judge (DCC Λ(α, β, x)) τ
  | quot   : Judge x α
    → Judge β (DCC Sort n)
    → Reduces (quot.type α β n) τ
    → Judge (DCC `(β, x)) τ
  | pair   : Judge f (DCC (Π(f_α, f_β) x_α))
    → Reduces (DCC (f_β x_α)) β
    → Judge g (DCC (Π(Id(Sort m), f_β₂) α))
    → Reduces (DCC (f_β₂ α)) (DCC (Π(β₂, γ)))
    → Reduces β₂ β
    → Reduces (DCC (f_α x_α)) α
    → Reduces (pair.type α β γ m) τ
    → Judge (DCC ⟨f, g⟩) τ
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge f_α (DCC ((α : Sort m) → Sort n))
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
    → Reduced (DCC (f_β x_α x)) τ
    → Judge (DCC (f x)) τ

def with_red (h : Option ((t : Expr) × PULift.{1, 0} (Judge e t))) :
  Option ((τ₁ τ₂ : Expr) × PULift.{1, 0} (Judge e τ₁) × PULift.{1, 0} (Reduces τ₁ τ₂)) :=
  match h with
  | .some ⟨t, h⟩ => .some ⟨t, reduce_all t, h, ⟨reduce_reduces rfl⟩⟩
  | _ => .none

@[dcc_judge] def with_arr (h : Option ((t : Expr) × PULift.{1, 0} (Judge e t))) :
  Option ((τ α β : Expr) × (m : Level) × PULift.{1, 0} (Judge e τ) × PULift.{1, 0} (τ = DCC ((α : Sort m) → β))) :=
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
  Option ((τ : Expr) × (f_α x_α : Expr) × (m n : Level) × PULift.{1, 0} (Judge e τ) × (PULift.{1, 0} (τ = curr.β.type f_α x_α m n))) :=
  match h with
  | .some ⟨t, h⟩ => match curr.β.type.matcher t with
    | .some ⟨f_α, x_α, m, n, h₂⟩ => .some ⟨t, f_α, x_α, m, n, h, h₂⟩
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
    match infer g with
    | .some ⟨DCC (Π(Id(Sort m), Σ(__a, Λ(_a, _b, f_β ∘' _c))) α), ⟨ht₁⟩⟩ =>
      if heq : (DCC (Π(Id(Sort m), Σ(__a, Λ(_a, _b, f_β ∘' _c))) α)) = comp.g.type α f_β m then
        match infer f with
        | .some ⟨(DCC (Π(Id(Sort n), f_γ) _a)), ⟨ht₂⟩⟩ =>
          if heq₂ : (DCC (Π(Id(Sort n), f_γ) _a)) = comp.f.type f_β f_γ n then
            .some ⟨_, ⟨.comp (heq ▸ ht₁) (heq₂ ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
          else .none
        | _ => .none
      else .none
    | _ => .none
  | DCC (f ∘' g) =>
    match infer g with
    | .some ⟨(DCC (Π(Id(Sort m), f_β₀) α)), ⟨ht⟩⟩ =>
      match (DCC (f_β₀ α)).reduce_all with
      | DCC `(α₀', β) =>
        if heq₀ : (DCC (f_β₀ α)).reduce_all = (DCC (`(α, β))) then
          match (infer f) with
          | .some ⟨(DCC (Π(f_β, _γ) x_β)), ⟨ht₂⟩⟩ =>
            if heq : (DCC (f_β x_β)).reduce_all = β then
              .some ⟨_, ⟨.comp' ht (reduce_reduces heq₀) ht₂ (reduce_reduces heq) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
            else .none
          | _ => .none
        else .none
      | _ => .none
    | _ => .none
  | DCC x = y =>
    match infer x with
    | .some ⟨t_x, ⟨ht₁⟩⟩ =>
      match infer y with
      | .some ⟨t_y, ⟨ht₂⟩⟩ =>
        if heq : t_x = t_y then
          .some ⟨_, ⟨.eq ht₁ (heq ▸ ht₂)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Eql(f_α) =>
    match with_arr (infer f_α) with
    | .some ⟨_τ₁, δ, DCC Sort m, o, ⟨ht₁⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.eql (harr ▸ ht₁) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC refl(f_α) =>
    match with_arr (infer f_α) with
    | .some ⟨_τ₁, δ, DCC Sort m, o, ⟨ht₁⟩, ⟨harr⟩⟩ =>
      .some ⟨_, ⟨.refl (harr ▸ ht₁) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC Σ(f_α, f_β) =>
    match with_arr (infer f_α) with
    | .some ⟨_τ₁, δ, DCC Sort m, o, ⟨ht₁⟩, ⟨harr⟩⟩ =>
      match infer f_β with
      | .some ⟨DCC (Π(_a, `(_b, Π(_c, Λ(_d, _e, `(_f, Sort n))))) _g), ⟨ht₂⟩⟩ =>
        if heq : (DCC (Π(_a, `(_b, Π(_c, Λ(_d, _e, `(_f, Sort n))))) _g)) = Pi.f_β.type f_α δ o n then
          .some ⟨_, ⟨.sigma (harr ▸ ht₁) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC ⟦β⟧(x, y) =>
    match infer x with
    | .some ⟨α, ⟨ht₁⟩⟩ =>
      match infer y with
      | .some ⟨βxm, ⟨ht₂⟩⟩ =>
        match with_curr_β_type (infer β) with
        | .some ⟨_, f_α₂, x_α₂, m, n, ⟨ht₃⟩, ⟨harr⟩⟩ =>
          if heq : reduce_all (DCC (β x)) = βxm then
            if heq₂ : α = (DCC (f_α₂ x_α₂)).reduce_all then
              .some ⟨_, ⟨.mk ht₁ ht₂ (harr ▸ ht₃) (reduce_reduces heq₂.symm) (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
            else .none
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC Coup(β) =>
    match infer β with
    | .some ⟨(DCC (Π(Id(Sort m), f_β) α)), ⟨ht⟩⟩ =>
      match (DCC (f_β α)).reduce_all with
      | DCC `(α₂, Sort n) =>
        if heq : (DCC (f_β α)).reduce_all = DCC `(α, Sort n) then
          .some ⟨_, ⟨.coup ht (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Fstc(β) =>
    match infer β with
    | .some ⟨(DCC (Π(Id(Sort m), f_β) α)), ⟨ht⟩⟩ =>
      match (DCC (f_β α)).reduce_all with
      | DCC `(α₂, Sort n) =>
        if heq : (DCC (f_β α)).reduce_all = DCC `(α, Sort n) then
          .some ⟨_, ⟨.fstc ht (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Sndc(β) =>
    match infer β with
    | .some ⟨(DCC (Π(Id(Sort m), f_β) α)), ⟨ht⟩⟩ =>
      match (DCC (f_β α)).reduce_all with
      | DCC `(α₂, Sort n) =>
        if heq : (DCC (f_β α)).reduce_all = DCC `(α, Sort n) then
          .some ⟨_, ⟨.sndc ht (reduce_reduces heq) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Λ(α, β, x) =>
    match α.infer with
    | .some ⟨DCC Sort m, ⟨ht⟩⟩ =>
      match infer x with
      | .some ⟨DCC (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : reduce_all (DCC (f_α x_α)) = reduce_all (DCC Coup(β)) then
          .some ⟨_, ⟨.curr
            ht
            ht₂
            (reduce_reduces heq.symm)
            (reduce_reduces rfl)
            (reduce_reduces rfl)
            (reduce_reduces rfl)⟩⟩
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
    | .some ⟨DCC (Π(f_α, f_β) x_α), ⟨ht₁⟩⟩,
      .some ⟨DCC (Π(Id(Sort m), f_β₂) α), ⟨ht₂⟩⟩ =>
      let α₂ := (DCC (f_α x_α)).reduce_all
      let β := (DCC (f_β x_α)).reduce_all
      match heqm : (DCC (f_β₂ α)).reduce_all with
      | DCC (Π(β₂, γ)) =>
        if heq : α₂ = α ∧ β₂.reduce_all = β then
          have ⟨h₁, h₃⟩ := heq
          .some ⟨_, ⟨.pair
            ht₁
            (reduce_reduces rfl)
            ht₂
            (reduce_reduces heqm)
            (reduce_reduces h₃)
            (reduce_reduces h₁)
            (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _, _ => .none
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
    | .some ⟨DCC (Π(f_α, f_β) x_α), ⟨ht₁⟩⟩, .some ⟨τ₂', ⟨ht₂⟩⟩ =>
      if heq : reduce_all (DCC (f_α x_α)) = τ₂' then
        match reduce_all? (DCC (f_β x_α x)) with
        | .some ⟨τ', ⟨h_red⟩⟩ =>
          .some ⟨_, ⟨.app ht₁ (reduce_reduces rfl) (by rw [heq]; exact ht₂) h_red⟩⟩
        | _ => .none
      else .none
    | _, _ => .none

def test_pair_comp : Option Expr := do
  let e := DCC (⟨Id(Sort 1),
      Λ(Sort 1, `(Sort 1, Sort 1), Fstc(`(Sort 1, Sort 1)))⟩)
  Sigma.fst <$> e.infer

#eval test_pair_comp

def test_id_nested : Option Expr := do
  let ⟨t, _⟩ ← (DCC Id(Sort 1)).infer
  Sigma.fst <$> (DCC (Id(t) Id(Sort 1) (Sort 0))).infer

--#eval (DCC (Π(Id(Sort 3), `(Sort 3, Π(Id(Sort 2), Λ(Sort 2, Id(Sort 2), (`(⊤, `(Coup(Id(Sort 2)), Sort 2)) ∗))))) Sort 2)).reduce_η

#eval test_id_nested

--#eval .reduce_η

@[dcc_rel, aesop norm (rule_sets := [DccRel])]
instance Judge.instRel : Rel (fun x y => PULift.{1, 0} (Judge x y)) (m := Option) where
  run := infer

end Expr
