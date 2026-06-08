import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Types
import Dcc.Eta.Reduce

namespace EtaExpr
#eval Sigma.fst <$> (EtaExpr.domain₂? (DCCη Λ(Sort 1, Id(Sort 1), `(Coup(Id(Sort 1)), Sort 2))))
#eval (·.2.1) <$> (EtaExpr.domain₂? (DCCη Λ(Sort 1, Id(Sort 1), `(Coup(Id(Sort 1)), Sort 2))))
#eval (Expr.reduce EtaExpr.RedAffEta (DCCη (Λ(Sort 1, Id(Sort 1), `(Coup(Id(Sort 1)), Sort 2)) hole(1) hole(2)))).fst
end EtaExpr

namespace Expr

abbrev RedAffReflTrans := Relation.ReflTransGen RedAff

inductive Reduces : Expr → Expr → Prop
  | mk : RedAffReflTrans A B
    → IsNorm RedAff B
    → B.RedEta C
    → Reduces A C

@[dcc_force_reduce]
def reduce_all := Expr.red_eta' ∘ reduce' RedAff

def reduce_reduces (h : reduce_all A = B) : Reduces A B := ⟨reduce_sound rfl, reduce_norm rfl, by
  simp [reduce_all, reduce'] at h
  simp [← h]
  exact reduce_eta_sound rfl⟩

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
  | refl    : Judge f_α τ_f_α
    → Arrow δ (DCC Sort m) o τ_f_α
    → Reduces (eql.type f_α δ o) τ
    → Judge (DCC refl(f_α)) τ
  | eql    : Judge f_α τ_f_α
    → Arrow δ (DCC Sort m) o τ_f_α
    → Reduces (eql.type f_α δ o) τ
    → Judge (DCC Eql(f_α)) τ
  | id     : Judge α (DCC Sort m)
    → Reduces α α'
    → Reduces (id.type α' m) τ
    → Judge (DCC Id(α)) τ
  | comp   : Judge g (comp.g.type α β m)
    → Judge f (comp.f.type f_β f_γ n)
    → Reduces f_β (DCC `(α, β))
    → Reduces (DCC (f_γ Coup(`(α, β)))) γ
    → Reduces α α'
    → Reduces (comp.type α' γ g m) τ
    → Judge (DCC (f ∘ g)) τ
  | comp₂  : Judge g (comp₂.g.type α β m)
    → Judge f (comp₂.f.type β f_γ n)
    → Reduces (DCC (f_γ Coup(β))) γ
    → Reduces α α'
    → Reduces (comp.type α' γ g m) τ
    → Judge (DCC (f ∘∘ g)) τ
  | comp'  : Judge g (DCC (Π(Id(Sort m), f_β₀) α))
    → Reduces (DCC (f_β₀ α)) (DCC (`(α, β)))
    → Judge f (DCC (Π(f_β, f_γ) x_β))
    → Reduces (DCC (f_β x_β)) β
    → Reduces (DCC (f_γ x_β)) γ
    → Reduces α α'
    → Reduces (comp'.type α' γ g m) τ
    → Judge (DCC f ∘' g) τ
  | coup   : Judge β (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) (DCC `(α, Sort n))
    → Reduces (Coup.type m n) τ
    → Judge (DCC Coup(β)) τ
  | fstc   : Judge β (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) (DCC `(α, Sort n))
    → Reduces β β'
    → Reduces (fstc.type α β' m n) τ
    → Judge (DCC Fstc(β)) τ
  | sndc    : Judge β (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) (DCC `(α, Sort n))
    → Reduces β β'
    → Reduces (sndc.type β' m n) τ
    → Judge (DCC Sndc(β)) τ
  | sigma   : Judge f_α τ_f_α
    → Arrow δ (DCC Sort m) o τ_f_α
    → Judge f_β τ_f_β
    → Pi.f_β.type f_α δ o n τ_f_β
    → Reduces (Sigma.type δ m n o) τ
    → Judge (DCC Σ(f_α, f_β)) τ
  | mk     : Judge x α
    → Judge β τ_β
    → Arrow α (DCC Sort n) m τ_β
    → Reduces (DCC (β x)) τ₂
    → Judge y τ₂
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
    → Reduces α α'
    → Reduces (curr.type α' β γ' m) τ
    → Judge (DCC Λ(α, β, x)) τ
  | curr'  : Judge α (DCC Sort m)
    → Judge x (DCC (Π(f_α, γ) x_α))
    → Reduces (DCC !(Coup(β))) τα
    → Reduces (DCC (f_α x_α)) τα
    → Reduces (DCC (γ x_α)) γ'
    → Reduces α α'
    → Reduces (curr'.type α' β γ' m) τ
    → Judge (DCC !Λ(α, β, x)) τ
  | map    : Judge x (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) β
    → Reduces (DCC (Π(Id(Sort m), `(Sort m, !<β>)) !(α))) τ
    → Judge (DCC !<x>) τ
  | fmap   : Judge x (DCC (Π(Id(Sort m), f_β) α))
    → Reduces (DCC (f_β α)) β
    → Reduces (DCC (Π(Id(Sort m), `(Sort m, !<β>)) !(α))) τ
    → Judge (DCC $<x>) τ
  | eval   : Judge x (DCC (Π(f_α, f_β) env))
    → Reduces (DCC (f_α env)) α
    → Reduces (DCC (f_β env)) (DCC (Π(β, γ)))
    → Judge α (DCC Sort m)
    → Judge β (DCC (Π(f_α₂, f_β₂) env₂))
    → Reduces (DCC (f_α₂ env₂)) α
    → Reduces (DCC (f_β₂ env₂)) (DCC `(α, Sort n))
    → Reduces (Eval.type α β γ m n) τ
    → Judge (DCC Eval(α, β, x)) τ
  | quot   : Judge x α
    → Judge β (DCC Sort n)
    → Reduces β β'
    → Reduces (quot.type α β' n) τ
    → Judge (DCC `(β, x)) τ
  | pair   : Judge f (DCC (Π(Id(Sort m), f_β) x_α))
    → Reduces (DCC (f_β x_α)) β
    → Judge g (DCC (Π(f_α₂, f_β₂) α))
    → Reduces γ γ'
    → Reduces (DCC (f_β₂ α)) (DCC (Π(β₂, γ₂)))
    → Reduces γ₂ γ'
    → Reduces β₂ β
    → Reduces (DCC (Id(Sort m) x_α)) α'
    → Reduces (DCC (f_α₂ α)) α'
    → Reduces (pair.type α' β γ' m) τ
    → Judge (DCC ⟦γ⟧⟨f, g⟩) τ
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge f_α τ_f_α
    → Arrow δ (DCC Sort m) o τ_f_α
    → Judge f_β τ_f_β
    → Pi.f_β.type f_α δ o n τ_f_β
    → Reduces (Pi.type δ o n) τ
    → Judge (DCC Π(f_α, f_β)) τ
  | sort   : Judge (DCC Sort m) (DCC Sort m.succ)
  | top    : Judge (DCC ⊤) Top.type
  | bot    : Judge (DCC ⊥) Bot.type
  | tintro : Judge (DCC ∗) Tintro.type
  | bang   : Judge τ (DCC Sort m) → Judge (DCC !(τ)) (DCC Sort m)
  | box    : Judge x τ  → Judge (DCC &(x)) (DCC !(τ))
  | unbox  : Judge α (DCC Sort m)
    → Reduces (DCC (!(α) : Sort m) → α) τ
    → Judge (DCC *(α)) τ
  | app    : Judge f (DCC (Π(f_α, f_β) x_α))
    → Reduces (DCC (f_α x_α)) α
    → Judge x α
    → Reduces x_α x_α'
    → Reduces (DCC (f_β x_α' x)) τ
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
  | DCC !<f> => match f.infer with
    | .some ⟨(DCC (Π(Id(Sort m), f_β) α)), ⟨ht⟩⟩ =>
      .some ⟨_, ⟨.map ht (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC $<f> => match f.infer with
    | .some ⟨(DCC (Π(Id(Sort m), f_β) α)), ⟨ht⟩⟩ =>
      .some ⟨_, ⟨.fmap ht (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC *(α) => match α.infer with
    | .some ⟨DCC Sort m, ⟨ht⟩⟩ => .some ⟨_, ⟨.unbox ht (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC !(τ) => match τ.infer with
    | .some ⟨DCC Sort m, ⟨ht⟩⟩ => .some ⟨_, ⟨.bang ht⟩⟩
    | _ => .none
  | DCC &(x) => match x.infer with
    | .some ⟨τ, ⟨ht⟩⟩ => .some ⟨_, ⟨.box ht⟩⟩
    | _ => .none
  | DCC ⊤ => .some ⟨_, ⟨.top⟩⟩
  | DCC ⊥ => .some ⟨_, ⟨.bot⟩⟩
  | DCC ∗ => .some ⟨_, ⟨.tintro⟩⟩
  | DCC Sort _m => .some ⟨_, ⟨.sort⟩⟩
  | DCC (Id(α)) =>
    match infer α with
    | .some ⟨DCC Sort _m, ⟨ht⟩⟩ => .some ⟨_, ⟨.id ht (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
    | _ => .none
  | DCC (f ∘ g) =>
    match infer g with
    | .some ⟨DCC (Π(Id(Sort m), `(_m, Σ(__a, Λ(_a, _b, `(___a, β))) ∘' _a₂)) !(α)), ⟨ht₁⟩⟩ =>
      if heq : (DCC (Π(Id(Sort m), `(_m, Σ(__a, Λ(_a, _b, `(___a, β))) ∘' _a₂)) !(α))) = comp.g.type α β m then
        match infer f with
        | .some ⟨(DCC (Π(Id(Sort n), f_γ) Coup(f_β))), ⟨ht₂⟩⟩ =>
          if heq₂ : (DCC (Π(Id(Sort n), f_γ) Coup(f_β))) = comp.f.type f_β f_γ n then
            if heq₃ : f_β.reduce_all = (DCC `(α, β)) then
              .some ⟨_, ⟨.comp (heq ▸ ht₁) ht₂ (reduce_reduces heq₃) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
            else .none
          else .none
        | _ => .none
      else .none
    | _ => .none
  | DCC (f ∘∘ g) =>
    match infer g with
    | .some ⟨DCC (Π(Id(Sort m), `(_m, Σ(__a, Λ(_a, _b, β ∘' Fstc(___a))) ∘' _a₂)) !(α)), ⟨ht₁⟩⟩ =>
      if heq : (DCC (Π(Id(Sort m), `(_m, Σ(__a, Λ(_a, _b, β ∘' Fstc(___a))) ∘' _a₂)) !(α))) = comp₂.g.type α β m then
        match infer f with
        | .some ⟨(DCC (Π(Id(Sort n), f_γ) _a)), ⟨ht₂⟩⟩ =>
          if heq₂ : (DCC (Π(Id(Sort n), f_γ) _a)) = comp₂.f.type β f_γ n then
            .some ⟨_, ⟨.comp₂ (heq ▸ ht₁) (heq₂ ▸ ht₂) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
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
              .some ⟨_, ⟨.comp' ht (reduce_reduces heq₀) ht₂ (reduce_reduces heq) (reduce_reduces rfl) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
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
    match infer f_α with
    | .some ⟨τ, ⟨ht₁⟩⟩ =>
      match τ.read_arrow with
      | .some ⟨δ, DCC Sort m, o, h⟩ =>
        .some ⟨_, ⟨.eql ht₁ h (reduce_reduces rfl)⟩⟩
      | _ => .none
    | _ => .none
  | DCC refl(f_α) =>
    match infer f_α with
    | .some ⟨τ, ⟨ht₁⟩⟩ =>
      match τ.read_arrow with
      | .some ⟨δ, DCC Sort m, o, h⟩ =>
        .some ⟨_, ⟨.refl ht₁ h (reduce_reduces rfl)⟩⟩
      | _ => .none
    | _ => .none
  | DCC Σ(f_α, f_β) =>
    match f_α.infer with
    | .some ⟨τ_f_α, ⟨h₁⟩⟩ =>
      match τ_f_α.read_arrow with
      | .some ⟨δ, DCC Sort m, o, harr⟩ =>
        match infer f_β with
        | .some ⟨τ_f_β, ⟨h₂⟩⟩ =>
          match τ_f_β.view_pi_f_β f_α δ o with
          | .some ⟨n, h₃⟩ =>
            .some ⟨_, ⟨.sigma h₁ harr h₂ h₃ (reduce_reduces rfl)⟩⟩
          | _ => .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC ⟦β⟧(x, y) =>
    match infer x with
    | .some ⟨α, ⟨ht₁⟩⟩ =>
      match infer y with
      | .some ⟨βxm, ⟨ht₂⟩⟩ =>
        match β.infer with
        | .some ⟨τ_β, ⟨h₃⟩⟩ =>
          match τ_β.read_arrow₁ α with
          | .some ⟨DCC Sort n, m, harr⟩ =>
            if heq : reduce_all (DCC (β x)) = βxm then
              .some ⟨_, ⟨.mk ht₁ h₃ harr
                (reduce_reduces (B := βxm) heq) (heq ▸ ht₂) (reduce_reduces rfl)⟩⟩
            else .none
          | _ => .none
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
    match (infer β) with
    | .some ⟨DCC (Π(Id(Sort m), f_β) α), ⟨ht₁⟩⟩ =>
      match heq : (DCC (f_β α)).reduce_all with
      | DCC `(α₂, Sort n) =>
        if heq₂ : α₂ = α then
          .some ⟨_, ⟨.fstc ht₁ (reduce_reduces (heq₂ ▸ heq)) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Sndc(β) =>
    match (infer β) with
    | .some ⟨DCC (Π(Id(Sort m), f_β) α), ⟨ht₁⟩⟩ =>
      match heq : (DCC (f_β α)).reduce_all with
      | DCC `(α₂, Sort n) =>
        if heq₂ : α₂ = α then
          .some ⟨_, ⟨.sndc ht₁ (reduce_reduces (heq₂ ▸ heq)) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
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
            (reduce_reduces rfl)
            (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC !Λ(α, β, x) =>
    match α.infer with
    | .some ⟨DCC Sort m, ⟨ht⟩⟩ =>
      match infer x with
      | .some ⟨DCC (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : reduce_all (DCC (f_α x_α)) = reduce_all (DCC !(Coup(β))) then
          .some ⟨_, ⟨.curr'
            ht
            ht₂
            (reduce_reduces heq.symm)
            (reduce_reduces rfl)
            (reduce_reduces rfl)
            (reduce_reduces rfl)
            (reduce_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC Eval(α, β, x) =>
    match infer x with
    | .some ⟨DCC (Π(f_α, f_β) env), ⟨ht₁⟩⟩ =>
      if heq : (DCC (f_α env)).reduce_all = α then
        match heq₂ : (DCC (f_β env)).reduce_all with
        | DCC Π(β₂, γ) =>
          if heq₃ : β₂ = β then
            match infer α with
            | .some ⟨DCC Sort m, ⟨ht₂⟩⟩ =>
              match infer β with
              | .some ⟨DCC (Π(f_α₂, f_β₂) env₂), ⟨ht₃⟩⟩ =>
                if heq₄ : (DCC (f_α₂ env₂)).reduce_all = α then
                  match heq₅ : (DCC (f_β₂ env₂)).reduce_all with
                  | DCC `(α₃, Sort n) =>
                    if heq₆ : α₃ = α then
                      .some ⟨_, ⟨.eval ht₁ (reduce_reduces heq) (heq₃ ▸ (reduce_reduces heq₂))
                        ht₂ ht₃ (reduce_reduces heq₄) (reduce_reduces (heq₆ ▸ heq₅)) (reduce_reduces rfl)⟩⟩
                    else .none
                  | _ => .none
                else .none
              | _ => .none
            | _ => .none
          else .none
        | _ => .none
      else .none
    | _ => .none
  | DCC `(β, x) =>
    match infer x, infer β with
    | .some ⟨_α, ⟨ht₁⟩⟩, .some ⟨DCC Sort _n, ⟨ht₂⟩⟩ =>
      .some ⟨_, ⟨.quot ht₁ ht₂ (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
    | _, _ => .none
  | DCC ⟦γ⟧⟨f, g⟩ =>
    match infer f, infer g with
    | .some ⟨DCC (Π(Id(Sort m), f_β) x_α), ⟨ht₁⟩⟩,
      .some ⟨DCC (Π(f_α₂, f_β₂) α), ⟨ht₂⟩⟩ =>
      let β := (DCC (f_β x_α)).reduce_all
      match heqm : (DCC (f_β₂ α)).reduce_all with
      | DCC (Π(β₂, γ₂)) =>
        if heq : (DCC (Id(Sort m) x_α)).reduce_all = (DCC (f_α₂ α)).reduce_all ∧ β₂.reduce_all = β then
          if heq₂ : γ₂.reduce_all = γ.reduce_all then
            have ⟨h₁, h₃⟩ := heq
            .some ⟨_, ⟨.pair
              ht₁
              (reduce_reduces rfl)
              ht₂
              (reduce_reduces rfl)
              (reduce_reduces heqm)
              (reduce_reduces heq₂)
              (reduce_reduces h₃)
              (reduce_reduces rfl)
              (reduce_reduces h₁.symm)
              (reduce_reduces rfl)⟩⟩
          else .none
        else .none
      | _ => .none
    | _, _ => .none
  | DCC Π(f_α, f_β) =>
    match f_α.infer with
    | .some ⟨τ_f_α, ⟨ht₁⟩⟩ =>
      match τ_f_α.read_arrow with
      | .some ⟨δ, DCC Sort m, o, harr⟩ =>
        match infer f_β with
        | .some ⟨τ_f_β, ⟨ht₂⟩⟩ =>
          match τ_f_β.view_pi_f_β f_α δ o with
          | .some ⟨n, h₂⟩ =>
            .some ⟨_, ⟨.pi ht₁ harr ht₂ h₂ (reduce_reduces rfl)⟩⟩
          | _ => .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC (f x) =>
    match infer f, infer x with
    | .some ⟨DCC (Π(f_α, f_β) x_α), ⟨ht₁⟩⟩, .some ⟨τ₂', ⟨ht₂⟩⟩ =>
      if heq : reduce_all (DCC (f_α x_α)) = τ₂' then
        .some ⟨_, ⟨.app ht₁ (reduce_reduces rfl) (by rw [heq]; exact ht₂) (reduce_reduces rfl) (reduce_reduces rfl)⟩⟩
      else .none
    | _, _ => .none

abbrev infer' (e : Expr) : Option Expr := Sigma.fst <$> e.infer

end Expr
