import Dcc.Ast
import Dcc.Aff.Red
import Dcc.Types
import Dcc.Eta.Reduce

namespace GenericExpr
#eval Sigma.fst <$> (domain₂? (DCCη Λ(Sort 1, Id(Sort 1), `(Coup(Id(Sort 1)), Sort 2))))
#eval (·.2.1) <$> (domain₂? (DCCη Λ(Sort 1, Id(Sort 1), `(Coup(Id(Sort 1)), Sort 2))))
#eval (reduce RedAff (DCCη (Λ(Sort 1, Id(Sort 1), `(Coup(Id(Sort 1)), Sort 2)) hole(1) hole(2)))).fst

inductive Reduces₂.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Prop
  | mk : Relation.ReflTransGen RedAff A B
    → IsNorm RedAff B
    → B.RedEta₂ C
    → Reduces₂ A C

@[dcc_force_reduce]
def reduce_all₂.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] := (red_eta'₂ (τ_c := τ_c)) ∘ reduce' RedAff

def reduce₂_reduces.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {A B : GenericExpr τ_c} (h : reduce_all₂ A = B) : Reduces₂ A B := ⟨reduce_sound rfl, reduce_norm rfl, by
  simp [reduce_all₂, reduce'] at h
  simp [← h]
  exact reduce_eta_sound rfl⟩

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
theorem Reduces₂.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {τ τ' : GenericExpr τ_c}
  (h : Reduces₂ (τ_c := τ_c) τ τ') : reduce_all₂ τ = τ' := by
  cases h with
  | mk hr hn hr₂ =>
    have ha := reduce_complete hr hn
    have hb := hr₂.complete
    simp [reduce_all₂, reduce', red_eta'₂]
    rw [ha, hb]

#eval Std.format <| pair.β.type (DCC (Sort 30)) 10 20

-- For checking arguments under apps
inductive DefEq.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Prop
  | pi   : Reduces₂ (DCC? (f_α₁ env₁)) f_α'
    → Reduces₂ (DCC? (f_α₂ env₂)) f_α'
    → Reduces₂ (DCC? (f_β₁ env₁)) f_β'
    → Reduces₂ (DCC? (f_β₂ env₂)) f_β'
    → DefEq (DCC? (Π(f_α₁, f_β₁) env₁)) (DCC? (Π(f_α₂, f_β₂) env₂))
  | bang : DefEq τ₁ τ₂ → DefEq (DCC? !(τ₁)) (DCC? !(τ₂))
  | tm : ((¬ ∃ f_α f_β env, τ₁ = (DCC? (Π(f_α, f_β) env)))
    ∨ (¬ ∃ f_α f_β env, τ₂ = (DCC? (Π(f_α, f_β) env))))
    → ((¬ ∃ τ, τ₁ = (DCC? !(τ))) ∨ (¬ ∃ τ, τ₂ = (DCC? !(τ))))
    → Reduces₂ τ₁ τ'
    → Reduces₂ τ₂ τ'
    → DefEq τ₁ τ₂

instance {τ₁ : GenericExpr τ_c} : Decidable (∃ f_α₁ f_β₁ env₁, τ₁ = (DCC? (Π(f_α₁, f_β₁) env₁))
    ∧ ∃ f_α₂ f_β₂ env₂, τ₂ = (DCC (Π(f_α₂, f_β₂) env₂))) :=
  if h₁ : ∃ f_α₁ f_β₁ env₁, τ₁ = (DCC? (Π(f_α₁, f_β₁) env₁)) then
    if h₂ : ∃ f_α₂ f_β₂ env₂, τ₂ = (DCC? (Π(f_α₂, f_β₂) env₂)) then
      .isTrue (by simp_all)
    else .isFalse (fun h => by simp_all)
  else .isFalse (fun h => by simp_all)

instance {τ₁ : GenericExpr τ_c} : Decidable ((∃ α, τ₁ = (DCC? !(α)))
    ∧ ∃ α, τ₂ = (DCC !(α))) :=
  if h₁ : (∃ τ, τ₁ = (DCC? !(τ))) then
    if h₂ : (∃ τ, τ₂ = (DCC? !(τ))) then
      .isTrue (by simp_all)
    else .isFalse (fun h => by simp_all)
  else .isFalse (fun h => by simp_all)

def def_eq?.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] (τ₁ τ₂ : GenericExpr τ_c) : Option (PLift (DefEq τ₁ τ₂)) :=
  if hn₁ : ((¬ ∃ f_α₁ f_β₁ env₁, τ₁ = (DCC? (Π(f_α₁, f_β₁) env₁)))
    ∨ (¬ ∃ f_α₂ f_β₂ env₂, τ₂ = (DCC? (Π(f_α₂, f_β₂) env₂))))
    ∧ ((¬ ∃ τ, τ₁ = (DCC? !(τ))) ∨ (¬ ∃ τ, τ₂ = (DCC? !(τ)))) then
    if heq : τ₁.reduce_all₂ = τ₂.reduce_all₂ then
      .some ⟨.tm (by simp_all) (by simp_all) (reduce₂_reduces rfl) (reduce₂_reduces heq.symm)⟩
    else .none
  else
    match τ₁, τ₂ with
    | (DCC? (Π(f_α₁, f_β₁) env₁)), (DCC? (Π(f_α₂, f_β₂) env₂)) =>
      if heq₁ : (DCC? (f_α₁ env₁)).reduce_all₂ = (DCC? (f_α₂ env₂)).reduce_all₂ then
        if heq₂ : (DCC? (f_β₁ env₁)).reduce_all₂ = (DCC? (f_β₂ env₂)).reduce_all₂ then
          .some ⟨.pi (reduce₂_reduces rfl) (reduce₂_reduces heq₁.symm)
            (reduce₂_reduces rfl)  (reduce₂_reduces heq₂.symm)⟩
        else .none
      else .none
    | (DCC? !(τ₁)), (DCC? !(τ₂)) =>
      match def_eq? τ₁ τ₂ with
      | .some ⟨h⟩ => .some ⟨.bang h⟩
      | _ => .none
    | _, _ => .none

@[dcc_reduce, aesop safe destruct (rule_sets := [DccReduce])]
theorem DefEq.complete.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] {τ₁ τ₂ : GenericExpr τ_c} (h : DefEq (τ_c := τ_c) τ₁ τ₂) : def_eq? τ₁ τ₂ = .some ⟨h⟩ := by
  induction h
  · dsimp [def_eq?]
    dcc_aesop
  case bang h ih =>
    dsimp [def_eq?]
    simp [ih]
  case tm hn₁ hn₂ hr₁ hr₂ =>
    have ha := hr₁.complete
    have hb := hr₂.complete
    unfold def_eq?
    simp only [hn₁, hn₂]
    simp [ha, hb]

inductive Judge₂.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] : GenericExpr τ_c → GenericExpr τ_c → Prop where
  | eq     : Judge₂ x α
    → Judge₂ y α
    → Judge₂ (DCC? x = y) (DCC? Sort 0)
  | refl    : Judge₂ f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Reduces₂ (eql.type f_α δ o) τ
    → Judge₂ (DCC? refl(f_α)) τ
  | eql    : Judge₂ f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Reduces₂ (eql.type f_α δ o) τ
    → Judge₂ (DCC? Eql(f_α)) τ
  | id     : Judge₂ α (DCC? Sort m)
    → Reduces₂ α α'
    → Reduces₂ (id.type α' m) τ
    → Judge₂ (DCC? Id(α)) τ
  | comp   : Judge₂ g (comp.g.type α β m)
    → Judge₂ f (comp.f.type f_β f_γ n)
    → Reduces₂ f_β (DCC? `(α, β))
    → Reduces₂ (DCC? (f_γ Coup(`(α, β)))) γ
    → Reduces₂ α α'
    → Reduces₂ (comp.type α' γ g m) τ
    → Judge₂ (DCC? (f ∘ g)) τ
  | comp₂  : Judge₂ g τ_g
    → Comp₂.g.type α β m τ_g
    → Judge₂ f (comp₂.f.type β f_γ n)
    → Reduces₂ (DCC? (f_γ Coup(β))) γ
    → Reduces₂ (comp₂.type α γ g m) τ
    → Judge₂ (DCC? (f ∘∘ g)) τ
  | comp'  : Judge₂ g (DCC? (Π(Id(Sort m), f_β₀) α))
    → Reduces₂ (DCC? (f_β₀ α)) (DCC? (`(α, β)))
    → Judge₂ f (DCC? (Π(f_β, f_γ) x_β))
    → Reduces₂ (DCC? (f_β x_β)) β
    → Reduces₂ (DCC? (f_γ x_β)) γ
    → Reduces₂ α α'
    → Reduces₂ (comp'.type α' γ g m) τ
    → Judge₂ (DCC? f ∘' g) τ
  | coup   : Judge₂ β (DCC? (Π(Id(Sort m), f_β) α))
    → Reduces₂ (DCC? (f_β α)) (DCC? `(α, Sort n))
    → Reduces₂ (Coup.type m n) τ
    → Judge₂ (DCC? Coup(β)) τ
  | fstc   : Judge₂ β τ_β
    → Arrow α (DCC? Sort n) m τ_β
    → Reduces₂ β β'
    → Reduces₂ (fstc.type α β' m n) τ
    → Judge₂ (DCC? Fstc(β)) τ
  | sndc    : Judge₂ β τ_β
    → Arrow α (DCC? Sort n) m τ_β
    → Reduces₂ β β'
    → Reduces₂ (sndc.type β' m n) τ
    → Judge₂ (DCC? Sndc(β)) τ
  | sigma   : Judge₂ f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Judge₂ f_β τ_f_β
    → Pi.f_β.type f_α δ o n τ_f_β
    → Reduces₂ (Sigma.type δ m n o) τ
    → Judge₂ (DCC? Σ(f_α, f_β)) τ
  | mk     : Judge₂ x α
    → Judge₂ β τ_β
    → Arrow α (DCC? Sort n) m τ_β
    → Reduces₂ (DCC? (β x)) τ₂
    → Judge₂ y τ₂
    → Reduces₂ (DCC? Coup(β)) τ
    → Judge₂ (DCC? ⟦β⟧(x, y)) τ
  /-
    Λ(β, x)
    β receives (α, x)
    β : Coup(Sort m, Id(Sort m)) → Sort n
  -/
  | curr   : Judge₂ α (DCC? Sort m)
    → Judge₂ x (DCC? (Π(f_α, γ) x_α))
    → Reduces₂ (DCC? Coup(β)) τα
    → Reduces₂ (DCC? (f_α x_α)) τα
    → Reduces₂ (DCC? (γ x_α)) γ'
    → Reduces₂ α α'
    → Reduces₂ (curr.type α' β γ' m) τ
    → Judge₂ (DCC? Λ(α, β, x)) τ
  | curr'  : Judge₂ α (DCC? Sort m)
    → Judge₂ x (DCC? (Π(f_α, γ) x_α))
    → Reduces₂ (DCC? !(Coup(β))) τα
    → Reduces₂ (DCC? (f_α x_α)) τα
    → Reduces₂ (DCC? (γ x_α)) γ'
    → Reduces₂ α α'
    → Reduces₂ (curr'.type α' β γ' m) τ
    → Judge₂ (DCC? !Λ(α, β, x)) τ
  | map    : Judge₂ x (DCC? (Π(Id(Sort m), f_β) α))
    → Reduces₂ (DCC? (f_β α)) β
    → Reduces₂ (DCC? (Π(Id(Sort m), `(Sort m, !<β>)) !(α))) τ
    → Judge₂ (DCC? !<x>) τ
  | fmap   : Judge₂ x (DCC? (Π(Id(Sort m), f_β) α))
    → Reduces₂ (DCC? (f_β α)) β
    → Reduces₂ (DCC? (Π(Id(Sort m), `(Sort m, !<β>)) !(α))) τ
    → Judge₂ (DCC? $<x>) τ
  | eval   : Judge₂ x (DCC? (Π(f_α, f_β) env))
    → Reduces₂ (DCC? (f_α env)) α
    → Reduces₂ (DCC? (f_β env)) (DCC? (Π(β, γ)))
    → Judge₂ α (DCC? Sort m)
    → Judge₂ β (DCC? (Π(f_α₂, f_β₂) env₂))
    → Reduces₂ (DCC? (f_α₂ env₂)) α
    → Reduces₂ (DCC? (f_β₂ env₂)) (DCC? `(α, Sort n))
    → Reduces₂ (Eval.type α β γ m n) τ
    → Judge₂ (DCC? Eval(α, β, x)) τ
  | quot   : Judge₂ x α
    → Judge₂ β (DCC? Sort n)
    → Reduces₂ β β'
    → Reduces₂ (quot.type α β' n) τ
    → Judge₂ (DCC? `(β, x)) τ
  | pair   : Judge₂ f (DCC? (Π(Id(Sort m), f_β) x_α))
    → Reduces₂ (DCC? (f_β x_α)) β
    → Judge₂ g (DCC? (Π(f_α₂, f_β₂) α))
    → Reduces₂ γ γ'
    → Reduces₂ (DCC? (f_β₂ α)) (DCC? (Π(β₂, γ₂)))
    → Reduces₂ γ₂ γ'
    → Reduces₂ β₂ β
    → Reduces₂ (DCC? (Id(Sort m) x_α)) α'
    → Reduces₂ (DCC? (f_α₂ α)) α'
    → Reduces₂ (pair.type α' β γ' m) τ
    → Judge₂ (DCC? ⟦γ⟧⟨f, g⟩) τ
  /-
    ef_α : α → Sort m
    f_β : ∀ (x : α) (y : f_α x), Sort n
    Π(f_α, f_β)
  -/
  | pi     : Judge₂ f_α τ_f_α
    → Arrow δ (DCC? Sort m) o τ_f_α
    → Judge₂ f_β τ_f_β
    → Pi.f_β.type f_α δ o n τ_f_β
    → Reduces₂ (Pi.type δ o n) τ
    → Judge₂ (DCC? Π(f_α, f_β)) τ
  | sort   : Judge₂ (DCC? Sort m) (DCC? Sort m.succ)
  | top    : Judge₂ (DCC? ⊤) Top.type
  | bot    : Judge₂ (DCC? ⊥) Bot.type
  | tintro : Judge₂ (DCC? ∗) Tintro.type
  | bang   : Judge₂ τ (DCC? Sort m) → Judge₂ (DCC? !(τ)) (DCC? Sort m)
  | box    : Judge₂ x τ
    → Judge₂ (DCC? &(x)) (DCC? !(τ))
  | unbox  : Judge₂ α (DCC? Sort m)
    → Reduces₂ (DCC? (!(α) : Sort m) → α) τ
    → Judge₂ (DCC? *(α)) τ
  | app    : Judge₂ f (DCC? (Π(f_α, f_β) x_α))
    → Reduces₂ (DCC? (f_α x_α)) α₁
    → Judge₂ x α₂
    → DefEq α₁ α₂
    → Reduces₂ x_α x_α'
    → Reduces₂ (DCC? (f_β x_α' x)) τ
    → Judge₂ (DCC? (f x)) τ

def infer₂.{u} {τ_c : Type u} [hDecEq : DecidableEq τ_c] [BEq τ_c] (e : GenericExpr τ_c) : Option ((t : GenericExpr τ_c) × PULift.{1, 0} (Judge₂ e t)) :=
  match e with
  | DCC? !<f> => match f.infer₂ with
    | .some ⟨(DCC? (Π(Id(Sort m), f_β) α)), ⟨ht⟩⟩ =>
      .some ⟨_, ⟨.map ht (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
    | _ => .none
  | DCC? $<f> => match f.infer₂ with
    | .some ⟨(DCC? (Π(Id(Sort m), f_β) α)), ⟨ht⟩⟩ =>
      .some ⟨_, ⟨.fmap ht (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
    | _ => .none
  | DCC? *(α) => match α.infer₂ with
    | .some ⟨DCC? Sort m, ⟨ht⟩⟩ => .some ⟨_, ⟨.unbox ht (reduce₂_reduces rfl)⟩⟩
    | _ => .none
  | DCC? !(τ) => match τ.infer₂ with
    | .some ⟨DCC? Sort m, ⟨ht⟩⟩ => .some ⟨_, ⟨.bang ht⟩⟩
    | _ => .none
  | DCC? &(x) => match x.infer₂ with
    | .some ⟨τ, ⟨ht⟩⟩ => .some ⟨_, ⟨.box ht⟩⟩
    | _ => .none
  | DCC? ⊤ => .some ⟨_, ⟨.top⟩⟩
  | DCC? ⊥ => .some ⟨_, ⟨.bot⟩⟩
  | DCC? ∗ => .some ⟨_, ⟨.tintro⟩⟩
  | DCC? Sort _m => .some ⟨_, ⟨.sort⟩⟩
  | DCC? (Id(α)) =>
    match infer₂ α with
    | .some ⟨DCC? Sort _m, ⟨ht⟩⟩ => .some ⟨_, ⟨.id ht (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
    | _ => .none
  | DCC? (f ∘ g) =>
    match infer₂ g with
    | .some ⟨DCC? (Π(Id(Sort m), `(_m, Σ(__a, Λ(_a, _b, `(___a, β))) ∘' _a₂)) !(α)), ⟨ht₁⟩⟩ =>
      if heq : (DCC? (Π(Id(Sort m), `(_m, Σ(__a, Λ(_a, _b, `(___a, β))) ∘' _a₂)) !(α))) = comp.g.type α β m then
        match infer₂ f with
        | .some ⟨(DCC? (Π(Id(Sort n), f_γ) Coup(f_β))), ⟨ht₂⟩⟩ =>
          if heq₂ : (DCC? (Π(Id(Sort n), f_γ) Coup(f_β))) = comp.f.type f_β f_γ n then
            if heq₃ : f_β.reduce_all₂ = (DCC? `(α, β)) then
              .some ⟨_, ⟨.comp (heq ▸ ht₁) ht₂ (reduce₂_reduces heq₃) (reduce₂_reduces rfl) (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
            else .none
          else .none
        | _ => .none
      else .none
    | _ => .none
  | DCC? (f ∘∘ g) =>
    match infer₂ g with
    | .some ⟨τ_g, ⟨ht₁⟩⟩ =>
      match τ_g.read_comp₂_g_type with
      | .some ⟨α, β, m, hg⟩ =>
        match infer₂ f with
        | .some ⟨(DCC? (Π(Id(Sort n), f_γ) _a)), ⟨ht₂⟩⟩ =>
          if heq₂ : (DCC? (Π(Id(Sort n), f_γ) _a)) = comp₂.f.type β f_γ n then
            .some ⟨_, ⟨.comp₂ ht₁ hg (heq₂ ▸ ht₂) (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
          else .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC? (f ∘' g) =>
    match infer₂ g with
    | .some ⟨(DCC? (Π(Id(Sort m), f_β₀) α)), ⟨ht⟩⟩ =>
      match (DCC? (f_β₀ α)).reduce_all₂ with
      | DCC? `(α₀', β) =>
        if heq₀ : (DCC? (f_β₀ α)).reduce_all₂ = (DCC? (`(α, β))) then
          match (infer₂ f) with
          | .some ⟨(DCC? (Π(f_β, _γ) x_β)), ⟨ht₂⟩⟩ =>
            if heq : (DCC? (f_β x_β)).reduce_all₂ = β then
              .some ⟨_, ⟨.comp' ht (reduce₂_reduces heq₀) ht₂ (reduce₂_reduces heq) (reduce₂_reduces rfl) (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
            else .none
          | _ => .none
        else .none
      | _ => .none
    | _ => .none
  | DCC? x = y =>
    match infer₂ x with
    | .some ⟨t_x, ⟨ht₁⟩⟩ =>
      match infer₂ y with
      | .some ⟨t_y, ⟨ht₂⟩⟩ =>
        if heq : t_x = t_y then
          .some ⟨_, ⟨.eq ht₁ (heq ▸ ht₂)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC? Eql(f_α) =>
    match infer₂ f_α with
    | .some ⟨τ, ⟨ht₁⟩⟩ =>
      match τ.read_arrow with
      | .some ⟨δ, DCC? Sort m, o, h⟩ =>
        .some ⟨_, ⟨.eql ht₁ h (reduce₂_reduces rfl)⟩⟩
      | _ => .none
    | _ => .none
  | DCC? refl(f_α) =>
    match infer₂ f_α with
    | .some ⟨τ, ⟨ht₁⟩⟩ =>
      match τ.read_arrow with
      | .some ⟨δ, DCC? Sort m, o, h⟩ =>
        .some ⟨_, ⟨.refl ht₁ h (reduce₂_reduces rfl)⟩⟩
      | _ => .none
    | _ => .none
  | DCC? Σ(f_α, f_β) =>
    match f_α.infer₂ with
    | .some ⟨τ_f_α, ⟨h₁⟩⟩ =>
      match τ_f_α.read_arrow with
      | .some ⟨δ, DCC? Sort m, o, harr⟩ =>
        match infer₂ f_β with
        | .some ⟨τ_f_β, ⟨h₂⟩⟩ =>
          match τ_f_β.view_pi_f_β f_α δ o with
          | .some ⟨n, h₃⟩ =>
            .some ⟨_, ⟨.sigma h₁ harr h₂ h₃ (reduce₂_reduces rfl)⟩⟩
          | _ => .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC? ⟦β⟧(x, y) =>
    match infer₂ x with
    | .some ⟨α, ⟨ht₁⟩⟩ =>
      match infer₂ y with
      | .some ⟨βxm, ⟨ht₂⟩⟩ =>
        match β.infer₂ with
        | .some ⟨τ_β, ⟨h₃⟩⟩ =>
          match τ_β.read_arrow₁ α with
          | .some ⟨DCC? Sort n, m, harr⟩ =>
            if heq : reduce_all₂ (DCC? (β x)) = βxm then
              .some ⟨_, ⟨.mk ht₁ h₃ harr
                (reduce₂_reduces (B := βxm) heq) (heq ▸ ht₂) (reduce₂_reduces rfl)⟩⟩
            else .none
          | _ => .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC? Coup(β) =>
    match infer₂ β with
    | .some ⟨(DCC? (Π(Id(Sort m), f_β) α)), ⟨ht⟩⟩ =>
      match (DCC? (f_β α)).reduce_all₂ with
      | DCC? `(α₂, Sort n) =>
        if heq : (DCC? (f_β α)).reduce_all₂ = DCC? `(α, Sort n) then
          .some ⟨_, ⟨.coup ht (reduce₂_reduces heq) (reduce₂_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC? Fstc(β) =>
    match (infer₂ β) with
    | .some ⟨τ_β, ⟨ht₁⟩⟩ =>
      match τ_β.read_arrow with
      | .some ⟨α, DCC? Sort n, m, harr⟩ =>
        .some ⟨_, ⟨.fstc ht₁ harr (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
      | _ => .none
    | _ => .none
  | DCC? Sndc(β) =>
    match (infer₂ β) with
    | .some ⟨τ_β, ⟨ht₁⟩⟩ =>
      match τ_β.read_arrow with
      | .some ⟨α, DCC? Sort n, m, harr⟩ =>
        .some ⟨_, ⟨.sndc ht₁ harr (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
      | _ => .none
    | _ => .none
  | DCC? Λ(α, β, x) =>
    match α.infer₂ with
    | .some ⟨DCC? Sort m, ⟨ht⟩⟩ =>
      match infer₂ x with
      | .some ⟨DCC? (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : reduce_all₂ (DCC? (f_α x_α)) = reduce_all₂ (DCC? Coup(β)) then
          .some ⟨_, ⟨.curr
            ht
            ht₂
            (reduce₂_reduces heq.symm)
            (reduce₂_reduces rfl)
            (reduce₂_reduces rfl)
            (reduce₂_reduces rfl)
            (reduce₂_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC? !Λ(α, β, x) =>
    match α.infer₂ with
    | .some ⟨DCC? Sort m, ⟨ht⟩⟩ =>
      match infer₂ x with
      | .some ⟨DCC? (Π(f_α, _γ) x_α), ⟨ht₂⟩⟩ =>
        if heq : reduce_all₂ (DCC? (f_α x_α)) = reduce_all₂ (DCC? !(Coup(β))) then
          .some ⟨_, ⟨.curr'
            ht
            ht₂
            (reduce₂_reduces heq.symm)
            (reduce₂_reduces rfl)
            (reduce₂_reduces rfl)
            (reduce₂_reduces rfl)
            (reduce₂_reduces rfl)⟩⟩
        else .none
      | _ => .none
    | _ => .none
  | DCC? Eval(α, β, x) =>
    match infer₂ x with
    | .some ⟨DCC? (Π(f_α, f_β) env), ⟨ht₁⟩⟩ =>
      if heq : (DCC? (f_α env)).reduce_all₂ = α then
        match heq₂ : (DCC? (f_β env)).reduce_all₂ with
        | DCC? Π(β₂, γ) =>
          if heq₃ : β₂ = β then
            match infer₂ α with
            | .some ⟨DCC? Sort m, ⟨ht₂⟩⟩ =>
              match infer₂ β with
              | .some ⟨DCC? (Π(f_α₂, f_β₂) env₂), ⟨ht₃⟩⟩ =>
                if heq₄ : (DCC? (f_α₂ env₂)).reduce_all₂ = α then
                  match heq₅ : (DCC? (f_β₂ env₂)).reduce_all₂ with
                  | DCC? `(α₃, Sort n) =>
                    if heq₆ : α₃ = α then
                      .some ⟨_, ⟨.eval ht₁ (reduce₂_reduces heq) (heq₃ ▸ (reduce₂_reduces heq₂))
                        ht₂ ht₃ (reduce₂_reduces heq₄) (reduce₂_reduces (heq₆ ▸ heq₅)) (reduce₂_reduces rfl)⟩⟩
                    else .none
                  | _ => .none
                else .none
              | _ => .none
            | _ => .none
          else .none
        | _ => .none
      else .none
    | _ => .none
  | DCC? `(β, x) =>
    match infer₂ x, infer₂ β with
    | .some ⟨_α, ⟨ht₁⟩⟩, .some ⟨DCC? Sort _n, ⟨ht₂⟩⟩ =>
      .some ⟨_, ⟨.quot ht₁ ht₂ (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
    | _, _ => .none
  | DCC? ⟦γ⟧⟨f, g⟩ =>
    match infer₂ f, infer₂ g with
    | .some ⟨DCC? (Π(Id(Sort m), f_β) x_α), ⟨ht₁⟩⟩,
      .some ⟨DCC? (Π(f_α₂, f_β₂) α), ⟨ht₂⟩⟩ =>
      let β := (DCC? (f_β x_α)).reduce_all₂
      match heqm : (DCC? (f_β₂ α)).reduce_all₂ with
      | DCC? (Π(β₂, γ₂)) =>
        if heq : (DCC? (Id(Sort m) x_α)).reduce_all₂ = (DCC? (f_α₂ α)).reduce_all₂ ∧ β₂.reduce_all₂ = β then
          if heq₂ : γ₂.reduce_all₂ = γ.reduce_all₂ then
            have ⟨h₁, h₃⟩ := heq
            .some ⟨_, ⟨.pair
              ht₁
              (reduce₂_reduces rfl)
              ht₂
              (reduce₂_reduces rfl)
              (reduce₂_reduces heqm)
              (reduce₂_reduces heq₂)
              (reduce₂_reduces h₃)
              (reduce₂_reduces rfl)
              (reduce₂_reduces h₁.symm)
              (reduce₂_reduces rfl)⟩⟩
          else .none
        else .none
      | _ => .none
    | _, _ => .none
  | DCC? Π(f_α, f_β) =>
    match f_α.infer₂ with
    | .some ⟨τ_f_α, ⟨ht₁⟩⟩ =>
      match τ_f_α.read_arrow with
      | .some ⟨δ, DCC? Sort m, o, harr⟩ =>
        match infer₂ f_β with
        | .some ⟨τ_f_β, ⟨ht₂⟩⟩ =>
          match τ_f_β.view_pi_f_β f_α δ o with
          | .some ⟨n, h₂⟩ =>
            .some ⟨_, ⟨.pi ht₁ harr ht₂ h₂ (reduce₂_reduces rfl)⟩⟩
          | _ => .none
        | _ => .none
      | _ => .none
    | _ => .none
  | DCC? (f x) =>
    match infer₂ f, infer₂ x with
    | .some ⟨DCC? (Π(f_α, _f_β) x_α), ⟨ht₁⟩⟩, .some ⟨τ₂', ⟨ht₂⟩⟩ =>
      match def_eq? (reduce_all₂ (DCC? (f_α x_α))) τ₂' with
      | .some ⟨h⟩ =>
        .some ⟨_, ⟨.app ht₁ (reduce₂_reduces rfl) ht₂ h (reduce₂_reduces rfl) (reduce₂_reduces rfl)⟩⟩
      | _ => .none
    | _, _ => .none
  | .const _ => .none

abbrev infer₂'.{u} {τ_c : Type u} [DecidableEq τ_c] [BEq τ_c] (e : GenericExpr τ_c) : Option (GenericExpr τ_c) := Sigma.fst <$> e.infer₂

end GenericExpr

abbrev Expr.infer₂' (e : Expr) : Option Expr := Sigma.fst <$> e.infer₂
abbrev Expr.infer₂ (e : Expr) : Option ((t : GenericExpr Unit) × PULift.{1, 0} (GenericExpr.Judge₂ e t)) := GenericExpr.infer₂ e

@[dcc_force_reduce]
def Expr.reduce_all₂ : Expr → Expr := (GenericExpr.red_eta'₂ (τ_c := Unit)) ∘ GenericExpr.reduce' GenericExpr.RedAff
