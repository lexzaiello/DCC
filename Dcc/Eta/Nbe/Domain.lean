import Dcc.Eta.Ast
import Dcc.Eta.Reflect
import Dcc.Eta.Rel
import Dcc.Aff.Red

variable {τ_c : Type u}
variable [DecidableEq τ_c]

/-
Note: there will be no apps in the expression
-/

namespace NormExpr

open GenericExpr

inductive Domain : @NormExpr τ_c RedAff → @NormExpr τ_c RedAff → Type u
  | eql₁     : Domain ⟨f_α, hn.point' 0⟩ ⟨δ, hn_δ⟩
    → Domain ⟨(DCC? Eql(f_α)), hn⟩ ⟨(DCC? !(δ)), mk_inner_norm⟩
  | eql₂     : Domain ⟨f_α, hn.congrFun.point' 0⟩ ⟨δ, hn_δ⟩
    → (hrn : RedAffNorm (DCC? (f_α env)) ⟨τ, hn_τ⟩)
    → Domain ⟨(DCC? (Eql(f_α) &(env))), hn⟩ ⟨(DCC? !(τ)), mk_inner_norm⟩
  | refl₁     : Domain ⟨f_α, hn.point' 0⟩ ⟨δ, hn_δ⟩
    → Domain ⟨(DCC? refl(f_α)), hn⟩ ⟨(DCC? !(δ)), mk_inner_norm⟩
  | refl₂     : Domain ⟨f_α, hn.congrFun.point' 0⟩ ⟨δ, hn_δ⟩
    → (hrn : RedAffNorm (DCC? (f_α env)) ⟨τ, hn_τ⟩)
    → Domain ⟨(DCC? (refl(f_α) &(env))), hn⟩ ⟨(DCC? !(τ)), mk_inner_norm⟩
  | unmap    : Domain ⟨f, hn_map.point' 0⟩ ⟨α, hn_α⟩
    → Domain ⟨(DCC? *<f>), hn_map⟩ ⟨(DCC? !(α)), mk_inner_norm⟩
  | id       : Domain ⟨(DCC? Id(α)), hn⟩ ⟨α, hn.point' 0⟩
  | fstc     : Domain ⟨(DCC? Fst(β)), hn⟩ ⟨(DCC? Coup(β)), fun ⟨_, .coup₀ h⟩ => hn.point' (h_arr := by grind) 0 ⟨_, h⟩⟩
  | sndc     : Domain ⟨(DCC? Snd(β)), hn⟩ ⟨(DCC? Coup(β)), fun ⟨_, .coup₀ h⟩ => hn.point' (h_arr := by grind) 0 ⟨_, h⟩⟩
  | curr₁    : Domain ⟨x, hn.point' 2⟩ ⟨(DCC? Coup(β)), mk_inner_norm (by grind) (fun ⟨_, h⟩ => hn.point' 1 (h_arr := by grind) ⟨_, h⟩)⟩
    → Domain ⟨(DCC? Λ(α, β, x)), hn⟩ ⟨α, hn.point' 0⟩
  | curr₂    : {y : GenericExpr τ_c}
    → (hrn  : RedAffNorm (DCC? (β y)) τ)
    → {hn   : IsNorm RedAff (DCC? (Λ(α, β, x) y))}
    → Domain ⟨x, hn.congrFun.point' 2⟩
      ⟨(DCC? Coup(β)), mk_inner_norm (by grind) (fun ⟨_, h⟩ => hn.congrFun.point' 1 (h_arr := by grind) ⟨_, h⟩)⟩
    → Domain ⟨(DCC? (Λ(α, β, x) y)), hn⟩ τ
  | curr₁'   : Domain ⟨x, hn.point' 2⟩ ⟨(DCC? !(Coup(β))), mk_inner_norm (by grind) (fun ⟨_, .coup₀ h⟩ => hn.point' 1 (h_arr := by grind) ⟨_, h⟩)⟩
    → Domain ⟨(DCC? !Λ(α, β, x)), hn⟩ ⟨DCC? !(α), fun ⟨_, .bang₀ h⟩ => hn.point' 0 (h_arr := by grind) ⟨_, h⟩⟩
  | curr₂'   : (hrn : RedAffNorm (DCC? (β y)) τ)
    → {hn : IsNorm RedAff (DCC? (!Λ(α, β, x) &(y)))}
    → Domain ⟨x, hn.congrFun.point' 2⟩ ⟨(DCC? !(Coup(β))), mk_inner_norm (by grind) (fun ⟨_, .coup₀ h⟩ => hn.congrFun.point' 1 (h_arr := by grind) ⟨_, h⟩)⟩
    → Domain ⟨(DCC? (!Λ(α, β, x) &(y))), hn⟩ τ
  | map      : Domain ⟨f, hn_map.map⟩ ⟨α, hn_α⟩
    → Domain ⟨(DCC? !<f>), hn_map⟩ ⟨(DCC? !(α)), mk_inner_norm⟩
  | fmap     : Domain ⟨f, hn_f⟩ ⟨α, hn_α⟩
    → Domain ⟨(DCC? $<f>), hn⟩ ⟨(DCC? !(α)), mk_inner_norm⟩
  | pair     : {hn : IsNorm RedAff (DCC? ⟦β⟧⟨M, N⟩)}
    → Domain ⟨M, hn.point' 1⟩ α
    → Domain ⟨N, hn.point' 2⟩ α
    → Domain ⟨(DCC? ⟦β⟧⟨M, N⟩), hn⟩ α
  /-
  TODO: Not sure how to fit Eval in here yet
  | eval     : Val.Domain Val(λ env 2 => f) α → Val.Domain Val(
  | eval     : Apply x y f'
    → Apply f' z e'
    → Apply Val(λ env 1 => Eval(_α, _β, x)) Val(neutral(⟦__β⟧(y, z))) e'-/
  | eval     : Domain ⟨x, hn.point' 2⟩ ⟨α, hn.point' 0⟩
    → Domain ⟨(DCC? Eval(α, β, x)), hn⟩ ⟨DCC? Coup(β), fun ⟨_, .coup₀ h⟩ => hn.point' 1 (h_arr := by grind) ⟨_, h⟩⟩
  | quot     : Domain ⟨(DCC? `(β, x)), hn⟩ ⟨β, hn.point' 0⟩
  -- f ∘ g x
  -- again, need to handle second round
  -- can use β-reducer for this.
  | comp'    : {hn : IsNorm RedAff (DCC? (f ∘' g))}
    → Domain ⟨g, hn.point' 1⟩ α
    → Domain ⟨(DCC? f ∘' g), hn⟩ α
  | comp     : {hn : IsNorm RedAff (DCC? (f ∘ g))}
    → Domain ⟨g, hn.point' 1⟩ α
    → Domain ⟨(DCC? f ∘ g), hn⟩ α
  | comp₂    : {hn : IsNorm RedAff (DCC? (f ∘∘ g))}
    → Domain ⟨g, hn.point' 1⟩ α
    → Domain ⟨(DCC? f ∘∘ g), hn⟩ α
  | pi       : Domain ⟨f_α, hn.point' 0⟩ δ
    → Domain ⟨f_β, hn.point' 1⟩ δ
    → Domain ⟨(DCC? Π(f_α, f_β)), hn⟩ δ
deriving DecidableEq

/-inductive Domain₂ : @NormExpr τ_c RedAff → @NormExpr τ_c RedAff → @NormExpr τ_c RedAff → Type u
  | id      : (RedAffNorm (DCC? (f_α x_α)) ⟨α, hn_α⟩)
    → RedAffNorm (DCC? (Π(f_α, f_β) x_α)) ⟨τ, hn_τ⟩
    → Domain₂ ⟨(DCC? Id((Π(f_α, f_β) x_α))), fun ⟨_, h⟩ => nomatch h⟩
      ⟨τ, hn_τ⟩
      ⟨(DCC? `(τ, α)), fun ⟨_, h⟩ => match h with | .quot₀ hr => hn_α ⟨_, hr⟩⟩
  | comp'   : {hn : IsNorm RedAff (DCC? (f ∘' g))}
    → Domain ⟨g, fun ⟨_, h⟩ => hn ⟨_, .comp'r h⟩⟩ α
    → Domain₂ ⟨f, fun ⟨_, h⟩ => hn ⟨_, .comp'l h⟩⟩ β ⟨γ, hn_γ⟩
    → Domain₂ ⟨(DCC? (f ∘' g)), hn⟩ α ⟨(DCC? γ ∘' g), fun ⟨_, h⟩ =>
      match h with
      | .comp'l h => hn_γ ⟨_, h⟩
      | .comp'r h => hn ⟨_, .comp'r h⟩⟩
  | eql      : (hrn₁ : RedAffNorm f_α ⟨f_α', hn_f_α'⟩) → Domain ⟨f_α', hn_f_α'⟩ ⟨δ, hn_δ⟩
    → Domain₂ ⟨(DCC? Eql(f_α)), fun ⟨_, h⟩ => nomatch h⟩
      ⟨(DCC? !(δ)), fun ⟨_, h⟩ => match h with | .bang h => hn_δ ⟨_, h⟩⟩
      ⟨(DCC? !<f_α'>), fun ⟨_, h⟩ =>
        match h with
        | .map₀ h =>
          hn_f_α' ⟨_, h⟩⟩
  | refl      : (hrn₁ : RedAffNorm f_α ⟨f_α', hn_f_α'⟩) → Domain ⟨f_α', hn_f_α'⟩ ⟨δ, hn_δ⟩
    → Domain₂ ⟨(DCC? refl(f_α)), fun ⟨_, h⟩ => nomatch h⟩
      ⟨(DCC? !(δ)), fun ⟨_, h⟩ => match h with | .bang h => hn_δ ⟨_, h⟩⟩
      ⟨(DCC? !<f_α'>), fun ⟨_, h⟩ => match h with
        | .map₀ h => hn_f_α' ⟨_, h⟩⟩
  | curr     : (hrn₁ : RedAffNorm α α')
    → (hrn₂ : RedAffNorm β ⟨β', hn_β⟩)
    → Domain ⟨x, hn.curr₀⟩ ⟨(DCC? Coup(β')), fun ⟨_, h⟩ => match h with | .coup h => hn_β ⟨_, h⟩⟩
    → Domain₂ ⟨(DCC? Λ(α, β, x)), hn⟩ α' ⟨β', hn_β⟩
  | curr'    : (hrn₁ : RedAffNorm α ⟨α', hn_α'⟩)
    → (hrn₂ : RedAffNorm β ⟨β', hn_β'⟩)
    → Domain ⟨x, hn.curr'₀⟩ ⟨(DCC? !(Coup(β'))), fun ⟨_, h⟩ => match h with | .bang (.coup h) => hn_β' ⟨_, h⟩⟩
    → Domain₂ ⟨(DCC? !Λ(α, β, x)), hn⟩
      ⟨DCC? !(α'), fun ⟨_, h⟩ => match h with | .bang h => hn_α' ⟨_, h⟩⟩ ⟨DCC? !<β'>, fun ⟨_, .map₀ h⟩ => hn_β' ⟨_, h⟩⟩
deriving DecidableEq-/

/-def Domain₂.to_domain (h : Domain₂ f α β) : Domain f α :=
  match h with
  | .id _hr₁ hr => .id hr
  | .comp' h_dom₁ _ => .comp' h_dom₁
  | .eql hr₁ h_dom => .eql₁ hr₁ h_dom
  | .refl hr₁ h_dom => .refl₁ hr₁ h_dom
  | .curr hr₁ hr₂ h_dom => .curr₁ hr₁
  | .curr' hr₁ hr₂ _ => .curr₁' hr₁-/

def domain? (e : @NormExpr τ_c RedAff) : Option ((τ : @NormExpr τ_c RedAff) × (Domain e τ)) :=
  match e with
  | ⟨e, hn⟩ =>
    match e with
    | (DCC? Eval(α, β, x)) =>
      match (mk x (hn.point' 2)).domain? with
      | .some ⟨⟨α', hn_α'⟩, h⟩ =>
        if heqa : α' = α then
          .some ⟨_, .eval (heqa ▸ h)⟩
        else .none
      | _ => .none
    | (DCC? Eql(f_α)) =>
      match (mk f_α (hn.point' 0)).domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .eql₁ h⟩
      | _ => .none
    | (DCC? (Eql(f_α) &(_env))) =>
      match (mk f_α (hn.congrFun.point' 0)).domain? with
      | .some ⟨_, h⟩ =>
        .some ⟨_, .eql₂ h (aff_sound rfl)⟩
      | _ => .none
    | (DCC? refl(f_α)) =>
      match (mk f_α (hn.point' 0)).domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .refl₁ h⟩
      | _ => .none
    | (DCC? (refl(f_α) &(_env))) =>
      match (mk f_α (hn.congrFun.point' 0)).domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .refl₂ h (aff_sound rfl)⟩
      | _ => .none
    | (DCC? *<f>) =>
      match (mk f hn.unmap).domain? with
      | .some ⟨_, h⟩ =>
        .some ⟨_, .unmap h⟩
      | _ => .none
    | (DCC? Id(_α)) => .some ⟨_, .id⟩
    | (DCC? Fst(_β)) => .some ⟨_, .fstc⟩
    | (DCC? Snd(_β)) => .some ⟨_, .sndc⟩
    | (DCC? Λ(_α, β, x)) =>
      match (mk x (hn.point' 2)).domain? with
      | .some ⟨⟨α', hn_α'⟩, h⟩ =>
        if heq : α' = DCC? Coup(β) then
          .some ⟨_, .curr₁ (heq ▸ h)⟩
        else .none
      | .none => .none
    | (DCC? (Λ(_α, β, x) y)) =>
      match (mk x (hn.congrFun.point' 2)).domain? with
      | .some ⟨⟨α', hn_α'⟩, h⟩ =>
        if heq : α' = DCC? Coup(β) then
          .some ⟨_, .curr₂ (y := y) (aff_sound rfl) (heq ▸ h)⟩
        else .none
      | .none => .none
    | (DCC? !Λ(_α, β, x)) =>
      match (mk x (hn.point' 2)).domain? with
      | .some ⟨⟨α', hn_α'⟩, h⟩ =>
        if heq : α' = DCC? !(Coup(β)) then
          .some ⟨_, .curr₁' (heq ▸ h)⟩
        else .none
      | .none => .none
    | (DCC? (!Λ(_α, β, x) &(y))) =>
      match (mk x (hn.congrFun.point' 2)).domain? with
      | .some ⟨⟨α', hn_α'⟩, h⟩ =>
        if heq : α' = DCC? !(Coup(β)) then
          .some ⟨_, .curr₂' (y := y) (aff_sound rfl) (heq ▸ h)⟩
        else .none
      | .none => .none
    | (DCC? !<f>) =>
      match (mk f hn.map).domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .map h⟩
      | _ => .none
    | (DCC? $<f>) =>
      match (mk f (hn.point' 0)).domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .fmap h⟩
      | _ => .none
    | (DCC? ⟦_β⟧⟨M, N⟩) =>
      match (mk M (hn.point' 1)).domain?, (mk N (hn.point' 2)).domain? with
      | .some ⟨α, h₁⟩, .some ⟨α', h₂⟩ =>
        if heq : α' = α then
          .some ⟨α, .pair h₁ (heq ▸ h₂)⟩
        else .none
      | _, _ => .none
    | (DCC? `(_β, _x)) => .some ⟨_, .quot⟩
    | (DCC? _f ∘' g) =>
      match (mk g (hn.point' 1)).domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp' h⟩
      | _ => .none
    | (DCC? _f ∘ g) =>
      match (mk g (hn.point' 1)).domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp h⟩
      | _ => .none
    | (DCC? _f ∘∘ g) =>
      match (mk g (hn.point' 1)).domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp₂ h⟩
      | _ => .none
    | (DCC? Π(f_α, f_β)) =>
      match (mk f_α (hn.point' 0)).domain?, (mk f_β (hn.point' 1)).domain? with
      | .some ⟨δ, h₁⟩, .some ⟨δ', h₂⟩ =>
        if heq : δ' = δ then
          .some ⟨_, .pi h₁ (heq ▸ h₂)⟩
        else .none
      | _, _ => .none
    | _ => .none

/-def domain₂? (e : @NormExpr τ_c RedAff) : Option ((α β : @NormExpr τ_c RedAff) × (Domain₂ e α β)) :=
  match e with
  | ⟨e, hn⟩ =>
    match e with
    | (DCC? Id((Π(f_α, f_β) x_α))) =>
      .some ⟨_, _, .id (aff_sound rfl) (aff_sound rfl)⟩
    | (DCC? (f ∘' g)) =>
      match (mk g hn.comp'r).domain?, (mk f hn.comp'l).domain₂? with
      | .some ⟨_, h₁⟩, .some ⟨_, _, h₂⟩ =>
        .some ⟨_, _, .comp' h₁ h₂⟩
      | _, _ => .none
    | (DCC? Eql(f_α)) =>
      match f_α.red_aff.domain? with
      | .some ⟨_, h₁⟩ =>
        .some ⟨_, _, .eql (aff_sound rfl) h₁⟩
      | .none => .none
    | (DCC? refl(f_α)) =>
      match f_α.red_aff.domain? with
      | .some ⟨_, h₁⟩ =>
        .some ⟨_, _, .refl (aff_sound rfl) h₁⟩
      | .none => .none
    | (DCC? Λ(α, β, x)) =>
      match (mk x hn.curr₀).domain? with
      | .some ⟨⟨DCC? Coup(β₂), hn⟩, h_dom⟩ =>
        if heq : (red_aff β).raw = β₂ then
          .some ⟨_, _, .curr (aff_sound rfl) (aff_sound rfl) (by
            simp_all [red_aff]
            cases heq
            exact h_dom)⟩
        else .none
      | _ => .none
    | (DCC? !Λ(α, β, x)) =>
      match (mk x hn.curr'₀).domain? with
      | .some ⟨⟨DCC? !(Coup(β₂)), hn⟩, h_dom⟩ =>
        if heq : (red_aff β).raw = β₂ then
          .some ⟨_, _, .curr' (aff_sound rfl) (aff_sound rfl) (by
            simp_all [red_aff]
            cases heq
            exact h_dom)⟩
        else .none
      | _ => .none
    | _ => .none
termination_by e.size
decreasing_by
  all_goals (grind)-/

namespace Domain

set_option maxHeartbeats 100000000000000000 in
@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
theorem complete {e τ : @NormExpr τ_c RedAff} (h : Domain e τ) : (domain? (τ_c := τ_c)) e = .some ⟨τ, h⟩ := by
  induction h
  any_goals (
    focus
    try (
      expose_names
      have ha := hrn.complete
      simp [domain?]
      cases ha
      dcc_simp_all)
    done)
  any_goals (
    focus
    try (
      expose_names
      simp [domain?, a_ih])
    done)
  any_goals (simp [domain?])
  case pair | pi =>
    expose_names
    simp [a_ih, a_ih_1]

end Domain

/-set_option maxHeartbeats 100000000000000000 in
@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
theorem Domain₂.complete
  {e α β : @NormExpr τ_c RedAff} (h : Domain₂ e α β) : e.domain₂? = .some ⟨α, β, h⟩ := by
  induction h with
  | id hr₁ hr₂ =>
    have ha := hr₁.complete
    have hb := hr₂.complete
    simp [domain₂?]
    simp [red_aff] at hb
    cases ha
    dcc_simp_all
    cases hb
    cases hr₂.eq
    rfl
  | comp' h_dom h_dom₂ heq =>
    simp [domain₂?]
    have hc := h_dom.complete
    --dcc_simp_all
    dcc_simp_all
  | refl hr h_domain | eql hr h_domain =>
    have ha := h_domain.complete
    have hb := hr.complete
    simp [domain₂?]
    dcc_simp_all
    cases hb
    dcc_simp_all [ha]
  | curr hrt₁ hrt₂ h_dom =>
    have ha := hrt₁.complete
    have hb := hrt₂.complete
    have hd := h_dom.complete
    simp [domain₂?]
    dcc_simp_all [ha, hb, hc, hd]
    rw [← ha] at hrt₁
    cases hb
    have hc := hrt₁.eq
    have hd := hrt₂.eq
    cases ha; cases hc
    dcc_simp_all
  | curr' hrt₁ hrt₂ h_dom =>
    have ha := hrt₁.complete
    have hb := hrt₂.complete
    have hd := h_dom.complete
    simp [domain₂?]
    dcc_simp_all [ha, hb, hc, hd]
    cases ha
    cases hb
    dcc_simp_all-/

@[dcc_force_reduce, aesop safe destruct (rule_sets := [DccRel])]
def Domain.unique {x τ₁ τ₂ : @NormExpr τ_c RedAff} (h₁ : Domain x τ₁) (h₂ : Domain x τ₂) : τ₁ = τ₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

def Domain.is_norm_aff {e τ : @NormExpr τ_c RedAff} (_h : Domain (τ_c := τ_c) e τ) : IsNorm RedAff τ.raw := τ.is_norm

--def Domain₂.is_norm_aff (_h : Domain₂ e α β) : IsNorm RedAff α.raw ∧ IsNorm RedAff β.raw := ⟨α.is_norm, β.is_norm⟩

def Domain.preservation {f α B : @GenericExpr τ_c} {hn_f : IsNorm RedAff f} {hn_α : IsNorm RedAff α} {hn_B : IsNorm RedAff B} (_h_dom : Domain ⟨f, hn_f⟩ ⟨α, hn_α⟩) (hr : RedAff f B) : Domain (τ_c := τ_c) ⟨B, hn_B⟩ ⟨α, hn_α⟩ :=
  hn_f.elim _ hr

/-@[dcc_force_reduce, aesop safe destruct (rule_sets := [DccRel])]
def Domain₂.unique {f τ₁a τ₁b τ₂a τ₂b : @NormExpr τ_c RedAff} (h₁ : Domain₂ f τ₁a τ₁b) (h₂ : Domain₂ f τ₂a τ₂b) : τ₁a = τ₂a ∧ τ₁b = τ₂b := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind-/

@[dcc_size]
def Domain.size_pos (h : Domain f τ) : 0 < f.size := by
  induction h <;> grind

@[dcc_force_reduce]
def Domain.eq (h₁ h₂ : Domain (τ_c := τ_c) x τ₁) : h₁ = h₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

/-@[dcc_force_reduce]
def Domain₂.eq (h₁ h₂ : Domain₂ (τ_c := τ_c) x τ₁ τ₂) : h₁ = h₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all-/

set_option maxHeartbeats 100000000000000000 in
open GenericExpr in
open NormExpr in
def Domain.decreasing {e α : @NormExpr τ_c' RedAff} (h : Domain e α) : NormExpr.size α < NormExpr.size e := by
  induction h
  any_goals (
    focus
    try (
      rename_i hr h_dom hlt
      have ha := h_dom.complete
      grind)
    done)
  any_goals (
    focus
    try (
      rename_i hn hr
      have ha := hr.complete
      dcc_simp_all [NormExpr.size]
      first | grind)
    done)
  any_goals (grind)
  case curr₂ | curr₂' =>
    expose_names
    have ha := hrn.complete
    have hb := hrn.decreasing?
    dcc_simp_all [NormExpr.size]
    grind

open GenericExpr in
open NormExpr in
def Domain.decreasing' {e α : @NormExpr τ_c RedAff} (h : Domain e α) : GenericExpr.size α.raw < GenericExpr.size e.raw := by
  have h := h.decreasing
  simp_all [NormExpr.size, raw]

end NormExpr

set_option maxHeartbeats 100000000000000000 in
open GenericExpr in
open NormExpr in
@[dcc_force_reduce, dcc_force_aff]
instance Domain.instRedRel : GenericExpr.RedRel.{u, u + 1} (α := @NormExpr τ_c RedAff) (Domain (τ_c := τ_c)) size where
  run := fun x => match domain? x with
    | .some ⟨_, h⟩ => .some ⟨_, ⟨h⟩⟩
    | .none => .none
  decreasing := Domain.decreasing

set_option maxHeartbeats 100000000000000000 in
open GenericExpr in
open NormExpr in
def NormExpr.Domain.to_eta {f α : @NormExpr τ_c RedAff} (h : Domain f α) : Domain f.to_eta α.to_eta :=
  match h with
  | .map _ | .unmap _  => by
    expose_names
    have h_dec₁ := a.decreasing
    have h := a.to_eta
    constructor
    · assumption
  | .refl₁ _ | .eql₁ _
    | .fmap _ => by
    all_goals (
      try expose_names)
    · have h_dec₁ := a.decreasing
      have h := a.to_eta
      constructor
      · assumption
  | .curr₁ _ | .eval _ | .curr₁' _ => by
    all_goals (
      try (rename_i hn_β _ _ hrn))
    · have ha := hrn.to_eta
      constructor
      assumption
  | .eql₂ _ _ | .refl₂ _ _ => by
    all_goals (try (expose_names))
    · have ha := hrn.to_eta
      have hb := hn_τ.to_eta
      have hc := a.to_eta
      constructor <;> assumption
  | .quot | .id | .fstc | .sndc => by
    constructor
  | .curr₂' _ _ | .curr₂ _ _ => by
    expose_names
    have hb := hrn.to_eta
    have hc := a.to_eta
    constructor <;> assumption
  | .pair _ _ | .pi _ _ => by
    expose_names
    have ha := a.to_eta
    have hb := a_1.to_eta
    constructor <;> assumption
  | .comp₂ a | .comp' a | .comp a => by
    have hb := a.to_eta
    constructor; assumption
termination_by (size f)
decreasing_by
  any_goals (grind)

def NormExpr.Domain.no_holes (h : Domain f α) (hn : ¬ f.raw.contains_hole) : ¬ α.raw.contains_hole := by
  induction h
  any_goals (
    focus
    try (
      expose_names
      have hrn := GenericExpr.RedAffNorm.tail_no_hole (by assumption) (by grind)
      have h := a_ih (by grind)
      grind)
    done)
  any_goals (
    focus
    try (
      expose_names
      have h := a_ih (by grind)
      grind)
    done)
  any_goals (grind)

open GenericExpr in
def NormExpr.Domain.from_eta {f α : @EtaExpr.Norm τ_c} (h : Domain f α)
  (hn₁ : ¬ f.raw.contains_hole)
  (hn₂ : ¬ α.raw.contains_hole) : Domain (f.from_eta hn₁) (α.from_eta hn₂) := by
  cases h
  any_goals (
    focus
    try (
      expose_names
      constructor
      exact a.from_eta (by grind) (by grind))
    done)
  any_goals (
    focus
    try (
      expose_names
      have h_dec := hrn.decreasing?
      have h := hrn.tail_no_hole (by grind)
      constructor
      · exact hrn.from_eta (hn₁ := by grind)
      · exact a.from_eta (by grind) (by grind))
    done)
  any_goals (
    focus
    try (
      expose_names
      have ha := hrn.tail_no_hole (by grind)
      have hb := hrn.from_eta (hn₁ := by grind)
      have hn := a.no_holes (by grind)
      have h₁ := a.from_eta (by grind) (by grind)
      constructor <;> assumption)
    done)
  case pi | pair =>
    expose_names
    have ha := a.from_eta (by grind) (by grind)
    have ha := a_1.from_eta (by grind) (by grind)
    constructor <;> assumption
  case id | fstc | sndc | quot => constructor
termination_by size f
decreasing_by
  any_goals (grind)

/-set_option maxHeartbeats 100000000000000000 in
open GenericExpr in
open NormExpr in
def NormExpr.Domain₂.to_eta {f α : @NormExpr τ_c RedAff} (h : Domain₂ f α β) : Domain₂ f.to_eta α.to_eta β.to_eta :=
  match h with
  | .id _ _ => by
    expose_names
    have ha := hn_α.to_eta
    have hc := a.to_eta
    have hd := a_1.to_eta
    constructor <;> assumption
  | .comp' _ _ => by
    expose_names
    have hb := hn_γ.to_eta
    have he := a.to_eta
    have hf := a_1.to_eta
    constructor <;> assumption
  | .eql _ _ => by
    expose_names
    have ha := hn_f_α'.to_eta
    have hb := hn_δ.to_eta
    have hc := hrn₁.to_eta
    have hd := a.to_eta
    constructor <;> assumption
  | .refl _ _ => by
    expose_names
    have ha := hn_f_α'.to_eta
    have hb := hn_δ.to_eta
    have hc := hrn₁.to_eta
    have hd := a.to_eta
    constructor <;> assumption
  | .curr _ _ _ => by
    expose_names
    have ha := hn_β.to_eta
    have hb := hrn₁.to_eta
    have hc := hrn₂.to_eta
    have he := a.to_eta
    constructor <;> assumption
  | .curr' _ _ _ => by
    expose_names
    have ha := hn_α'.to_eta
    have hb := hn_β'.to_eta
    have he := hrn₁.to_eta
    have hf := hrn₂.to_eta
    have hg := a.to_eta
    constructor <;> assumption-/

/-def NormExpr.Domain₂.no_holes (h : Domain₂ f α β) (hn : ¬ f.raw.contains_hole) : (¬ α.raw.contains_hole) ∧ (¬ β.raw.contains_hole) := by
  induction h
  case id =>
    expose_names
    have hrn := GenericExpr.RedAffNorm.tail_no_hole (by assumption) (by grind)
    have hrn := GenericExpr.RedAffNorm.tail_no_hole a (by grind)
    grind
  case comp' =>
    expose_names
    have ha := a_ih (by grind)
    have hb := a.no_holes (by grind)
    grind
  case eql | refl | curr | curr' =>
    expose_names
    have hrna := GenericExpr.RedAffNorm.tail_no_hole hrn₁ (by grind)
    have hb := a.no_holes (by grind)
    grind-/

/-set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
def NormExpr.Domain₂.from_eta {f α β : @EtaExpr.Norm τ_c} (h : Domain₂ f α β)
  (hn₁ : ¬ f.raw.contains_hole)
  (hn₂ : ¬ α.raw.contains_hole)
  (hn₃ : ¬ β.raw.contains_hole)
  : Domain₂ (f.from_eta (by grind)) (α.from_eta (by grind))
  (β.from_eta (by grind)) := by
  let hn₃₀ := hn₃
  cases h
  case id =>
    expose_names
    constructor
    · exact a.from_eta (hn₁ := by grind)
    · exact a_1.from_eta (hn₁ := by grind)
  case comp' =>
    expose_names
    have h₀   := a.no_holes (by grind)
    have h₁   := a_1.no_holes (by grind)
    have a'   := a.from_eta (by grind) (by grind)
    have a_1' := a_1.from_eta (by grind) (by grind)
    have h₂   := hn.from_eta (by grind)
    have ha   := hn.comp'r.from_eta (by grind)
    have hb   := hn_γ.from_eta (by grind)
    have he   := a.no_holes (by grind)
    have he   := a.from_eta (by grind) (by grind) (by grind)
    constructor <;> assumption
  case eql | refl =>
    expose_names
    have ha := hrn₁.from_eta (hn₁ := by grind)
    have hb := hrn₁.tail_no_hole (by grind)
    have hc := a.from_eta (by grind) (by grind)
    constructor <;> assumption
  case curr' | curr =>
    expose_names
    have ha := a.no_holes (by grind)
    have hb := hrn₁.tail_no_hole (by grind)
    have hc := hrn₂.tail_no_hole (by grind)
    have hd := hrn₁.to_eta
    have he := hrn₁.from_eta (hn₁ := by grind)
    have hf := a.from_eta (by grind) (by grind)
    have hh := hn.from_eta (by grind)
    have hj := hrn₂.from_eta (hn₁ := by grind)
    constructor <;> assumption-/

open GenericExpr in
open NormExpr in
instance Domain.instEtaRel : (EtaRel (β := @NormExpr τ_c RedAff) Domain (m := Option)) where
  run      := domain?
  complete := Domain.complete

open GenericExpr in
open NormExpr in
instance Domain.instFallibleEtaRel : (FallibleEtaRel (Domain (τ_c := τ_c)) (m := Option)) where
  none     := fun heq hr => by
    have h := hr.complete
    simp_all
    grind
  none_complete := fun h => by
    simp [failure]
    apply Option.eq_none_iff_forall_ne_some.mpr
    intro ⟨_, hr⟩
    exact (h hr).elim

open GenericExpr in
open NormExpr in
instance Domain.instOptionEtaRel : OptionEtaRel (Domain (τ_c := τ_c)) where

def NormExpr.Domain.arity_pos (h : Domain f α) : 0 < arity f := by
  induction h
  any_goals (grind)

/-def NormExpr.unary_to_eta (hn : ∀ α β, Domain₂ f α β → False) : ∀ α β, Domain₂ f.to_eta α β → False := by
  intro α β h
  have hn_mem := h.no_holes GenericExpr.to_eta_no_hole
  have h_dom := h.from_eta GenericExpr.to_eta_no_hole hn_mem.left hn_mem.right
  dcc_simp [from_eta] at h_dom
  exact hn _ _ h_dom-/

/-def NormExpr.domain₂?_none_sound (h_none : domain₂? (τ_c := τ_c) f = .none := by assumption) : ∀ α β, Domain₂ f α β → False := by
  intro α β h_dom
  have heq := h_dom.complete
  grind-/

/-def NormExpr.domain₂_none_complete (hn : ∀ α β, Domain₂ (τ_c := τ_c) f α β → False) : domain₂? f = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro h
  exact (hn _ _ h.2.2).elim-/

/-def NormExpr.domain?_none_sound (h_none : domain? (τ_c' := τ_c) f = .none := by assumption) : ∀ α, Domain f α → False := by
  intro α h_dom
  have heq := h_dom.complete
  grind-/

def NormExpr.domain_none_complete (hn : ∀ α, Domain (τ_c := τ_c) f α → False) : domain? f = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro h
  exact (hn _ h.2).elim
