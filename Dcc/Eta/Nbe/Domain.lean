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
  | eql₁     : (hrn : RedAffNorm f_α f_α')
    → Domain f_α' ⟨δ, hn_δ⟩
    → Domain ⟨(DCC? Eql(f_α)), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(δ)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => hn_δ ⟨_, h⟩⟩
  | eql₂     : (hrn : RedAffNorm (DCC? (f_α env)) ⟨τ, hn_τ⟩)
    → Domain ⟨(DCC? (Eql(f_α) &(env))), fun ⟨_, h⟩ => match h with
      | .congrFun h => nomatch h
      | .congrArg h => nomatch h⟩ ⟨(DCC? !(τ)), fun ⟨_, h⟩ => match h with | .bang h => hn_τ ⟨_, h⟩⟩
  | refl₁     : (hrn : RedAffNorm f_α f_α')
    → Domain f_α' ⟨δ, hn_δ⟩
    → Domain ⟨(DCC? refl(f_α)), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(δ)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => hn_δ ⟨_, h⟩⟩
  | refl₂     : (hrn : RedAffNorm (DCC? (f_α env)) ⟨τ, hn_τ⟩)
    → Domain ⟨(DCC? (refl(f_α) &(env))), fun ⟨_, h⟩ => match h with
      | .congrFun h => nomatch h
      | .congrArg h => nomatch h⟩ ⟨(DCC? !(τ)), fun ⟨_, h⟩ => match h with | .bang h => hn_τ ⟨_, h⟩⟩
  | unmap    : (hrn : RedAffNorm f f') → Domain f' ⟨α, hn_α⟩
    → Domain ⟨(DCC? *<f>), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(α)), fun ⟨_, h⟩ =>
      match h with
      | .bang h => hn_α ⟨_, h⟩⟩
  | unbox    : (hrn : RedAffNorm α ⟨α', hn_α'⟩)
    → Domain ⟨(DCC? *(α)), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(α')), fun ⟨_, h⟩ =>
      match h with
      | .bang h => hn_α' ⟨_, h⟩⟩
  | id       : (hrn : RedAffNorm α α') → Domain ⟨(DCC? Id(α)), fun ⟨_, h⟩ => nomatch h⟩ α'
  | fstc     : (hrn : RedAffNorm β ⟨β', hn_β'⟩) → Domain ⟨(DCC? Fst(β)), fun ⟨_, h⟩ => nomatch h⟩
    ⟨(DCC? Coup(β')), fun ⟨_, h⟩ => match h with
      | .coup h => hn_β' ⟨_, h⟩⟩
  | sndc     : (hrn : RedAffNorm β ⟨β', hn_β'⟩) → Domain ⟨(DCC? Snd(β)), fun ⟨_, h⟩ => nomatch h⟩
    ⟨(DCC? Coup(β')), fun ⟨_, h⟩ => match h with
      | .coup h => hn_β' ⟨_, h⟩⟩
  | curr₁    : (hrn : RedAffNorm α α') → Domain ⟨(DCC? Λ(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩ α'
  | curr₂    : {y : GenericExpr τ_c}
    → {hn_y : IsNorm RedAff y}
    → (hrn : RedAffNorm (DCC? (β y)) τ)
    → Domain ⟨(DCC? (Λ(α, β, x) y)), fun ⟨_, h⟩ =>
      match h with
      | .congrFun h => nomatch h
      | .congrArg h => hn_y ⟨_, h⟩⟩ τ
  | curr₁'   : (hrn : RedAffNorm α ⟨α', hn_α'⟩) → Domain ⟨(DCC? !Λ(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩ ⟨DCC? !(α'), fun ⟨_, h⟩ =>
    match h with
    | .bang h => hn_α' ⟨_, h⟩⟩
  | curr₂'   : (hrn : RedAffNorm (DCC? (β y)) τ)
    → Domain ⟨(DCC? (!Λ(α, β, x) &(y))), fun ⟨_, h⟩ =>
      match h with
      | .congrFun h => nomatch h
      | .congrArg h => nomatch h⟩ τ
  | map      : (hrn : RedAffNorm f f') → Domain f' ⟨α, hn_α⟩
    → Domain ⟨(DCC? !<f>), hn_map⟩ ⟨(DCC? !(α)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => hn_α ⟨_, h⟩⟩
  | fmap     : (hrn : RedAffNorm f f') → Domain f' ⟨α, hn_α⟩
    → Domain ⟨(DCC? $<f>), fun ⟨_, h⟩ => nomatch h⟩ ⟨(DCC? !(α)), fun ⟨_, h⟩ =>
    match h with
    | .bang h => hn_α ⟨_, h⟩⟩
  | pair     : {M N : GenericExpr τ_c}
    → (hn₁ : IsNorm RedAff M)
    → (hn₂ : IsNorm RedAff N)
    → Domain ⟨M, hn₁⟩ α
    → Domain ⟨(DCC? ⟦β⟧⟨M, N⟩), fun ⟨_, h⟩ =>
    match h with
    | .pairl h => hn₁ ⟨_, h⟩
    | .pairr h => hn₂ ⟨_, h⟩⟩ α
  /-
  TODO: Not sure how to fit Eval in here yet
  | eval     : Val.Domain Val(λ env 2 => f) α → Val.Domain Val(
  | eval     : Apply x y f'
    → Apply f' z e'
    → Apply Val(λ env 1 => Eval(_α, _β, x)) Val(neutral(⟦__β⟧(y, z))) e'-/
  | eval     : (hrn : RedAffNorm β ⟨β', hn_β⟩)
    → Domain ⟨(DCC? Eval(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩
      ⟨DCC? Coup(β'), fun ⟨_, h⟩ => match h with | .coup h => hn_β ⟨_, h⟩⟩
  | quot     : (hrn : RedAffNorm β β') → Domain ⟨(DCC? `(β, x)), fun ⟨_, h⟩ => nomatch h⟩ β'
  -- f ∘ g x
  -- again, need to handle second round
  -- can use β-reducer for this.
  | comp'    : (hrn₁ : RedAffNorm g g') → Domain g' α
    → Domain ⟨(DCC? f ∘' g), fun ⟨_, h⟩ => nomatch h⟩ α
  | comp     : (hrn₁ : RedAffNorm g g') → Domain g' α
    → Domain ⟨(DCC? f ∘ g), fun ⟨_, h⟩ => nomatch h⟩ α
  | comp₂    : (hrn₁ : RedAffNorm g g') → Domain g' α
    → Domain ⟨(DCC? f ∘∘ g), fun ⟨_, h⟩ => nomatch h⟩ α
  | pi       : (hn₁ : IsNorm RedAff f_α)
    → (hn₂ : IsNorm RedAff f_β)
    → Domain ⟨f_α, hn₁⟩ δ
    → Domain ⟨(DCC? Π(f_α, f_β)), fun ⟨_, h⟩ => match h with
      | .pil h => hn₁ ⟨_, h⟩
      | .pir h => hn₂ ⟨_, h⟩⟩ δ
deriving DecidableEq

inductive Domain₂ : @NormExpr τ_c RedAff → @NormExpr τ_c RedAff → @NormExpr τ_c RedAff → Type u
  | quot    : RedAffNorm α ⟨α', hn_α'⟩
    → Domain₂ ⟨DCC? `(α, `(β, x)), fun h => nomatch h⟩
      ⟨α', hn_α'⟩
      ⟨DCC? `(α', β), fun h => nomatch h⟩
  | id      : RedAffNorm (DCC? (f_α x_α)) ⟨α, hn_α⟩
    → RedAffNorm (DCC? (Π(f_α, f_β) x_α)) ⟨τ, hn_τ⟩
    → Domain₂ ⟨(DCC? Id((Π(f_α, f_β) x_α))), fun ⟨_, h⟩ => nomatch h⟩
      ⟨τ, hn_τ⟩
      ⟨(DCC? `(τ, α)), fun ⟨_, h⟩ => nomatch h⟩
  | comp'   : (hrn₁ : RedAffNorm f f')
    → (hrn₂ : RedAffNorm g ⟨g', hn_g'⟩)
    → Domain ⟨g', hn_g'⟩ α
    → Domain₂ f' β ⟨γ, hn_γ⟩
    → Domain₂ ⟨(DCC? (f ∘' g)), fun ⟨_, h⟩ => nomatch h⟩ α ⟨(DCC? γ ∘' g'), fun ⟨_, h⟩ => nomatch h⟩
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
    → (hrx  : RedAffNorm x x')
    → Domain x' ⟨(DCC? Coup(β')), fun ⟨_, h⟩ => match h with | .coup h => hn_β ⟨_, h⟩⟩
    → Domain₂ ⟨(DCC? Λ(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩ α' ⟨β', hn_β⟩
  | curr'    : (hrn₁ : RedAffNorm α ⟨α', hn_α'⟩)
    → (hrn₂ : RedAffNorm β ⟨β', hn_β'⟩)
    → (hrx  : RedAffNorm x x')
    → Domain x' ⟨(DCC? !(Coup(β'))), fun ⟨_, h⟩ => match h with | .bang (.coup h) => hn_β' ⟨_, h⟩⟩
    → Domain₂ ⟨(DCC? !Λ(α, β, x)), fun ⟨_, h⟩ => nomatch h⟩
      ⟨DCC? !(α'), fun ⟨_, h⟩ => match h with | .bang h => hn_α' ⟨_, h⟩⟩ ⟨DCC? !<β'>, fun ⟨_, .map₀ h⟩ => hn_β' ⟨_, h⟩⟩
deriving DecidableEq

def Domain₂.to_domain (h : Domain₂ f α β) : Domain f α :=
  match h with
  | .quot hr₁ => .quot hr₁
  | .id _hr₁ hr => .id hr
  | .comp' _hr₁ hr₂ h_dom₁ _ => .comp' hr₂ h_dom₁
  | .eql hr₁ h_dom => .eql₁ hr₁ h_dom
  | .refl hr₁ h_dom => .refl₁ hr₁ h_dom
  | .curr hr₁ hr₂ hr_x h_dom => .curr₁ hr₁
  | .curr' hr₁ hr₂ _ _ => .curr₁' hr₁

def domain? (e : @NormExpr τ_c' RedAff) : Option ((τ : @NormExpr τ_c' RedAff) × (Domain e τ)) :=
  match e with
  | ⟨e, hn⟩ =>
    match e with
    | (DCC? Eval(α, β, x)) => .some ⟨_, .eval (aff_sound rfl)⟩
    | (DCC? Eql(f_α)) =>
      match f_α.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .eql₁ (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? (Eql(_f_α) &(_env))) => .some ⟨_, .eql₂ (aff_sound rfl)⟩
    | (DCC? refl(f_α)) =>
      match f_α.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .refl₁ (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? (refl(_f_α) &(_env))) => .some ⟨_, .refl₂ (aff_sound rfl)⟩
    | (DCC? *<f>) =>
      match f.red_aff.domain? with
      | .some ⟨_, h⟩ =>
        .some ⟨_, .unmap (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? *(_α)) => .some ⟨_, .unbox (aff_sound rfl)⟩
    | (DCC? Id(_α)) => .some ⟨_, .id (aff_sound rfl)⟩
    | (DCC? Fst(_β)) => .some ⟨_, .fstc (aff_sound rfl)⟩
    | (DCC? Snd(_β)) => .some ⟨_, .sndc (aff_sound rfl)⟩
    | (DCC? Λ(_α, _β, _x)) => .some ⟨_, .curr₁ (aff_sound rfl)⟩
    | (DCC? (Λ(_α, _β, _x) y)) => .some ⟨_, .curr₂
      (y := y) (hn_y := fun ⟨_, h⟩ => hn ⟨_, .congrArg h⟩) (aff_sound rfl)⟩
    | (DCC? !Λ(_α, _β, _x)) => .some ⟨_, .curr₁' (aff_sound rfl)⟩
    | (DCC? (!Λ(_α, _β, _x) &(_y))) => .some ⟨_, .curr₂' (aff_sound rfl)⟩
    | (DCC? !<f>) =>
      match f.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .map (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? $<f>) =>
      match f.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .fmap (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? ⟦_β⟧⟨M, N⟩) =>
      let M' : @NormExpr τ_c' RedAff := ⟨M, (fun ⟨_, h⟩ => hn ⟨_, .pairl h⟩)⟩
      --let N' : @NormExpr τ_c RedAff := ⟨N, (fun ⟨_, h⟩ => hn ⟨_, .pairr h⟩)⟩

      match M'.domain? with
      | .some ⟨α, h⟩ =>
        have hn₁ : IsNorm RedAff M := (fun ⟨_, h⟩ => hn ⟨_, .pairl h⟩)
        have hn₂ : IsNorm RedAff N := (fun ⟨_, h⟩ => hn ⟨_, .pairr h⟩)

        .some ⟨α, .pair hn₁ hn₂ h⟩
      | _ => .none
    | (DCC? `(_β, _x)) => .some ⟨_, .quot (aff_sound rfl)⟩
    | (DCC? _f ∘' g) =>
      match g.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp' (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? _f ∘ g) =>
      match g.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? _f ∘∘ g) =>
      match g.red_aff.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .comp₂ (aff_sound rfl) h⟩
      | _ => .none
    | (DCC? Π(f_α, f_β)) =>
      let hn₁ : IsNorm RedAff f_α := fun ⟨_, h⟩ => hn ⟨_, .pil h⟩
      let hn₂ : IsNorm RedAff f_β := fun ⟨_, h⟩ => hn ⟨_, .pir h⟩

      let f_α' : @NormExpr τ_c' RedAff := ⟨f_α, hn₁⟩

      match f_α'.domain? with
      | .some ⟨_, h⟩ => .some ⟨_, .pi hn₁ hn₂ h⟩
      | _ => .none
    | _ => .none
termination_by e.size
decreasing_by
  all_goals (grind)

def domain₂? (e : @NormExpr τ_c RedAff) : Option ((α β : @NormExpr τ_c RedAff) × (Domain₂ e α β)) :=
  match e with
  | ⟨e, hn⟩ =>
    match e with
    | (DCC? Id((Π(f_α, f_β) x_α))) =>
      .some ⟨_, _, .id (aff_sound rfl) (aff_sound rfl)⟩
    | (DCC? (f ∘' g)) =>
      match g.red_aff.domain?, f.red_aff.domain₂? with
      | .some ⟨_, h₁⟩, .some ⟨_, _, h₂⟩ =>
        .some ⟨_, _, .comp' (aff_sound rfl) (aff_sound rfl) h₁ h₂⟩
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
      match (red_aff x).domain? with
      | .some ⟨⟨DCC? Coup(β₂), hn⟩, h_dom⟩ =>
        if heq : (red_aff β).raw = β₂ then
          .some ⟨_, _, .curr (aff_sound rfl) (aff_sound rfl) (aff_sound rfl) (by
            simp_all [red_aff]
            cases heq
            simp [red_aff] at h_dom
            exact h_dom)⟩
        else .none
      | _ => .none
    | (DCC? !Λ(α, β, x)) =>
      match (red_aff x).domain? with
      | .some ⟨⟨DCC? !(Coup(β₂)), hn⟩, h_dom⟩ =>
        if heq : (red_aff β).raw = β₂ then
          .some ⟨_, _, .curr' (aff_sound rfl) (aff_sound rfl) (aff_sound rfl) (by
            simp_all [red_aff]
            cases heq
            simp [red_aff] at h_dom
            exact h_dom)⟩
        else .none
      | _ => .none
    | (DCC? `(α, `(β, x))) =>
      .some ⟨_, _, .quot (aff_sound rfl)⟩
    | _ => .none
termination_by e.size
decreasing_by
  all_goals (grind)

namespace Domain

set_option maxHeartbeats 100000000000000000 in
@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
theorem complete {e τ : @NormExpr τ_c' RedAff} (h : Domain e τ) : (domain? (τ_c' := τ_c')) e = .some ⟨τ, h⟩ := by
  induction h
  any_goals (
    focus
    try (
      rename_i hr h_dom heq
      have ha := hr.complete
      simp [domain?]
      cases ha
      dcc_simp_all [heq])
    done)
  any_goals (
    focus
    try (
      rename_i hr
      have ha := hr.complete
      simp [domain?]
      cases ha
      dcc_simp_all)
    done)
  all_goals (
    focus
    try (
      simp [domain?]
      dcc_simp_all
      try grind))

end Domain

set_option maxHeartbeats 100000000000000000 in
@[aesop safe forward (rule_sets := [DccReduce]), dcc_rel]
theorem Domain₂.complete
  {e α β : @NormExpr τ_c RedAff} (h : Domain₂ e α β) : e.domain₂? = .some ⟨α, β, h⟩ := by
  induction h with
  | quot hr₁ =>
    have ha := hr₁.complete
    simp [domain₂?]
    cases ha
    dcc_simp_all
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
  | comp' hr₁ hr₂ h_dom h_dom₂ heq =>
    have ha := hr₁.complete
    have hb := hr₂.complete
    simp [domain₂?]
    have hc := h_dom.complete
    --dcc_simp_all
    cases ha; cases hb
    dcc_simp_all
  | refl hr h_domain | eql hr h_domain =>
    have ha := h_domain.complete
    have hb := hr.complete
    simp [domain₂?]
    dcc_simp_all
    cases hb
    dcc_simp_all [ha]
  | curr hrt₁ hrt₂ hrt₃ h_dom =>
    have ha := hrt₁.complete
    have hb := hrt₂.complete
    have hc := hrt₃.complete
    have hd := h_dom.complete
    simp [domain₂?]
    dcc_simp_all [ha, hb, hc, hd]
    rw [← ha] at hrt₁
    cases hb
    rw [← hc] at hrt₃
    have hc := hrt₁.eq
    have hd := hrt₂.eq
    cases ha; cases hb; cases hc
    cases hc
    dcc_simp_all
  | curr' hrt₁ hrt₂ hrt₃ h_dom =>
    have ha := hrt₁.complete
    have hb := hrt₂.complete
    have hc := hrt₃.complete
    have hd := h_dom.complete
    simp [domain₂?]
    dcc_simp_all [ha, hb, hc, hd]
    cases hc
    cases ha
    cases hb
    dcc_simp_all

@[dcc_force_reduce, aesop safe destruct (rule_sets := [DccRel])]
def Domain.unique {x τ₁ τ₂ : @NormExpr τ_c RedAff} (h₁ : Domain x τ₁) (h₂ : Domain x τ₂) : τ₁ = τ₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

def Domain.is_norm_aff {e τ : @NormExpr τ_c RedAff} (_h : Domain (τ_c := τ_c) e τ) : IsNorm RedAff τ.raw := τ.is_norm

def Domain₂.is_norm_aff (_h : Domain₂ e α β) : IsNorm RedAff α.raw ∧ IsNorm RedAff β.raw := ⟨α.is_norm, β.is_norm⟩

def Domain.preservation {f α B : @GenericExpr τ_c} {hn_f : IsNorm RedAff f} {hn_α : IsNorm RedAff α} {hn_B : IsNorm RedAff B} (_h_dom : Domain ⟨f, hn_f⟩ ⟨α, hn_α⟩) (hr : RedAff f B) : Domain (τ_c := τ_c) ⟨B, hn_B⟩ ⟨α, hn_α⟩ :=
  hn_f.elim _ hr

@[dcc_force_reduce, aesop safe destruct (rule_sets := [DccRel])]
def Domain₂.unique {f τ₁a τ₁b τ₂a τ₂b : @NormExpr τ_c RedAff} (h₁ : Domain₂ f τ₁a τ₁b) (h₂ : Domain₂ f τ₂a τ₂b) : τ₁a = τ₂a ∧ τ₁b = τ₂b := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

@[dcc_size]
def Domain.size_pos (h : Domain f τ) : 0 < f.size := by
  induction h <;> grind

@[dcc_force_reduce]
def Domain.eq (h₁ h₂ : Domain (τ_c := τ_c) x τ₁) : h₁ = h₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

@[dcc_force_reduce]
def Domain₂.eq (h₁ h₂ : Domain₂ (τ_c := τ_c) x τ₁ τ₂) : h₁ = h₂ := by
  have ha := h₁.complete
  have hb := h₂.complete
  simp_all

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
      have hb := hr.decreasing?
      grind)
    done)
  any_goals (
    focus
    try (
      rename_i hn hr
      have ha := hr.complete
      have hb := hr.decreasing?
      dcc_simp_all [NormExpr.size]
      first | grind)
    done)
  any_goals (grind)

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
  | .map _ _ | .unmap _ _ | .refl₁ _ _ | .eql₁ _ _
    | .fmap _ _ => by
    all_goals (
      try expose_names)
    · have h_dec₁ := a.decreasing
      have h_dec₂ := hrn.decreasing?
      have h := a.to_eta
      constructor
      · exact hrn.to_eta
      · assumption
  | .eval _ | .curr₁' _ => by
    all_goals (
      try (rename_i hn_β _ _ hrn))
    · have ha := hrn.to_eta
      have hb := hn_β.to_eta
      constructor
      assumption
  | .eql₂ _ | .refl₂ _ => by
    all_goals (try (expose_names))
    · have ha := hrn.to_eta
      have hb := hn_τ.to_eta
      constructor
      assumption
  | .unbox _ => by
    expose_names
    have ha := hn_α'.to_eta
    have hb := hrn.to_eta
    constructor
    assumption
  | .fstc _ | .sndc _  => by
    all_goals (try (expose_names))
    · have ha := hrn.to_eta
      have hb := hn_β'.to_eta
      constructor
      assumption
  | .curr₂ _ => by
    expose_names
    have ha := hn_y.to_eta
    have hb := hrn.to_eta
    constructor
    · assumption
    · assumption
  | .quot _ | .curr₂' _ | .curr₁ _ | .id _ => by
    all_goals (try (expose_names))
    · have ha := hrn.to_eta
      constructor
      assumption
  | .pi _ _ _ => by
    expose_names
    have ha := hn₁.to_eta
    have hb := hn₂.to_eta
    have hc := a.to_eta
    constructor <;> assumption
  | .pair _ _ _ => by
    expose_names
    have ha := hn₁.to_eta
    have hb := hn₂.to_eta
    have hc := a.to_eta
    constructor <;> assumption
  | .comp₂ _ _ | .comp' _ _ | .comp _ _ => by
    all_goals (try (
      expose_names
      have ha := hrn₁.to_eta
      have hb := a.to_eta
      have h_dec₁ := ha.decreasing?
      have h_dec₂ := hrn₁.decreasing?))
    constructor <;> assumption
termination_by (size f)
decreasing_by
  any_goals (grind)
  all_goals (
    focus
    try (
      expose_names
      have h_dec₁ := hrn₁.decreasing?
      grind))

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
      · exact hrn.from_eta (hn₁ := by grind)
      · have h_dec := hrn.decreasing?
        have hn := hrn.tail_no_hole (by grind)
        exact a.from_eta hn (by grind))
    done)
  any_goals (
    focus
    try (
      expose_names
      have h_dec := hrn.decreasing?
      have h := hrn.tail_no_hole (by grind)
      constructor
      · exact hrn.from_eta (hn₁ := by grind))
    done)
  · expose_names
    have h := hrn.tail_no_hole (by grind)
    have h_dec := hrn.decreasing?
    constructor
    · exact hn_y.from_eta (by grind)
    · exact hrn.from_eta (hn₁ := by grind)
  · expose_names
    constructor
    · exact hn₂_1.from_eta (by grind)
    · exact a.from_eta (by grind) (by grind)
  any_goals (
    focus
    try (
      expose_names
      have h_dec := hrn₁.decreasing?
      have h   := hrn₁.from_eta (hn₁ := by grind)
      have hn' := hrn₁.tail_no_hole (by grind)
      constructor
      · exact h
      · exact a.from_eta (by grind) (by grind))
    done)
  · expose_names
    have h₁ := a.from_eta (by grind) (by grind)
    constructor
    · exact hn₂_1.from_eta (by grind)
    · exact h₁
termination_by size f
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
      have hrn := GenericExpr.RedAffNorm.tail_no_hole (by assumption) (by grind)
      grind)
    done)
  all_goals (
    expose_names
    exact a_ih (by grind))

set_option maxHeartbeats 100000000000000000 in
open GenericExpr in
open NormExpr in
def NormExpr.Domain₂.to_eta {f α : @NormExpr τ_c RedAff} (h : Domain₂ f α β) : Domain₂ f.to_eta α.to_eta β.to_eta :=
  match h with
  | .quot _ => by
    expose_names
    have ha := hn_α'.to_eta
    have hb := a.to_eta
    constructor
    assumption
  | .id _ _ => by
    expose_names
    have ha := hn_α.to_eta
    have hb := hn_τ.to_eta
    have hc := a.to_eta
    have hd := a_1.to_eta
    constructor <;> assumption
  | .comp' _ _ _ _ => by
    expose_names
    have ha := hn_g'.to_eta
    have hb := hn_γ.to_eta
    have hc := hrn₁.to_eta
    have hd := hrn₂.to_eta
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
  | .curr _ _ _ _ => by
    expose_names
    have ha := hn_β.to_eta
    have hb := hrn₁.to_eta
    have hc := hrn₂.to_eta
    have hd := hrx.to_eta
    have he := a.to_eta
    constructor <;> assumption
  | .curr' _ _ _ _ => by
    expose_names
    have ha := hn_α'.to_eta
    have hb := hn_β'.to_eta
    have hc := x'.to_eta
    have hd := hrx.to_eta
    have he := hrn₁.to_eta
    have hf := hrn₂.to_eta
    have hg := a.to_eta
    constructor <;> assumption

def NormExpr.Domain₂.no_holes (h : Domain₂ f α β) (hn : ¬ f.raw.contains_hole) : (¬ α.raw.contains_hole) ∧ (¬ β.raw.contains_hole) := by
  induction h
  · expose_names
    have hrn := GenericExpr.RedAffNorm.tail_no_hole (by assumption) (by grind)
    grind
  · expose_names
    have hrn := GenericExpr.RedAffNorm.tail_no_hole (by assumption) (by grind)
    have hrn := GenericExpr.RedAffNorm.tail_no_hole a (by grind)
    grind
  · expose_names
    have hrna := GenericExpr.RedAffNorm.tail_no_hole hrn₁ (by grind)
    have hrnb := GenericExpr.RedAffNorm.tail_no_hole hrn₂ (by grind)
    have ha := a_ih (by grind)
    have hb := a.no_holes (by grind)
    grind
  any_goals (
    focus
    try (
      expose_names
      have hrna := GenericExpr.RedAffNorm.tail_no_hole hrn₁ (by grind)
      have hb := a.no_holes (by grind)
      grind)
    done)
  any_goals (
    focus
    try (
      expose_names
      have hrna := GenericExpr.RedAffNorm.tail_no_hole hrn₁ (by grind)
      have hrnb := GenericExpr.RedAffNorm.tail_no_hole hrn₂ (by grind)
      have hrnc := GenericExpr.RedAffNorm.tail_no_hole hrx (by grind)
      have hb := a.no_holes (by grind)
      grind))

set_option pp.deepTerms true in
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
  · expose_names
    constructor
    · exact a.from_eta
  · expose_names
    constructor
    · exact a.from_eta (hn₁ := by grind)
    · exact a_1.from_eta (hn₁ := by grind)
  · expose_names
    have ha := hn_g'.from_eta (by grind)
    have hb := hn_γ.from_eta (by grind)
    have hc := hrn₁.from_eta (hn₁ := by grind)
    have hd := hrn₂.from_eta (hn₁ := by grind)
    have he := hrn₁.tail_no_hole (by grind)
    have hf := hrn₂.tail_no_hole (by grind)
    have he := a.no_holes (by grind)
    have he := a.from_eta (by grind) (by grind) (by grind)
    constructor
    · assumption
    · assumption
    · exact a_1.from_eta (by grind) (by grind)
    · exact he
  any_goals (
    focus
    try (
      expose_names
      have ha := hrn₁.from_eta (hn₁ := by grind)
      have hb := hrn₁.tail_no_hole (by grind)
      have hc := a.from_eta (by grind) (by grind)
      constructor <;> assumption)
    done)
  any_goals (
    focus
    try (
      expose_names
      have ha := hrn₂.from_eta (hn₁ := by grind)
      have ha := hrn₁.tail_no_hole (by grind)
      have hc := hrn₁.tail_no_hole (by grind)
      have hd := hrn₁.from_eta (hn₁ := by grind)
      have he := hrx.tail_no_hole (by grind)
      have hf := hrx.from_eta (hn₁ := by grind)
      have hg := a.from_eta (by grind) (by grind)
      constructor <;> assumption))

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
