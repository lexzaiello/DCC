import Dcc.Eta.Nbe.Hole
import Dcc.Eta.Reflect
import Dcc.Aff.Red
import Dcc.Eta.Inj

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace NormExpr

open GenericExpr in
def id_arity₁ (h_view : ViewFnType α → False) : (NormExpr.mk (DCC? Id(α)) hn).arity = 1 := by
  simp [raw, arity]
  cases α
  any_goals (grind)
  case app f x =>
    cases f
    any_goals (grind)
    case pi =>
      exact (h_view .pi).elim

namespace EtaFn

open GenericExpr

set_option pp.rawOnError true in
inductive Canonicalize : (e_f : EtaFn (τ_c := τ_c) f doms)
  → (e_f' : EtaFn (τ_c := τ_c) f' doms)
  → Type u
  | id₁   : (e_f : EtaFn (τ_c := τ_c) ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨hole₁, hn_hole₁⟩
    → Canonicalize e_f (.tm₁ (.id (hn := fun ⟨_, .id₀ h⟩ => hn_α ⟨_, h⟩)))
  | fstc  : (e_f : EtaFn f [⟨DCC? Coup(β), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦#(expr_to_eta β)⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.to_eta.raw ⟦#(expr_to_eta β)⟧(a, b))) ⟨a, hn_hole₁.sigl⟩
    → Canonicalize e_f (.tm₁ (.fstc (hn := fun ⟨_, .fstc₀ h⟩ => hn_coup ⟨_, .coup₀ h⟩)))
  | sndc  : (e_f : EtaFn f [⟨DCC? Coup(β), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦#(expr_to_eta β)⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.to_eta.raw ⟦#(expr_to_eta β)⟧(a, b))) ⟨b, hn_hole₁.sigr⟩
    → Canonicalize e_f (.tm₁ (.sndc (hn := fun ⟨_, .sndc₀ h⟩ => hn_coup ⟨_, .coup₀ h⟩)))
  | fstc' : (e_f : EtaFn f [⟨DCC? !(Coup(β)), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? &(⟦#(expr_to_eta β)⟧(a, b)), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.to_eta.raw &(⟦#(expr_to_eta β)⟧(a, b)))) ⟨a, (fun ⟨_, hr⟩ => by
        have h := e_h.points_norm ⟨0, e_f.arity_pos⟩ ⟨0, by simp [dcc_size, raw, Holes.v_elems, Vector.get]⟩
        change IsNorm RedAff ((expr_to_eta β).mkc a b) at h
        exact h ⟨_, .sig₁ hr⟩)⟩
    → Canonicalize e_f
      (.tm₁
        (f := ⟨.unmap (.fstc β), fun ⟨_, .unmap₀ (.fstc₀ h)⟩ => hn_coup ⟨_, .bang₀ (.coup₀ h)⟩⟩)
        (.unmap (.fstc (hn := fun ⟨_, .fstc₀ h⟩ => hn_coup ⟨_, .bang₀ (.coup₀ h)⟩))))
  | sndc' : (e_f : EtaFn f [⟨DCC? !(Coup(β)), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? &(⟦#(expr_to_eta β)⟧(a, b)), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.to_eta.raw &(⟦#(expr_to_eta β)⟧(a, b)))) ⟨b, (fun ⟨_, hr⟩ => by
        have h := e_h.points_norm ⟨0, e_f.arity_pos⟩ ⟨0, by simp [dcc_size, raw, Holes.v_elems, Vector.get]⟩
        change IsNorm RedAff ((expr_to_eta β).mkc a b) at h
        exact h ⟨_, .sig₂ hr⟩)⟩
    → Canonicalize e_f
      (.tm₁
        (f := ⟨.unmap (.sndc β), fun ⟨_, .unmap₀ (.sndc₀ h)⟩ => hn_coup ⟨_, .bang₀ (.coup₀ h)⟩⟩)
        (.unmap (.sndc (hn := fun ⟨_, .sndc₀ h⟩ => hn_coup ⟨_, .bang₀ (.coup₀ h)⟩))))
  | par   : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨(DCC? (f' hole₁)), hn₂⟩
    → (hn  : ¬ f'.contains_hole)
    → (heq : eta_to_expr f' hn = f'')
    → (e_f' : EtaFn ⟨f'', heq ▸ hn₂.congrFun.from_eta hn⟩ [⟨α, hn_α⟩])
    → Canonicalize e_f e_f'
  -- f (g x) η-> (f ∘' g) x
  | comp'    : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (e_h   : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨(DCC? (f' (g' hole₁))), hn₂⟩
    → (hna   : ¬ f'.contains_hole)
    → (hnb   : ¬ g'.contains_hole)
    → (heq₁  : eta_to_expr f' hna = f'')
    → (heq₂  : eta_to_expr g' hnb = g'')
    → (h_dom : Domain ⟨g'', fun ⟨_, h⟩ => hn₂.congrArg.congrFun.from_eta hnb ⟨_, heq₂ ▸ h⟩⟩ ⟨α, hn_α⟩)
    → Canonicalize e_f (.tm₁ (.comp' (f := f'') (g := g'') (hn := fun ⟨_, h⟩ => match h with
      | .comp'₀ h => hn₂.congrFun.from_eta hna ⟨_, heq₁ ▸ h⟩
      | .comp'₁ h => hn₂.congrArg.congrFun.from_eta hnb ⟨_, heq₂ ▸ h⟩) h_dom))
  | eval  : (e_f : EtaFn ⟨f, hn_f⟩ [⟨DCC? Coup(β), hn₁⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦#(expr_to_eta β)⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (#(expr_to_eta f) ⟦#(expr_to_eta β)⟧(a, b))) ⟨DCC? (f' a b), hn'⟩
    → (hn  : ¬ f'.contains_hole)
    → (heq : eta_to_expr f' hn = f'')
    → (e_f' : EtaFn ⟨f'', heq ▸ hn'.congrFun.congrFun.from_eta hn⟩ [⟨α, hn_α⟩])
    → Canonicalize e_f (.tm₁ (.eval (α := α) (β := β) (x := f'') e_f'.head_dom
      (hn := fun ⟨_, h⟩ => match h with
        | .eval₀ h => hn_α ⟨_, h⟩
        | .eval₁ h => hn₁ ⟨_, .coup₀ h⟩
        | .eval₂ h => (heq ▸ hn'.congrFun.congrFun.from_eta hn) ⟨_, h⟩)))
  | quot₁ : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → (hr_τ : RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨e', hn_e'⟩)
    → (hn : ¬ e'.contains_hole)
    → (heq : eta_to_expr e' hn = e'')
    → Canonicalize e_f (.tm₁ (.quot
      (β := α)
      (hn := (fun ⟨_, h⟩ =>
        match h with
        | .quot₀ h => hn_α ⟨_, h⟩
        | .quot₁ h => (hn_e'.from_eta hn) ⟨_, heq.symm ▸ h⟩)) (x := e'')))

/-def eta_const_do_dec (x y : (@GenericExpr (@EtaConst τ_c))) : Decidable (x = y) := by
  cases x <;> cases y
  any_goals (
    (first
     | exact Decidable.isTrue rfl
     | (focus
        apply Decidable.isFalse
        intro h
        cases h
        done)))
  · exact inferInstance
  any_goals (
    focus
    try (
      rename_i x y
      have h := do_dec x y
      aesop)
    done)
  any_goals (
    focus
    try (
      rename_i x₁ x₂ x₃ y₁ y₂ y₃
      have h₁ := do_dec x₁ y₁
      have h₂ := do_dec x₂ y₂
      have h₃ := do_dec x₃ y₃
      cases h₁
      case isTrue h₁ =>
        cases h₂
        case isTrue h₂ =>
          cases h₃
          case isTrue h₃ =>
            apply Decidable.isTrue; grind
          · apply Decidable.isFalse; grind
        · apply Decidable.isFalse; grind
      · apply Decidable.isFalse; grind)
    done)
  any_goals (
    focus
    try (
      rename_i x₁ x₂ y₁ y₂
      have h₁ := do_dec x₁ y₁
      have h₂ := do_dec x₂ y₂
      cases h₁
      case isTrue h₁ =>
        cases h₂
        · apply Decidable.isFalse; grind
        · apply Decidable.isTrue; grind
      · apply Decidable.isFalse; grind)
    done)
  case const x y =>
    cases x with
    | hole =>
      cases y with
      | hole => exact inferInstance
      | const _ => apply Decidable.isFalse; grind
    | const x =>
      cases y with
      | hole => apply Decidable.isFalse; grind
      | const y => exact inferInstance

instance : DecidableEq (@GenericExpr (@EtaConst τ_c)) := eta_const_do_dec-/

def canonicalize₁_par? {f : @GenericExpr τ_c}
  {hn : IsNorm RedAff f}
  {α : @GenericExpr τ_c} {hn_α : IsNorm RedAff α} (e_f : EtaFn ⟨f, hn⟩ [mk α hn_α])
  (e_holes  : e_f.Holes 0 [⟨e_hole, hn_hole⟩])
  : Option ((f' : @NormExpr τ_c RedAff) × (e_f' : EtaFn f' [mk α hn_α]) × e_f.Canonicalize e_f') :=
  match h_app_eq : (reduce RedAff (DCC? (#(expr_to_eta f) e_hole))) with
  | ⟨DCC? (f' (g' e_hole')), ⟨hr⟩⟩ =>
    have hn := reduce_norm h_app_eq
    if heq₁ : e_hole = e_hole' then
      if heq₂ : ¬ f'.contains_hole then
        if heq₃ : ¬ g'.contains_hole then
          let g'' := GenericExpr.eta_to_expr g' heq₃
          let g' : @NormExpr τ_c RedAff := ⟨g'', hn.congrArg.congrFun.from_eta (by grind)⟩
          match domain? g' with
          | .some ⟨α', e_g'⟩ =>
            if heq₂ : α' = mk α hn_α then by
              cases heq₁; cases heq₂
              exact .some ⟨_, _, .comp' e_f e_holes ⟨hr, hn⟩ heq₂ heq₃ rfl rfl e_g'⟩
            else .none
          | .none => .none
        else .none
      else .none
    else .none
  | ⟨DCC? (f' e_hole'), ⟨hr⟩⟩ =>
    have hn := reduce_norm h_app_eq
    if heq₁ : e_hole = e_hole' then
      if heq₂ : ¬ f'.contains_hole then
        let f'' := GenericExpr.eta_to_expr f' heq₂
        let f' : @NormExpr τ_c RedAff := ⟨f'', hn.congrFun.from_eta (by grind)⟩
        match view_eta_fn f' with
        | .some ⟨doms', e_f'⟩ =>
          if heq₂ : doms' = [mk α hn_α] then by
            cases heq₁; cases heq₂
            exact .some ⟨_, _, .par e_f e_holes ⟨hr, hn⟩ heq₂ rfl e_f'⟩
          else .none
        | .none => .none
      else .none
    else .none
  | _ => .none

def canonicalize₁ {f : @GenericExpr τ_c}
  {hn : IsNorm RedAff f}
  (α : @GenericExpr τ_c) (hn_α : IsNorm RedAff α) (e_f : EtaFn ⟨f, hn⟩ [mk α hn_α]) :
  Option ((f' : @NormExpr τ_c RedAff) × (e_f' : EtaFn f' [mk α hn_α]) × e_f.Canonicalize e_f') :=
  match e_f.holes 0 with
  | .some ⟨[⟨e_hole, hn_hole⟩], h_holes⟩ =>
    if heq : (reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst = e_hole then by
      have h := aff_sound' (DCC? (#(expr_to_eta f) e_hole))
      simp [heq] at h
      exact .some ⟨_, _, .id₁ e_f h_holes h⟩
    else if h_contains : ((reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst).hole_mem_tm then
      match e_f.canonicalize₁_par? h_holes with
      | .some ⟨_, h⟩ => .some ⟨_, h⟩
      | .none =>
        match heq_some : α.view_coup_bang? with
        | .some h => by
          cases h with
          | coup =>
            rename_i β
            match e_hole with
            | DCC? ⟦β₂⟧(a, b) =>
              if heqc : β₂ = expr_to_eta β then
                if heqa : (reduce RedAff (DCC? (#(expr_to_eta f) ⟦#(expr_to_eta β)⟧(a, b)))).fst = a then
                  have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                  cases heqc
                  exact .some ⟨_, _, .fstc e_f h_holes ⟨hr, hn⟩⟩
                else if heqa : (reduce RedAff (DCC? (#(expr_to_eta f) ⟦#(expr_to_eta β)⟧(a, b)))).fst = b then
                  have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                  cases heqc
                  exact .some ⟨_, _, .sndc e_f h_holes ⟨hr, hn⟩⟩
                else
                  match h_app_eq : (reduce RedAff (DCC? (#(expr_to_eta f) ⟦#(expr_to_eta β)⟧(a, b)))) with
                  | ⟨DCC? (f' a' b'), ⟨hr⟩⟩ =>
                    change @EtaExpr τ_c at f'
                    have hn' := reduce_norm h_app_eq
                    if heqa : a' = a then
                      if heqb : b' = b then
                        if hn'' : f'.contains_hole then
                          exact .none
                        else
                          let f'' := GenericExpr.eta_to_expr f' hn''
                          let f'₁ : @NormExpr τ_c RedAff := ⟨f'', hn'.congrFun.congrFun.from_eta hn''⟩
                          match f'₁.view_eta_fn with
                          | .some ⟨doms, e_f'⟩ =>
                            match doms with
                            | [α] =>
                              cases heqc; cases heqa; cases heqb
                              exact .some ⟨_, _, .eval e_f h_holes ⟨hr, hn'⟩ hn'' rfl e_f'⟩
                          | .none => exact .none
                      else exact .none
                    else exact .none
                  | _ => exact .none
              else exact .none
            | _ => exact .none
          | bang =>
            rename_i β
            match e_hole with
            | DCC? &(⟦β₂⟧(a, b)) =>
              if heqc : β₂ = expr_to_eta β then
                if heqa : (reduce RedAff (DCC? (#(expr_to_eta f) &(⟦#(expr_to_eta β)⟧(a, b))))).fst = a then
                  have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                  cases heqc
                  exact .some ⟨_, _, .fstc' e_f h_holes ⟨hr, hn⟩⟩
                else if heqa : (reduce RedAff (DCC? (#(expr_to_eta f) &(⟦#(expr_to_eta β)⟧(a, b))))).fst = b then
                  have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                  cases heqc
                  exact .some ⟨_, _, .sndc' e_f h_holes ⟨hr, hn⟩⟩
                else exact .none
              else exact .none
            | _ => exact .none
        | .none => .none
    else
      if hn' : ((reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst).contains_hole then
        .none
      else .some ⟨_, _, .quot₁ e_f h_holes (aff_sound' _) hn' rfl⟩
  | _ => .none

/-def canonicalize₁ {f : @GenericExpr τ_c}
  {hn : IsNorm RedAff f}
  (α : @GenericExpr τ_c) (hn_α : IsNorm RedAff α) (e_f : EtaFn ⟨f, hn⟩ [mk α hn_α]) :
  Option ((f' : @NormExpr τ_c RedAff) × (e_f' : EtaFn f' [mk α hn_α]) × e_f.Canonicalize e_f') :=
  match e_f.holes 0 with
  | .some ⟨[⟨e_hole, hn_hole⟩], h_holes⟩ =>
    if heq : (reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst = e_hole then
      if heq₂ : (view_fn_type? α).isNone then by
        have h := aff_sound' (DCC? (#(expr_to_eta f) e_hole))
        simp [heq] at h
        exact .some ⟨_, _, .id₁ e_f (view_fn_type?_none_sound' heq₂) h_holes h⟩
      else .none
    else if h_contains : ((reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst).hole_mem_tm then
      match heq_some : α.view_coup_bang? with
      | .some h => by
        cases h with
        | coup =>
          rename_i β
          match e_hole with
          | DCC? ⟦β₂⟧(a, b) =>
            if heqc : β₂ = expr_to_eta β then
              if heqa : (reduce RedAff (DCC? (#(expr_to_eta f) ⟦#(expr_to_eta β)⟧(a, b)))).fst = a then
                have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                cases heqc
                exact .some ⟨_, _, .fstc e_f h_holes ⟨hr, hn⟩⟩
              else if heqa : (reduce RedAff (DCC? (#(expr_to_eta f) ⟦#(expr_to_eta β)⟧(a, b)))).fst = b then
                have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                cases heqc
                exact .some ⟨_, _, .sndc e_f h_holes ⟨hr, hn⟩⟩
              else
                match h_app_eq : (reduce RedAff (DCC? (#(expr_to_eta f) ⟦#(expr_to_eta β)⟧(a, b)))) with
                | ⟨DCC? (f' a' b'), ⟨hr⟩⟩ =>
                  change @EtaExpr τ_c at f'
                  have hn' := reduce_norm h_app_eq
                  if heqa : a' = a then
                    if heqb : b' = b then
                      if hn'' : f'.contains_hole then
                        exact .none
                      else
                        let f'' := GenericExpr.eta_to_expr f' hn''
                        let f' : @NormExpr τ_c RedAff := ⟨f'', hn'.congrFun.congrFun.from_eta hn''⟩
                        match f'.view_eta_fn with
                        | .some ⟨doms, e_f'⟩ =>
                          match doms with
                          | [α, ⟨β', hn⟩] =>
                            if heq_β' : β' = β then
                              cases heq_β'; cases heqc; cases heqa; cases heqb
                              exact .some ⟨_, _, .eval e_f h_holes ⟨hr, hn'⟩ hn'' rfl e_f'⟩
                            else exact .none
                          | _ => exact .none
                        | .none => exact .none
                    else exact .none
                  else exact .none
                | _ => exact .none
            else exact .none
          | _ => exact .none
        | bang =>
          rename_i β
          match e_hole with
          | DCC? &(⟦β₂⟧(a, b)) =>
            if heqc : β₂ = expr_to_eta β then
              if heqa : (reduce RedAff (DCC? (#(expr_to_eta f) &(⟦#(expr_to_eta β)⟧(a, b))))).fst = a then
                have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                cases heqc
                exact .some ⟨_, _, .fstc' e_f h_holes ⟨hr, hn⟩⟩
              else if heqa : (reduce RedAff (DCC? (#(expr_to_eta f) &(⟦#(expr_to_eta β)⟧(a, b))))).fst = b then
                have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                cases heqc
                exact .some ⟨_, _, .sndc' e_f h_holes ⟨hr, hn⟩⟩
              else exact .none
            else exact .none
          | _ => exact .none
      | .none =>
        match h_red_eq : (reduce RedAff (DCC? (#(expr_to_eta f) e_hole))) with
        | ⟨DCC? (f' e_hole'), ⟨hr⟩⟩ =>
          have hn' := reduce_norm h_red_eq
          if h_hole_eq : e_hole' = e_hole then
            if hn'' : f'.contains_hole then .none
            else
              let f'' := GenericExpr.eta_to_expr f' hn''
              let f' : @NormExpr τ_c RedAff := ⟨f'', hn'.congrFun.from_eta (by grind)⟩
              match f'.view_eta_fn with
              | .some ⟨doms', e_fn'⟩ => by
                if heq_doms : doms' = [mk α hn_α] then
                  cases heq_doms
                  cases h_hole_eq
                  exact .some ⟨_, _, .par e_f (view_coup_bang?_none_sound' (by grind)) h_holes ⟨hr, hn'⟩ (by grind) rfl e_fn'⟩
                else exact .none
              | _ => .none
          else .none
        | _ => .none
    else
      if h_some : (view_quot? ((reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst)).isNone then
        if hn' : ((reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst).contains_hole then
          .none
        else .some ⟨_, _, .quot₁ e_f h_holes (aff_sound' _) (view_quot?_none_sound' h_some) hn' rfl⟩
      else .none
  | _ => .none-/

/-def canonicalize₂ {f : @GenericExpr τ_c}
  {hn : IsNorm RedAff f} (α : @GenericExpr τ_c) (hn_α : IsNorm RedAff α) (β : @GenericExpr τ_c)
  (hn_β : IsNorm RedAff β) (e_f : (mk f hn).EtaFn [mk α hn_α, mk β hn_β]) :
  Option ((f' : @NormExpr τ_c RedAff) × (e_f' : EtaFn f' [mk α hn_α, mk β hn_β]) × e_f.Canonicalize e_f') :=
  match e_f.holes 0 with
  | .some ⟨[⟨e_hole₁, hn_hole₁⟩, ⟨e_hole₂, hn_hole₂⟩], h_holes⟩ =>
    if h_contains : ((reduce RedAff (DCC? (#(expr_to_eta f) e_hole₁ e_hole₂))).fst).hole_mem_tm then
      match h_red_eq : (reduce RedAff (DCC? (#(expr_to_eta f) e_hole₁ e_hole₂))) with
      | ⟨DCC? (e_hole₁' e_hole₂'), ⟨hr⟩⟩ =>
        have hn' := reduce_norm h_red_eq
        if heqa : e_hole₁' = e_hole₁ then
          if heqb : e_hole₂' = e_hole₂ then
            match α with
            | DCC? (Π(f_α, f_β) x_α) =>
              match β with
              | DCC? `((Π(f_α₂, f_β₂) x_α₂), τ') =>
                if heqc : (DCC? `((Π(f_α₂, f_β₂) x_α₂), τ')) = (DCC? `((Π(f_α, f_β) x_α), #((reduce RedAff (DCC? (f_α x_α))).fst))) then by
                  cases heqc
                  cases heqa
                  cases heqb
                  exact .some ⟨_, _, .id₂ e_f (aff_sound' (DCC? (f_α x_α))) h_holes ⟨hr, hn'⟩⟩
                else .none
              | _ => .none
            | _ => .none
          else .none
        else .none
      | _ => .none
    else
      match β with
      | (DCC? !<β>) =>
        match α with
        | DCC? !(α) =>
          if h : (reduce RedAff ((f.expr_to_eta.app e_hole₁).app e_hole₂)).fst.contains_hole then
            .none
          else .some ⟨_, _, .quot_bang e_f h_holes (aff_sound' _) h_contains (by grind) rfl⟩
        | _ => .none
      | DCC? `(α₂, β) =>
        if heq_α : α₂ = α then by
          cases heq_α
          if h : (reduce RedAff ((f.expr_to_eta.app e_hole₁).app e_hole₂)).fst.contains_hole then
            exact .none
          else exact .some ⟨_, _, .quot₂ e_f h_holes (aff_sound' _) h_contains (by grind) rfl⟩
        else .none
      | _ => .none
  | _ => .none-/

def canonicalize (e_f : EtaFn (τ_c := τ_c) ⟨f, hn⟩ doms) : Option ((f' : @NormExpr τ_c RedAff)
  × (e_f' : EtaFn f' doms) × Canonicalize e_f e_f') := by
  cases e_f with
  | tm₁ =>
    rename_i α dom
    cases α with
    | mk α hn_α =>
      exact canonicalize₁ α hn_α (.tm₁ dom)

def canonicalize₁_par_some₁
  {f : @NormExpr τ_c RedAff}
  {e_f : EtaFn f [mk α hn_α]}
  {e_holes  : e_f.Holes 0 [mk (DCC? ⟦#(expr_to_eta β)⟧(a, b)) hn_h]} (h_some : (canonicalize₁_par? e_f e_holes).isSome)
  (heq : (reduce RedAff (f.to_eta.raw.app (β.expr_to_eta.mkc a b))).fst = a) : False := by
  cases e_holes with
  | tm₁ _ h =>
    cases h with
    | coup =>
      expose_names
      simp [canonicalize₁_par?] at h_some
      split at h_some
      · expose_names
        have h : β.expr_to_eta = f'.app (g'.app e_hole') := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
        exact (a_2.is_not_app (by assumption)).elim
      · expose_names
        have h : β.expr_to_eta = f'.app e_hole' := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
        exact (a_2.is_not_app (by assumption)).elim
      · grind

def canonicalize₁_par_some₂
  {f : @NormExpr τ_c RedAff}
  {e_f : EtaFn f [mk α hn_α]}
  {e_holes  : e_f.Holes 0 [mk (DCC? ⟦#(expr_to_eta β)⟧(a, b)) hn_h]} (h_some : (canonicalize₁_par? e_f e_holes).isSome)
  (heq : (reduce RedAff (f.to_eta.raw.app (β.expr_to_eta.mkc a b))).fst = b) : False := by
  cases e_holes with
  | tm₁ _ h =>
    cases h with
    | coup =>
      expose_names
      simp [canonicalize₁_par?] at h_some
      split at h_some
      · expose_names
        have h : b = f'.app (g'.app e_hole') := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
        exact (a_3.is_not_app (by assumption)).elim
      · expose_names
        have h : b = f'.app e_hole' := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
        exact (a_3.is_not_app (by assumption)).elim
      · grind

def canonicalize₁_par_some₃
  {f : @NormExpr τ_c RedAff}
  {e_f : EtaFn f [mk α hn_α]}
  {e_holes  : e_f.Holes 0 [mk (DCC? &(⟦#(expr_to_eta β)⟧(a, b))) hn_h]} (h_some : (canonicalize₁_par? e_f e_holes).isSome)
  (heq : (reduce RedAff (f.to_eta.raw.app (β.expr_to_eta.mkc a b).box)).fst = a) : False := by
  cases e_holes with
  | tm₁ _ h =>
    cases h with
    | bang h =>
      cases h with
      | coup =>
        expose_names
        simp [canonicalize₁_par?] at h_some
        split at h_some
        · expose_names
          have h : β.expr_to_eta = f'.app (g'.app e_hole') := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
          exact (a_2.is_not_app (by assumption)).elim
        · expose_names
          have h : β.expr_to_eta = f'.app e_hole' := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
          exact (a_2.is_not_app (by assumption)).elim
        · grind

def canonicalize₁_par_some₄
  {f : @NormExpr τ_c RedAff}
  {e_f : EtaFn f [mk α hn_α]}
  {e_holes  : e_f.Holes 0 [mk (DCC? &(⟦#(expr_to_eta β)⟧(a, b))) hn_h]} (h_some : (canonicalize₁_par? e_f e_holes).isSome)
  (heq : (reduce RedAff (f.to_eta.raw.app (β.expr_to_eta.mkc a b).box)).fst = b) : False := by
  cases e_holes with
  | tm₁ _ h =>
    cases h with
    | bang h =>
      cases h with
      | coup =>
        expose_names
        simp [canonicalize₁_par?] at h_some
        split at h_some
        · expose_names
          have h : b = f'.app (g'.app e_hole') := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
          exact (a_3.is_not_app (by assumption)).elim
        · expose_names
          have h : b = f'.app e_hole' := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
          exact (a_3.is_not_app (by assumption)).elim
        · grind

def canonicalize₁_par_some₅
  {f : @NormExpr τ_c RedAff}
  {e_f : EtaFn f [mk α hn_α]}
  {e_holes  : e_f.Holes 0 [mk (DCC? ⟦#(expr_to_eta β)⟧(a, b)) hn_h]}
  (h_some : (canonicalize₁_par? e_f e_holes).isSome)
  (heq : (reduce RedAff (f.to_eta.raw.app (β.expr_to_eta.mkc a b))).fst = (app (app f' a) b)) : False := by
  simp [canonicalize₁_par?] at h_some
  split at h_some
  case h_2 heq_2 | h_1 heq_2 =>
    have h := ((Sigma.ext_iff.mp heq_2).left.symm.trans heq).symm
    expose_names
    have hn_mem : ¬ f.1.expr_to_eta.hole_mem_tm := to_eta_no_mem_hole
    split at h_some
    case isTrue heq₃ =>
      cases heq₃
      have heq_f' : f'.app a = f'_1 := by grind
      cases heq_f'
      have h_mem : (f'.app a).contains_hole := by
        have h_mem := mem_imp_contains_hole (match e_holes with
          | .tm₁ _ h => h.sigl_hole_mem_tm)
        grind
      simp [h_mem] at h_some
    · grind
  · grind

@[dcc_force_reduce]
def Canonicalize.unique {f₁ f₂ : @NormExpr τ_c RedAff} {e_f : EtaFn f₁ doms} {e_f₁ : EtaFn f₂ doms} {e_f₂ : EtaFn f₂ doms}
  (h₁ : Canonicalize (τ_c := τ_c) e_f e_f₁)
  (h₂ : Canonicalize (τ_c := τ_c) e_f e_f₂) : e_f₁ = e_f₂ := by
  induction h₁
  any_goals (
    focus
    try (
      cases e_f₂
      rename_i h_dom
      cases h_dom
      rename_i hrn _
      cases hrn
      rfl)
    done)
  case fstc' | sndc' =>
    cases h₂ with
    | par =>
      expose_names
      cases e_h.unique e_h_1
      have h := match e_h with
      |.tm₁ _ h => mem_imp_contains_hole h.sigt_hole_mem_tm_box
      have h := to_eta_no_hole (e := β)
      grind
    | _ => grind
  case comp' =>
    expose_names
    cases h₂
    case par =>
      expose_names
      cases e_f_1.holes_same e_f_1 e_h_1 e_h
      cases a_1.unique a
    case comp' =>
      expose_names
      cases h_dom.eq h_dom_1
      rfl
  case par =>
    expose_names
    cases h₂
    case id₁ =>
      cases e_f'
      expose_names
      cases h_dom
      rfl
    case fstc | sndc | fstc' | sndc' | eval =>
      expose_names
      cases e_f_1.holes_same e_f_1 e_h_1 e_h
      cases a_2.unique a
    case par =>
      expose_names
      cases e_f'
      cases e_f₂
      expose_names
      cases h_dom.eq h_dom_1
      rfl
    case comp' =>
      expose_names
      cases e_f_1.holes_same e_f_1 e_h_1 e_h
      cases a_1.unique a
    case quot₁ =>
      expose_names
      cases e_f_1.holes_same e_f_1 e_h_1 e_h
      cases hr_τ.unique a
      rw [← heq_1] at heq
      grind
  case eval =>
    cases e_f₂
    rename_i h_dom
    cases h_dom
    rename_i h_dom₀
    expose_names
    cases e_f'
    simp [head_dom]
    rename_i h_dom'
    cases h_dom'.eq h_dom₀
    rfl

set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
set_option maxHeartbeats 100000000000 in
def Canonicalize.complete {f f' : @NormExpr τ_c RedAff}
  {e_f : EtaFn f doms}
  {e_f' : EtaFn f' doms}
  (h : Canonicalize e_f e_f') : canonicalize e_f = .some ⟨f', e_f', h⟩ := by
  induction h
  case id₁ =>
    rename_i e_f₁ e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f₁
    simp [canonicalize]
    unfold canonicalize₁
    simp [h_heq, heq]
    have ha := hrt.out_eq
    have hb := (ha ▸ hrt).eq
    grind
  case fstc =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    rename_i h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    change (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b))).fst = _ at heq
    have hneq : a ≠ β.expr_to_eta.mkc a b := fun h => by cases h
    have h_mem : a.hole_mem_tm = true := by
      cases e_h
      rename_i e_h
      have h := e_h.sigl_hole_mem_tm
      exact h
    simp [h_heq, heq, hneq, h_mem]
    split
    · exact (canonicalize₁_par_some₁ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
    · simp [view_coup_bang?]
      have h : (reduce RedAff (f.1.expr_to_eta.app ((expr_to_eta β).mkc a b))).fst = a := heq
      simp [h]
      split
      simp
      let ha := (hrt.out_eq ▸ hrt).eq
      rename_i a b
      let hb := ((RedAffNorm.mk a b).out_eq ▸ (RedAffNorm.mk a b)).eq
      have he := ha.trans hb.symm
      grind
  case sndc =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    rename_i h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    change (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b))).fst = _ at heq
    have hneq : b ≠ β.expr_to_eta.mkc a b := fun h => by cases h
    have h_mem : b.hole_mem_tm = true := by
      cases e_h
      rename_i e_h
      have h := e_h.sigr_hole_mem_tm
      exact h
    have hn_a_eq := match e_h with | .tm₁ _ h => h.coup_points_neq
    simp [h_heq, heq, hneq, h_mem]
    split
    · exact (canonicalize₁_par_some₂ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
    · simp [view_coup_bang?]
      have h : (reduce RedAff (f.1.expr_to_eta.app ((expr_to_eta β).mkc a b))).fst = b := heq
      simp [h, hn_a_eq.symm]
      split
      simp
      let ha := (hrt.out_eq ▸ hrt).eq
      rename_i a b
      let hb := ((RedAffNorm.mk a b).out_eq ▸ (RedAffNorm.mk a b)).eq
      have he := ha.trans hb.symm
      grind
  case eval =>
    rename_i f hn_f βt ahn₁ a₁ b hn_hole₁ f' hn' _ α hn_α e_f e_h hrt hn_mem heq_eta e_f'
    have heq := hrt.complete_fst
    have heq₀ := hrt.complete_snd
    have h_heq := e_h.complete
    cases e_f
    rename_i _heq h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    have h_mem : ((f'.app a₁).app b).hole_mem_tm := by
      cases e_h with
      | tm₁ _ h =>
        have h := h.sigl_hole_mem_tm
        grind
    have hneqa : (f'.app a₁).app b ≠ βt.expr_to_eta.mkc a₁ b := fun h => by cases h
    simp only [h_heq, heq, h_mem, hneqa]
    split
    · grind
    · split
      · split
        case h_1 heq' =>
          exact (canonicalize₁_par_some₅ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
        · have hneqa : (f'.app a₁).app b ≠ a₁ := fun h => by cases h
          have hneqb : (f'.app a₁).app b ≠ b := fun h => by cases h
          simp [view_coup_bang?, heq, hneqa, hneqb]
          split
          case h_1 heq' =>
            expose_names
            have heq' : (f'_2.app a').app b' = ((f'.app a₁).app b) := by
              grind
            cases heq'
            have h_contains := mem_imp_contains_hole (match e_h with
              | .tm₁ _ h => h.sigl_hole_mem_tm)
            have e_f'' := e_f'.complete
            simp [hn_mem]
            have heq : (Eq.mpr_not (Eq.refl (f'.contains_hole = true))
              (Eq.mpr_not (Eq.refl (f'.contains_hole = true))
                (of_eq_false
                  (Eq.trans (_root_.congrFun' (congrArg Eq (Bool.of_not_eq_true hn_mem)) true) Bool.false_eq_true)))) = hn_mem := by grind
            rw [heq]
            split
            case h_1 =>
              rename_i heq_match
              dcc_simp_all
              cases heq_eta
              have h := heq_match.symm.trans e_f''
              simp at h
              cases h.left; cases h.right
              have h := (hrt.out_eq ▸ hrt).eq
              simp
              have hrt' := RedAffNorm.mk hr hn'
              have hh := (hrt'.out_eq ▸ hrt').eq
              have he := h.trans hh.symm
              grind
            case h_2 =>
              rename_i heq_catchall
              generalize h_red : reduce RedAff (f.expr_to_eta.app (βt.expr_to_eta.mkc a₁ b)) = res
              cases res
              rename_i fst snd
              cases snd
              rename_i hr
              have h_fst : fst = (f'.app a₁).app b := by
                have h := heq
                grind
              simp_all
              have heq : (Eq.refl (f'.eta_to_expr hn_mem) ▸ IsNorm.from_eta (IsNorm.congrFun (IsNorm.congrFun hn')) hn_mem) =
                (heq_eta ▸ IsNorm.from_eta (IsNorm.congrFun (IsNorm.congrFun hn')) hn_mem) := by grind
              cases heq_eta
              grind
          case h_2 heq_catchall =>
            generalize h_red : reduce RedAff (f.expr_to_eta.app (βt.expr_to_eta.mkc a₁ b)) = res
            cases res
            rename_i fst snd
            cases snd
            rename_i hr
            have h_fst : fst = (f'.app a₁).app b := by
              have h := heq
              rw [h_red] at h
              exact h
            subst h_fst
            exact (heq_catchall f' a₁ b hr h_red).elim
      · grind
  case fstc' =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    rename_i h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    have hneq : a ≠ β.expr_to_eta.mkc a b := fun h => by cases h
    have h_mem : a.hole_mem_tm = true := by
      cases e_h
      rename_i e_h
      have h := e_h.sigl_hole_mem_tm_box
      exact h
    have hneq : a ≠ (β.expr_to_eta.mkc a b).box := fun h => by cases h
    change (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst = _ at heq
    simp [h_heq, heq, hneq, h_mem]
    split
    · exact (canonicalize₁_par_some₃ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
    · simp [view_coup_bang?, heq]
      split
      let h := (hrt.out_eq ▸ hrt).eq
      rename_i x hr hn
      let hrt' := RedAffNorm.mk hr hn
      let hh   := (hrt'.out_eq ▸ hrt').eq
      let he   := h.trans hh.symm
      expose_names
      dcc_simp_all
      aesop
  case sndc' =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    rename_i h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    have hneq : b ≠ β.expr_to_eta.mkc a b := fun h => by cases h
    have h_mem : b.hole_mem_tm = true := by
      cases e_h
      rename_i e_h
      have h := e_h.sigr_hole_mem_tm_box
      exact h
    have hneq : b ≠ (β.expr_to_eta.mkc a b).box := fun h => by cases h
    change (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst = _ at heq
    have hn_a_eq := (match e_h with | .tm₁ _ h => h.bang_coup_points_neq).symm
    simp [h_heq, heq, hneq, h_mem]
    split
    · exact (canonicalize₁_par_some₄ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
    · simp [view_coup_bang?, heq, hn_a_eq]
      split
      let h := (hrt.out_eq ▸ hrt).eq
      rename_i x hr hn
      let hrt' := RedAffNorm.mk hr hn
      let hh   := (hrt'.out_eq ▸ hrt').eq
      let he   := h.trans hh.symm
      expose_names
      dcc_simp_all
      aesop
  case par =>
    rename_i f' hn₂ e_f h_view e_h hrt hn_mem heq_eta e_f'
    have heq := hrt.complete_fst
    have heq_whole := hrt.complete
    have h_heq := e_h.complete
    expose_names
    have h_par_some : (canonicalize₁_par? h_view e_h).isSome := by
      unfold canonicalize₁_par?
      split
      case h_1 =>
        expose_names
        have heq_3 : f'_2.app (g'.app e_hole') = f'.app hole₁ := by
          grind
        have heq_4 : hole₁ = (g'.app e_hole') := by grind
        have heq_6 : f'_2 = f' := by grind
        have h := heq_6 ▸ hn_mem
        have heq_fn := e_f'.complete
        have heq_7 : f'_2.contains_hole = false := by grind
        cases heq_6
        cases heq_4
        have hneq : g'.app e_hole' ≠ e_hole' := fun h => by cases h
        simp [hneq]
        cases e_h with
        | tm₁ heq h => cases h
      case h_2 =>
        expose_names
        have heq_3 : f'_2.app e_hole' = f'.app hole₁ := by
          grind
        have heq_4 : hole₁ = e_hole' := by grind
        have heq_6 : f'_2 = f' := by grind
        have h := heq_6 ▸ hn_mem
        have heq_fn := e_f'.complete
        have heq_7 : f'_2.contains_hole = false := by grind
        cases heq_6
        cases heq_4
        simp [hn_mem]
        split
        case h_1 =>
          expose_names
          have heq : f'.eta_to_expr (of_eq_true
            (Eq.trans
              (congrArg Not
                (Eq.trans (_root_.congrFun' (congrArg Eq (Bool.of_not_eq_true hn_mem)) true) Bool.false_eq_true))
              not_false_eq_true)) = f'.eta_to_expr hn_mem := by grind
          have ha := e_f'_2.complete
          have hb := e_f'.complete
          split
          case isTrue =>
            aesop
          case isFalse =>
            simp [heq] at e_f'_2
            cases e_f'_2 with
            | tm₁ h_dom₂ =>
              cases e_f' with
              | tm₁ h_dom₃ =>
                simp_all
                cases heq_eta
                cases h_dom₂.unique h_dom₃
                grind
        case h_2 => aesop
      case h_3 x =>
        expose_names
        have heq' : (reduce RedAff (f_1.expr_to_eta.app hole₁)) =
          ⟨f'.app hole₁, heq ▸ (reduce RedAff (f_1.expr_to_eta.app hole₁)).snd⟩ := by
          grind
        let h := reduce_sound_fst heq
        exact (x _ _ h heq').elim
    cases h_view with
    | tm₁ =>
      simp [canonicalize]
      unfold canonicalize₁
      have hneq : f'.app hole₁ ≠ hole₁ := fun h => by cases h
      simp only [h_heq, heq, hneq]
      split
      · grind
      case isFalse =>
        have h_mem : (f'.app hole₁).hole_mem_tm := by
          match e_h with
          | .tm₁ _ h =>
            have ha := h.hole_mem_tm
            grind
        simp [h_mem]
        split
        case h_1 heq_1 =>
          simp [canonicalize₁_par?] at heq_1
          split at heq_1
          case h_1 =>
            expose_names
            have heq_red : f'.app hole₁ = f'_2.app (g'.app e_hole') := by grind
            cases heq_red
            have hneq : g'.app e_hole' ≠ e_hole' := fun h => by cases h
            simp [hneq] at heq_1
          case h_2 =>
            expose_names
            have heq : f'.app hole₁ = f'_2.app e_hole' := by grind
            cases heq
            simp [hn_mem] at heq_1
            cases heq_eta
            simp [e_f'.complete] at heq_1
            cases heq_1.left; cases heq_1.right
            dcc_simp_all
            aesop
          · grind
        · simp_all
  case quot₁ =>
    expose_names
    have heq := hr_τ.complete_fst
    have heq_whole := hr_τ.complete
    have h_heq  := e_h.complete
    have h_heq₁ := e_f.complete
    have h_heq₂ := e_f'.complete
    have h_heq₃ := e_f_1.complete
    cases e_f_1
    simp [canonicalize]
    unfold canonicalize₁
    expose_names
    cases heq_1
    have hneq : e' ≠ hole₁ := fun h => by
      match e_h with
      | .tm₁ _ h =>
        have ha := h.contains_hole
        grind
    have hn_mem : ¬ e'.hole_mem_tm := by
      intro h
      have h := mem_imp_contains_hole h
      grind
    simp only [h_heq, heq, hneq]
    simp [hn_mem, hn, heq]
    dcc_simp_all
    congr!
    have ha := hr_τ.out_eq
    have hb := (hr_τ.out_eq ▸ hr_τ).eq
    grind
  case comp' =>
    expose_names
    have ha := a.complete_fst
    have hb := a.aff_complete
    cases e_f_1 with
    | tm₁ h_dom' =>
      simp [canonicalize]
      unfold canonicalize₁
      have hneq : f'_1.app (g'.app hole₁) ≠ hole₁ :=
        fun h => by cases h
      have h_mem : (f'_1.app (g'.app hole₁)).hole_mem_tm := by
        have ha := match e_h with | .tm₁ _ h => h.hole_mem_tm
        grind
      simp only [e_h.complete, ha, hneq, h_mem]
      split
      · grind
      case isFalse =>
        unfold canonicalize₁_par?
        split
        case isTrue =>
          split
          case h_1 heq_1 =>
            split at heq_1
            case h_1 heq' =>
              expose_names
              have heq' : f'_2.app (g'_1.app e_hole') = (f'_1.app (g'.app hole₁)) := by grind
              cases heq'
              simp [hna, hnb] at heq_1
              cases heq₂
              cases heq₁
              simp [h_dom.complete] at heq_1
              cases heq_1.left; cases heq_1.right
              dcc_simp_all
              aesop
            case h_2 heq' =>
              expose_names
              have heqa : f'_2.app e_hole' = (f'_1.app (g'.app hole₁)) := by grind
              cases heqa
              simp [hna] at heq_1
              cases heq₁; cases heq₂
              exact (h_3 g' hole₁ hr rfl (by grind)).elim
            · grind
          case h_2 heq' =>
            split at heq'
            case h_1 =>
              expose_names
              have heq'' : f'_2.app (g'_1.app e_hole') = f'_1.app (g'.app hole₁) := by grind
              cases heq''
              cases heq₁; cases heq₂
              simp [hna, hnb, h_dom.complete] at heq'
            case h_2 hn heq' =>
              expose_names
              have heq'' : (f'_1.app (g'.app hole₁)) = f'_2.app e_hole' := by grind
              cases heq''
              cases heq₁; cases heq₂
              simp [hna] at heq'
              exact (hn g' hole₁ hr rfl (by grind)).elim
            case h_3 hna hnb =>
              exact (hna f'_1 g' hole₁ (RedAffNorm.red a) hb).elim
        · grind

def canonicalize_none_sound {e_f : EtaFn (τ_c := τ_c) ⟨f, hn⟩ doms} (h : canonicalize e_f = .none) : ∀
  {f' : @NormExpr τ_c RedAff} {e_f' : EtaFn (τ_c := τ_c) f' doms}, Canonicalize (τ_c := τ_c) e_f e_f' → False := by
  intro _ _ h
  have heq := h.complete (τ_c := τ_c)
  grind

def Canonicalize.none_complete {e_f : EtaFn (τ_c := τ_c) ⟨f, hn⟩ doms} (h : ∀ {f' : @NormExpr τ_c RedAff}
  {e_f' : EtaFn (τ_c := τ_c) f' doms}, Canonicalize e_f e_f' → False) : canonicalize e_f = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨f', e_f', h'⟩
  exact (h h').elim

end EtaFn

/-
Canonicalize does not produce holes now
-/

namespace EtaTm

open GenericExpr

inductive Canonicalize : (e_f : EtaTm (τ_c := τ_c) f doms)
  → (e_f' : EtaTm (τ_c := τ_c) f' doms)
  → Type u
  | fn : (h   : EtaFn.Canonicalize e_f e_f') → Canonicalize (EtaTm.fn e_f) (EtaTm.fn e_f')
  | pi : (hrt : RedAffNorm (DCC? (f_β x_α)) ⟨f_β_env, hn_f_β_env⟩)
    → (e_f    : EtaFn ⟨f_β_env, hn_f_β_env⟩ doms)
    → {e_f'   : EtaFn ⟨f_β', hn_f_β'⟩ doms}
    → (e_f.Canonicalize e_f')
    → ((mk f_β' hn_f_β') ≠ ⟨f_β_env, hn_f_β_env⟩)
    → Canonicalize (EtaTm.pi (hn := hn) (f_α := f_α) (f_β := f_β) (x_α := x_α))
      (.pi (hn := fun ⟨_, h⟩ => by
        cases h with
        | congrFun h =>
          cases h with
          | pil h =>
            exact hn.congrFun.pil ⟨_, h⟩
          | pir h => exact hn_f_β' ⟨_, h⟩
        | congrArg h => exact hn.congrArg ⟨_, h⟩) (f_α := f_α) (f_β := f_β') (x_α := x_α))

def canonicalize {f : @GenericExpr τ_c} {hn : IsNorm RedAff f} (e_f : EtaTm (τ_c := τ_c) ⟨f, hn⟩ doms) : Option ((f' : @NormExpr τ_c RedAff)
  × (e_f' : EtaTm f' doms) × Canonicalize e_f e_f') :=
  match e_f with
  | .fn h =>
    match h.canonicalize with
    | .some ⟨_, _, h⟩ => .some ⟨_, _, .fn h⟩
    | .none => .none
  | .pi => by
    expose_names
    match view_eta_fn (GenericExpr.red_aff (DCC? (f_β x_α))) with
    | .some ⟨_, e_f⟩ =>
      match e_f.canonicalize with
      | .some ⟨f_β', _, h_c⟩ =>
        if hneq : f_β' ≠ GenericExpr.red_aff (DCC? (f_β x_α)) then
          exact .some ⟨_, _, .pi (GenericExpr.aff_sound' _) e_f h_c hneq⟩
        else exact .none
      | .none => exact .none
    | .none => exact .none

def Canonicalize.complete {e_f : EtaTm (τ_c := τ_c) ⟨f, hn⟩ doms} {e_f' : EtaTm (τ_c := τ_c) f' doms} (h : Canonicalize e_f e_f') : canonicalize e_f = .some ⟨f', e_f', h⟩ := by
  cases h with
  | fn h =>
    have h := h.complete
    simp [canonicalize, h]
  | pi hrt e_f h_c hneq =>
    have heq₁ := hrt.complete
    have heq₂ := e_f.complete
    have heq₃ := h_c.complete
    unfold canonicalize
    cases heq₁
    simp only
    simp [GenericExpr.red_aff, heq₂, heq₃, hneq]
    dcc_simp

def canonicalize_none_sound {f : @GenericExpr τ_c} {hn : IsNorm RedAff f} {e_f : EtaTm (τ_c := τ_c) ⟨f, hn⟩ doms} (h : canonicalize e_f = .none) : ∀
  {f' : @NormExpr τ_c RedAff} {e_f' : EtaTm (τ_c := τ_c) f' doms}, Canonicalize e_f e_f' → False := by
  intro _ _ h
  have heq := h.complete
  grind

def Canonicalize.none_complete {e_f : EtaTm (τ_c := τ_c) ⟨f, hn⟩ doms} (h : ∀ {f' : @NormExpr τ_c RedAff}
  {e_f' : EtaTm (τ_c := τ_c) f' doms}, Canonicalize e_f e_f' → False) : canonicalize e_f = .none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro ⟨f', e_f', h'⟩
  exact (h h').elim

inductive Canonicalize! : (e_f : EtaTm (τ_c := τ_c) f doms)
  → (e_f' : EtaTm (τ_c := τ_c) f' doms)
  → Type u
  | step : Canonicalize e_f e_f'           → Canonicalize! e_f e_f'
  | refl : (∀ {f' : @NormExpr τ_c RedAff} {e_f' : EtaTm (τ_c := τ_c) f' doms}, Canonicalize e_f e_f' → False) → Canonicalize! e_f e_f

def canonicalize! (e_f : EtaTm (τ_c := τ_c) f doms) : ((f' : @NormExpr τ_c RedAff)
  × (e_f' : EtaTm f' doms) × Canonicalize! e_f e_f') :=
  match heq : e_f.canonicalize with
  | .some ⟨f', e_f', h⟩ => ⟨f', e_f', .step h⟩
  | .none => ⟨f, e_f, .refl (canonicalize_none_sound heq)⟩

def Canonicalize!.complete {e_f : EtaTm (τ_c := τ_c) f doms}
  {e_f' : EtaTm (τ_c := τ_c) f' doms}
  (h : Canonicalize! e_f e_f') : canonicalize! e_f = ⟨f', e_f', h⟩ := by
  cases h with
  | step h =>
    have h := h.complete
    simp [canonicalize!]
    split <;> grind
  | refl h =>
    rename_i e_f'
    unfold canonicalize!
    split
    case h_1 h _ =>
      expose_names
      exact (h_1 h).elim
    · rfl

end EtaTm

end NormExpr

namespace GenericExpr

open NormExpr

#check False.rec

inductive Canonicalize! : (f : @GenericExpr τ_c) → (f' : @GenericExpr τ_c) → Type u
  | step  : {f₁ : @GenericExpr.{u} τ_c}
    → (hrt : RedAffNorm f₁ ⟨f₂, hn_f₂⟩)
    → (e_f : EtaTm ⟨expr_to_eta f₂, hrt.is_norm.to_eta⟩ doms)
    → {e_f' : EtaTm ⟨f₄, hn_f₄⟩ doms}
    → EtaTm.Canonicalize! e_f e_f'
    → (hn : ¬ f₄.contains_hole)
    → Canonicalize! f₁ (GenericExpr.eta_to_expr f₄ hn)
  | refl₁ : {f₁ : @GenericExpr.{u} τ_c}
    → (hrt : RedAffNorm f₁ ⟨f₂, hn_f₂⟩)
    → (hn : ∀ {doms}, NormExpr.EtaTm ⟨expr_to_eta f₂, hrt.is_norm.to_eta⟩ doms → False)
    → Canonicalize! f₁ f₂
  | refl₂ : {f₁ : @GenericExpr.{u} τ_c}
    → (hrt : RedAffNorm f₁ ⟨f₂, hn_f₂⟩)
    → (e_f : EtaTm ⟨expr_to_eta f₂, hrt.is_norm.to_eta⟩ doms)
    → {e_f' : EtaTm ⟨f₄, hn_f₄⟩ doms}
    → EtaTm.Canonicalize! e_f e_f'
    → (hn : f₄.contains_hole)
    → Canonicalize! f₁ f₂

def Canonicalize!.is_norm (h : Canonicalize! f f') : IsNorm RedAff f' := by
  cases h with
  | step =>
    expose_names
    exact hn_f₄.from_eta (by assumption)
  | refl₁ | refl₂ => assumption

def canonicalize! (f : @GenericExpr τ_c) : ((f' : @GenericExpr τ_c) × Canonicalize! f f') :=
  match heq₁ : NormExpr.view_eta_tm (red_aff f).to_eta with
  | .some ⟨_, e_f⟩ =>
    match e_f.canonicalize! with
    | ⟨⟨f', _hn_f'⟩, _e_f', h⟩ =>
      if hn : f'.contains_hole then
        ⟨_, .refl₂ (aff_sound' f) e_f h hn⟩
      else
        ⟨_, .step (aff_sound' f) e_f h hn⟩
  | .none => ⟨_, .refl₁ (aff_sound' f) (view_eta_tm_none_sound heq₁)⟩

def Canonicalize!.complete {f f' : @GenericExpr τ_c} (h : Canonicalize! f f') : canonicalize! f = ⟨f', h⟩ := by
  cases h with
  | step =>
    expose_names
    have ha := a.complete
    have hb := e_f.complete
    have hc := e_f'.complete
    have he := hrt.complete
    cases he
    unfold canonicalize!
    split
    case h_1 =>
      expose_names
      have hd := e_f_1.complete
      simp [red_aff] at heq
      simp [to_eta, hb] at heq
      cases heq.left; cases heq.right
      split
      case h_1 =>
        expose_names
        have heq' := heq_1.symm.trans ha
        cases heq'
        simp [hn]
        dcc_simp_all
    case h_2 =>
      expose_names
      simp [red_aff] at heq
      simp [to_eta, hb] at heq
  | refl₁ =>
    expose_names
    have ha := EtaTm.none_complete hn
    have he := hrt.complete
    unfold canonicalize!
    cases he
    simp [red_aff, to_eta]
    split <;> dcc_simp_all
  | refl₂ =>
    expose_names
    have ha := a.complete
    have hb := e_f.complete
    have hc := e_f'.complete
    have he := hrt.complete
    cases he
    unfold canonicalize!
    split
    case h_1 =>
      expose_names
      have hd := e_f_1.complete
      simp [red_aff] at heq
      simp [hb, to_eta] at heq
      cases heq.left; cases heq.right
      split
      case h_1 =>
        expose_names
        have heq' := heq_1.symm.trans ha
        cases heq'
        simp [hn]
        dcc_simp_all
    case h_2 =>
      expose_names
      simp [red_aff] at heq
      simp [hb, to_eta] at heq

def Canonicalize!.unique (h₁ : Canonicalize! (τ_c := τ_c) A B) (h₂ : Canonicalize! A C) : B = C := by
  have ha := h₁.complete
  have hb := h₂.complete
  grind

end GenericExpr
