import Dcc.Eta.Nbe.Hole
import Dcc.Eta.Reflect
import Dcc.Aff.Red
import Dcc.Eta.Inj

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace GenericExpr

def IsNorm.bang (hn : IsNorm RedAff (.bang x)) : IsNorm RedAff x :=
  fun ⟨_, h⟩ => hn ⟨_, .bang h⟩

def unmap_norm : IsNorm RedAff (.unmap x) := fun ⟨_, h⟩ => by cases h

def fstc_norm  : IsNorm RedAff (.fstc x) := fun ⟨_, h⟩ => by cases h

def sndc_norm  : IsNorm RedAff (.sndc x) := fun ⟨_, h⟩ => by cases h

def quot_norm  : IsNorm RedAff (.quot x y) := fun ⟨_, h⟩ => by cases h

def mk_bang_norm (hn : IsNorm RedAff x) : IsNorm RedAff (.bang x) := fun ⟨_, h⟩ => by
  cases h with
  | bang h => exact hn ⟨_, h⟩

def mk_coup_norm (hn : IsNorm RedAff x) : IsNorm RedAff (.coup x) := fun ⟨_, h⟩ => by
  cases h with
  | coup h => exact hn ⟨_, h⟩

end GenericExpr

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

inductive Canonicalize : (e_f : EtaFn (τ_c := τ_c) f doms)
  → (e_f' : EtaFn (τ_c := τ_c) f' doms)
  → Type u
  | id₁   : (e_f : EtaFn (τ_c := τ_c) ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (n_pi_α : ViewFnType α → False)
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨hole₁, hn_hole₁⟩
    → Canonicalize e_f (.tm₁ (_heq := (id_arity₁ (by assumption))) (.id ⟨.refl, (by assumption)⟩))
  | fstc  : (e_f : EtaFn f [⟨DCC? Coup(β), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦#(expr_to_eta β)⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.to_eta.raw ⟦#(expr_to_eta β)⟧(a, b))) ⟨a, hn_hole₁.sigl⟩
    → Canonicalize e_f (.tm₁ (_heq := (by grind)) (.fstc ⟨.refl, hn_coup.coup⟩))
  | sndc  : (e_f : EtaFn f [⟨DCC? Coup(β), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦#(expr_to_eta β)⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.to_eta.raw ⟦#(expr_to_eta β)⟧(a, b))) ⟨b, hn_hole₁.sigr⟩
    → Canonicalize e_f (.tm₁ (_heq := (by grind)) (.sndc ⟨.refl, hn_coup.coup⟩))
  | fstc' : (e_f : EtaFn f [⟨DCC? !(Coup(β)), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? &(⟦#(expr_to_eta β)⟧(a, b)), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.to_eta.raw &(⟦#(expr_to_eta β)⟧(a, b)))) ⟨a, (fun ⟨_, hr⟩ => by
        have h := e_h.points_norm ⟨0, e_f.arity_pos⟩ ⟨0, by simp [dcc_size, raw, Holes.v_elems, Vector.get]⟩
        change IsNorm RedAff ((expr_to_eta β).mkc a b) at h
        exact h ⟨_, .sigl hr⟩)⟩
    → Canonicalize e_f
      (.tm₁
        (f := ⟨.unmap (.fstc β), GenericExpr.unmap_norm⟩)
        (_heq := (by grind))
        (.unmap ⟨.refl, fstc_norm⟩ (.fstc ⟨.refl, hn_coup.bang.coup⟩)))
  | sndc' : (e_f : EtaFn f [⟨DCC? !(Coup(β)), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? &(⟦#(expr_to_eta β)⟧(a, b)), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.to_eta.raw &(⟦#(expr_to_eta β)⟧(a, b)))) ⟨b, (fun ⟨_, hr⟩ => by
      have h := e_h.points_norm ⟨0, e_f.arity_pos⟩ ⟨0, by simp [dcc_size, raw, Holes.v_elems, Vector.get]⟩
      change IsNorm RedAff ((expr_to_eta β).mkc a b) at h
      exact h ⟨_, .sigr hr⟩)⟩
    → Canonicalize e_f
      (.tm₁
        (f := ⟨.unmap (.sndc β), unmap_norm⟩)
        (_heq := (by grind))
        (.unmap ⟨.refl, sndc_norm⟩ (.sndc ⟨.refl, hn_coup.bang.coup⟩)))
  | par   : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨(DCC? (f' hole₁)), hn₂⟩
    → (hn  : ¬ f'.contains_hole)
    → (heq : eta_to_expr f' hn = f'')
    → (e_f' : EtaFn ⟨f'', heq ▸ hn₂.congrFun.from_eta hn⟩ [⟨α, hn_α⟩])
    → Canonicalize e_f e_f'
  | eval  : (e_f : EtaFn ⟨f, hn_f⟩ [⟨DCC? Coup(β), hn₁⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦#(expr_to_eta β)⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (#(expr_to_eta f) ⟦#(expr_to_eta β)⟧(a, b))) ⟨DCC? (f' a b), hn'⟩
    → (hn  : ¬ f'.contains_hole)
    → (heq : eta_to_expr f' hn = f'')
    → (e_f' : EtaFn ⟨f'', heq ▸ hn'.congrFun.congrFun.from_eta hn⟩ [⟨α, hn_α⟩, ⟨β, hn₁.coup⟩])
    → Canonicalize e_f (.tm₁ (_heq := by grind) (.eval (α := α) (β := β) (x := f'') ⟨.refl, hn₁.coup⟩))
  | id₂   : (e_f : EtaFn ⟨f, hn_f⟩ [⟨DCC? (Π(f_α, f_β) x_α), hnτ⟩,
              ⟨DCC? `((Π(f_α, f_β) x_α), τ'), hn_x⟩])
    → (hr_τ : RedAffNorm (DCC? (f_α x_α)) ⟨τ', hn_τ'⟩)
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩, ⟨hole₂, hn_hole₂⟩])
    → RedAffNorm (DCC? (#(expr_to_eta f) hole₁ hole₂))
      ⟨(DCC? (hole₁ hole₂)), hn_nole'⟩
    → Canonicalize e_f (.tm₂ (_heq := by grind) (.id hr_τ ⟨.refl, hnτ⟩))
  | quot₁ : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → (hr_τ : RedAffNorm (DCC? (#(expr_to_eta f) hole₁)) ⟨e', hn_e'⟩)
    → (hn_e' : ViewQuot e' → False)
    → (hn : ¬ e'.contains_hole)
    → (heq : eta_to_expr e' hn = e'')
    → Canonicalize e_f (.tm₁ (_heq := by
      cases e'
      any_goals (grind)
      case quot => exact (hn_e' .quot).elim
      case const =>
        simp [arity, raw]
        cases heq
        unfold eta_to_expr
        simp
        split <;> grind) (.quot (x := e'') ⟨.refl, hn_α⟩))
  | quot₂ : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩, ⟨DCC? `(α, β), hn_quot⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩, ⟨hole₂, hn_hole₂⟩])
    → (hr_τ : RedAffNorm (DCC? (#(expr_to_eta f) hole₁ hole₂)) ⟨e', hn_e'⟩)
    → (¬ e'.hole_mem_tm)
    → (hn : ¬ e'.contains_hole)
    → (heq : eta_to_expr e' hn = e'')
    → Canonicalize e_f (.tm₂ (_heq := by grind) (.quot (x := e'') ⟨.refl, hn_α⟩))
  | quot_bang : (e_f : EtaFn ⟨f, hn_f⟩ [⟨DCC? !(α), hn_α⟩, ⟨(DCC? !<β>), hn_β⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩, ⟨hole₂, hn_hole₂⟩])
    → (hr_τ : RedAffNorm (DCC? (#(expr_to_eta f) hole₁ hole₂)) ⟨e', hn_e'⟩)
    → (¬ e'.hole_mem_tm)
    → (hn : ¬ e'.contains_hole)
    → (heq : eta_to_expr e' hn = e'')
    → Canonicalize e_f (.tm₂ (_heq := by grind) (.curr' ⟨.refl, hn_α.bang⟩ ⟨.refl, hn_β.map⟩
      (x := (DCC? `(!(Coup(β)), e'')))
      ⟨.refl, quot_norm⟩ (.quot
      (x := e'')
      (β  := (DCC? !(Coup(β))))
      (β' := ⟨(DCC? !(Coup(β))), mk_bang_norm (mk_coup_norm hn_β.map)⟩)
      ⟨.refl, mk_bang_norm (mk_coup_norm hn_β.map)⟩)))

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
    if heq : (reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst = e_hole then
      if heq₂ : (view_fn_type? α).isNone then by
        have h := aff_sound' (DCC? (#(expr_to_eta f) e_hole))
        simp [heq] at h
        exact .some ⟨_, _, .id₁ e_f (view_fn_type?_none_sound' heq₂) h_holes h⟩
      else .none
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
        | .none => .none
    else
      if h_some : (view_quot? ((reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst)).isNone then
        if hn' : ((reduce RedAff (DCC? (#(expr_to_eta f) e_hole))).fst).contains_hole then
          .none
        else .some ⟨_, _, .quot₁ e_f h_holes (aff_sound' _) (view_quot?_none_sound' h_some) hn' rfl⟩
      else .none
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

def canonicalize₂ {f : @GenericExpr τ_c}
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
  | _ => .none

def canonicalize (e_f : EtaFn (τ_c := τ_c) ⟨f, hn⟩ doms) : Option ((f' : @NormExpr τ_c RedAff)
  × (e_f' : EtaFn f' doms) × Canonicalize e_f e_f') := by
  cases e_f with
  | tm₁ =>
    rename_i α _heq dom
    cases α with
    | mk α hn_α =>
      exact canonicalize₁ α hn_α (.tm₁ dom)
  | tm₂ =>
    rename_i α β _heq dom
    cases α with
    | mk α hn_α =>
      cases β with
      | mk β hn_β =>
        exact canonicalize₂ α hn_α β hn_β (.tm₂ dom)

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
  case h_1 heq_2 =>
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
      rename_i hrn
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
  case par =>
    expose_names
    cases h₂
    any_goals (
      focus
      try (
        cases e_f'
        expose_names
        cases h_dom
        expose_names
        have heq := hrn.ext ⟨.refl, hn_α_1⟩
        grind)
      done)
    any_goals (
      focus
      try (
        cases e_f'
        expose_names
        cases h_dom
        expose_names
        have heq := hrn.ext ⟨.refl, hn_coup.coup⟩
        grind))
    · cases e_f'
      expose_names
      cases h_dom
      expose_names
      cases hrn.elim_norm fstc_norm
      have heq := hrn.ext ⟨.refl, fstc_norm⟩
      cases a_3
      expose_names
      cases hrn_1.elim_norm hn_coup.bang.coup
      have heq := hrn_1.ext ⟨.refl, hn_coup.bang.coup⟩
      grind
    · cases e_f'
      expose_names
      cases h_dom
      expose_names
      cases hrn.elim_norm sndc_norm
      have heq := hrn.ext ⟨.refl, sndc_norm⟩
      cases a_3
      expose_names
      cases hrn_1.elim_norm hn_coup.bang.coup
      have heq := hrn_1.ext ⟨.refl, hn_coup.bang.coup⟩
      grind
    · cases e_f'
      expose_names
      cases e_f₂
      expose_names
      cases h_dom.eq h_dom_1
      rfl
    · cases e_f'
      expose_names
      cases h_dom
      expose_names
      cases hrn.elim_norm hn_α.coup
      have heq := hrn.ext ⟨.refl, hn_α.coup⟩
      grind
  case id₂ =>
    cases e_f₂
    expose_names
    cases h_dom
    expose_names
    cases a_1.elim_norm hn_τ
    have heq := a_1.ext ⟨.refl, hn_τ⟩
    have h := hr_τ.ext a_2
    grind
  case quot_bang =>
    cases e_f₂
    expose_names
    cases h_dom
    expose_names
    cases hrx.elim_norm quot_norm
    have heq  := hrx.ext ⟨.refl, quot_norm⟩
    cases hrn₁.elim_norm hn_α.bang
    have heq₂ := hrn₁.ext ⟨.refl, hn_α.bang⟩
    cases hrn₂.elim_norm (by assumption)
    have heq₃ := hrn₂.ext ⟨.refl, by assumption⟩
    simp_all
    cases a
    expose_names
    cases hrn.elim_norm (mk_bang_norm (mk_coup_norm (by assumption)))
    have heq₄ := hrn.ext ⟨.refl, mk_bang_norm (mk_coup_norm (by assumption))⟩
    grind

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
    rename_i e_f₁ _ e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f₁
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      cases heq'.left; cases heq'.right
      simp [heq]
      exact ⟨ViewFnType.complete_none (by assumption), by
        have h := (hrt.out_eq ▸ hrt).eq
        grind⟩
    · grind
  case fstc =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    rename_i h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      cases heq'.left; cases heq'.right
      have hneq : (reduce RedAff (f.1.expr_to_eta.app ((expr_to_eta β).mkc a b))).fst ≠ (expr_to_eta β).mkc a b := fun h => by
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have heq := heq.symm.trans h
        cases heq
      split
      · contradiction
      · have h : (reduce RedAff (f.1.expr_to_eta.app ((expr_to_eta β).mkc a b))).fst.hole_mem_tm = true := by
          cases e_h
          rename_i e_h
          have h := e_h.sigl_hole_mem_tm
          rw [← heq] at h
          exact h
        split
        case isTrue =>
          split
          case h_1 heq₁ =>
            exact (canonicalize₁_par_some₁ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
          · dsimp
            simp [view_coup_bang?]
            have h : (reduce RedAff (f.1.expr_to_eta.app ((expr_to_eta β).mkc a b))).fst = a := heq
            simp [h]
            split
            simp
            let ha := (hrt.out_eq ▸ hrt).eq
            rename_i a b
            let hb := ((RedAffNorm.mk a b).out_eq ▸ (RedAffNorm.mk a b)).eq
            have he := ha.trans hb.symm
            grind
        ·   rename_i hn
            exact (hn h).elim
    · grind
  case sndc =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    rename_i h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      cases heq'.left; cases heq'.right
      have hneq : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b))).fst ≠ β.expr_to_eta.mkc a b := fun h => by
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have heq := heq.symm.trans h
        cases heq
      split
      · contradiction
      case isFalse =>
        have h : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b))).fst.hole_mem_tm = true := by
          cases e_h
          rename_i e_h
          have h := e_h.sigr_hole_mem_tm
          rw [← heq] at h
          --simp [raw, Holes.v_elems, Vector.mk, get, hole_mem_tm, Vector.get] at h
          exact h
        split
        case isTrue =>
          dsimp
          simp [view_coup_bang?]
          have hn : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b))).fst = b := heq
          simp [hn]
          split
          case h_1 heq₁ =>
            exact (canonicalize₁_par_some₂ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
          · split
            · have h := (hrt.out_eq ▸ hrt).eq
              have hnnn : a ≠ b :=
                match e_h with
                | .tm₁ heq h => by cases heq; exact h.coup_points_neq
              grind
            · split
              have h := (hrt.out_eq ▸ hrt).eq
              simp
              rename_i x hr hn
              have hrt' := RedAffNorm.mk hr hn
              have hh := (hrt'.out_eq ▸ hrt').eq
              have he := h.trans hh.symm
              grind
        · contradiction
    · grind
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
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      cases heq'.left; cases heq'.right
      rename_i e_hole hn_hole h_holes
      have hneq : (reduce RedAff (f.expr_to_eta.app (βt.expr_to_eta.mkc a₁ b))).fst ≠ βt.expr_to_eta.mkc a₁ b := fun h => by
        grind
      simp [hneq]
      have h_hole : (reduce RedAff (f.expr_to_eta.app (βt.expr_to_eta.mkc a₁ b))).fst.hole_mem_tm := by
        cases e_h
        rename_i e_h
        have h := e_h.sigl_hole_mem_tm
        grind
      simp [h_hole, view_coup_bang?]
      simp [heq]
      have hneq'a : (f'.app a₁).app b ≠ a₁ := fun heq => by
        cases heq
      have hneq'b : (f'.app a₁).app b ≠ b := fun heq => by
        cases heq
      simp [hneq'a, hneq'b]
      split
      case h_1 heq_par =>
        exact (canonicalize₁_par_some₅ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
      · split
        case h_1 =>
          rename_i f'_raw a' b' hr' heq_match
          have heq''a : a' = a₁ := by grind
          subst heq''a
          have heq''b : b' = b := by grind
          subst heq''b
          have heq_whole : f'_raw = f' := by grind
          subst heq_whole
          have h_comp := e_f'.complete
          simp [hn_mem]
          cases heq_eta
          simp [h_comp]
          have h := (hrt.out_eq ▸ hrt).eq
          have hrt' := RedAffNorm.mk hr' hn'
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
            rw [h_red] at h
            exact h
          subst h_fst
          exact (heq_catchall f' a₁ b hr h_red).elim
    ·   grind
  case fstc' =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      rename_i e_hole hn_hole h_holes
      simp at heq'
      cases heq'.left; cases heq'.right
      have hneq : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst ≠ (β.expr_to_eta.mkc a b).box := fun h => by
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have heq := heq.symm.trans h
        cases heq
      simp [hneq]
      have h : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst.hole_mem_tm := by
        cases e_h
        rename_i e_h
        have h := e_h.sigl_hole_mem_tm_box
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have h := heq.symm ▸ h
        exact h
      simp [h]
      simp [raw] at heq
      simp [view_coup_bang?]
      have heq' : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst = a := by
        unfold NormExpr.to_eta at heq
        exact heq
      simp [heq']
      split
      case h_1 heq_par =>
        exact (canonicalize₁_par_some₃ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
      · split
        simp
        have h := (hrt.out_eq ▸ hrt).eq
        rename_i x hr hn
        have hrt' := RedAffNorm.mk hr hn
        have hh   := (hrt'.out_eq ▸ hrt').eq
        have he   := h.trans hh.symm
        grind
    ·   grind
  case sndc' =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      rename_i e_hole hn_hole h_holes
      simp at heq'
      cases heq'.left; cases heq'.right
      have hneq : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst ≠ (β.expr_to_eta.mkc a b).box := fun h => by
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have heq := heq.symm.trans h
        cases heq
      simp [hneq]
      have h : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst.hole_mem_tm := by
        cases e_h
        rename_i e_h
        have h := e_h.sigr_hole_mem_tm_box
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have h := heq.symm ▸ h
        exact h
      simp [h]
      simp [raw] at heq
      simp [view_coup_bang?]
      have heq' : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst = b := by
        unfold NormExpr.to_eta at heq
        exact heq
      simp [heq']
      split
      case h_1 par_eq =>
        exact (canonicalize₁_par_some₄ (Option.isSome_iff_exists.mpr ⟨_, by assumption⟩) heq).elim
      · split
        · split
          · simp
            have h := (hrt.out_eq ▸ hrt).eq
            have hnnn : a ≠ b :=
              match e_h with
              | .tm₁ heq h => by cases heq; exact h.bang_coup_points_neq
            grind
        · split
          · simp
            have h := (hrt.out_eq ▸ hrt).eq
            rename_i x hr hn
            have hrt' := RedAffNorm.mk hr hn
            have hh   := (hrt'.out_eq ▸ hrt').eq
            have he   := h.trans hh.symm
            grind
    ·   grind
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
        have heq_3 : f'_2.app e_hole' = f'.app hole₁ := by
          grind
        have heq_4 : hole₁ = e_hole' := by grind
        have heq_6 : f'_2 = f' := by grind
        have h := heq_6 ▸ hn_mem
        have heq_fn := e_f'.complete
        have heq_7 : f'_2.contains_hole = false := by grind
        cases heq_6
        cases heq_4
        simp [h]
        split
        case h_1 =>
          expose_names
          have heq : (f'.eta_to_expr
          (of_eq_true
            (Eq.trans (congrArg Not (Eq.trans (congrFun' (congrArg Eq (Bool.of_not_eq_true h)) true) Bool.false_eq_true))
              not_false_eq_true))) = e_f := by
              grind
          have ha := e_f'_2.complete
          have hb := e_f'.complete
          split
          case isTrue =>
            aesop
          case isFalse =>
            simp [heq] at e_f'_2
            have ha := e_f'.arity_eq
            have hb := e_f'_2.arity_eq
            cases e_f'_2 with
            | tm₁ h_dom₂ =>
              cases e_f' with
              | tm₁ h_dom₃ =>
                cases h_dom₂.unique h_dom₃
                grind
            | tm₂ h_dom₂ =>
              simp_all [arity]
        case h_2 => aesop
      case h_2 x =>
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
      rw [h_heq]
      split
      case h_1 heq' =>
        simp at heq'
        expose_names
        have hneq : (reduce RedAff (f_1.expr_to_eta.app hole₁)).fst ≠ hole₁ := by
          intro h
          simp at heq
          rw [heq] at h
          cases h
        have hneq' : ((reduce RedAff (f_1.expr_to_eta.app hole₁)).fst ≠ e_hole) := by
          grind
        split
        · grind
        case isFalse hn =>
          have h_mem : (reduce RedAff (f_1.expr_to_eta.app e_hole)).fst.hole_mem_tm := by
            cases heq'.left
            rw [heq]
            have h := match e_h with | .tm₁ _ h => h.hole_mem_tm
            grind
          split
          case isTrue =>
            split
            · expose_names
              simp [canonicalize₁_par?] at heq_1
              split at heq_1
              case h_1 f'' e_hole' _ heq'' =>
                have heq_fst : f'.app hole₁ = f''.app e_hole' := by grind
                cases heq'.left; cases heq'.right
                have heq_hole : hole₁ = e_hole' := by grind
                have heq_f : f' = f'' := by grind
                cases heq_hole
                cases heq_f
                simp [hn_mem] at heq_1
                have ha := e_f'.complete
                split at heq_1
                · expose_names
                  have h := e_f'_2.complete
                  aesop
                · grind
              · grind
            · cases e_h.unique h_holes
              have ha := e_h.complete
              have hb := h_holes.complete
              have heq'' : e_h = h_holes := by grind
              aesop
          · grind
      · grind
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
    rw [h_heq]
    split
    case h_1 heq' =>
      rename_i e_hole hn_hole e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      expose_names
      have h_mem_hole : hole₁.hole_mem_tm := by
        cases e_h
        rename_i e_h
        exact e_h.hole_mem_tm
      have hn : (reduce RedAff (f_1.expr_to_eta.app hole₁)).fst ≠ hole₁ := fun h => by
        have h := heq.symm.trans h
        cases h
        have h := e_h.contains_hole₁
        grind
      split
      · grind
      case isFalse =>
        split
        · rename_i h_mem
          have h_mem' := heq ▸ h_mem
          have h := mem_imp_contains_hole (τ_c := τ_c) (e := e') (heq ▸ h_mem)
          grind
        · simp [heq.symm ▸ ViewQuot.complete_none hn_e'_1]
          have h := (hr_τ.out_eq ▸ hr_τ).eq
          simp_all
          aesop
    · grind
  case quot_bang =>
    expose_names
    have heq := hr_τ.complete_fst
    have heq_whole := hr_τ.complete
    have h_heq := e_h.complete
    cases e_f_1
    simp [canonicalize]
    unfold canonicalize₂
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      rename_i e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      expose_names
      have h_contains : (reduce RedAff ((f_1.expr_to_eta.app hole₁).app hole₂)).fst.hole_mem_tm ≠ true := fun h => by
        have h := heq ▸ h
        grind
      split
      · grind
      · simp
        have h := (hr_τ.out_eq ▸ hr_τ).eq
        simp_all
        aesop
    · grind
  case quot₂ =>
    expose_names
    have heq := hr_τ.complete_fst
    have heq_whole := hr_τ.complete
    have h_heq := e_h.complete
    cases e_f_1
    simp [canonicalize]
    unfold canonicalize₂
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      rename_i e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      expose_names
      have h_contains : (reduce RedAff ((f_1.expr_to_eta.app hole₁).app hole₂)).fst.hole_mem_tm ≠ true := fun h => by
        have h := heq ▸ h
        grind
      split
      · grind
      · simp
        have h := (hr_τ.out_eq ▸ hr_τ).eq
        simp_all
        aesop
    · grind
  case id₂ =>
    expose_names
    have heq := hr_τ.complete_fst
    have heqb := a.complete_fst
    have heq_whole := hr_τ.complete
    have heq_whole' := a.complete
    have h_heq := e_h.complete
    cases e_f_1
    simp [canonicalize]
    unfold canonicalize₂
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      rename_i e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      expose_names
      have h_mem₁ : hole₁.hole_mem_tm :=
        match e_h with
        | .tm₂ heq h _ _ => by cases heq; exact h.hole_mem_tm
      have h_mem : (reduce RedAff ((f_1.expr_to_eta.app hole₁).app hole₂)).fst.hole_mem_tm = true := by
        grind
      split
      case isTrue =>
        split
        case h_1 =>
          rename_i hole₃ hole₄ hr' heq'
          have heq_hole₁ : hole₃ = hole₁ := by grind
          have heq_hole₂ : hole₄ = hole₂ := by grind
          subst heq_hole₁
          subst heq_hole₂
          subst heq
          rename_i heq'
          subst heq'
          --cases heqb
          --subst heqb
          have h    := (hr_τ.out_eq ▸ hr_τ).eq
          have hrt' := RedAffNorm.mk hr' (by assumption)
          have hh   := (a.out_eq ▸ a).eq
          simp only
          simp_all
          constructor
          · simp [aff_sound, aff_sound']
            try grind
          · grind
        case h_2 x =>
          generalize h_red : reduce RedAff ((f_1.expr_to_eta.app hole₁).app hole₂) = res
          cases res
          rename_i fst snd
          cases snd
          rename_i hr
          have h_fst : fst = hole₁.app hole₂ := by
            grind
          subst h_fst
          exact (x hole₁ hole₂ (match a with | ⟨a, _⟩ => a) h_red).elim
      · grind
    · grind

/-set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 9999 in
set_option pp.proofs true in
set_option pp.proofs.threshold 9999 in
set_option maxHeartbeats 100000000000 in
def Canonicalize.complete {f f' : @NormExpr τ_c RedAff}
  {e_f : EtaFn f doms}
  {e_f' : EtaFn f' doms}
  (h : Canonicalize e_f e_f') : canonicalize e_f = .some ⟨f', e_f', h⟩ := by
  induction h with
  | id₁ =>
    rename_i e_f₁ _ e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f₁
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      cases heq'.left; cases heq'.right
      simp [heq]
      exact ⟨ViewFnType.complete_none (by assumption), by
        have h := (hrt.out_eq ▸ hrt).eq
        grind⟩
    · grind
  | fstc =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    rename_i h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      cases heq'.left; cases heq'.right
      have hneq : (reduce RedAff (f.1.expr_to_eta.app ((expr_to_eta β).mkc a b))).fst ≠ (expr_to_eta β).mkc a b := fun h => by
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have heq := heq.symm.trans h
        cases heq
      split
      · contradiction
      · have h : (reduce RedAff (f.1.expr_to_eta.app ((expr_to_eta β).mkc a b))).fst.hole_mem_tm = true := by
          cases e_h
          rename_i e_h
          have h := e_h.sigl_hole_mem_tm
          rw [← heq] at h
          exact h
        split
        case isTrue =>
          dsimp
          simp [view_coup_bang?]
          have h : (reduce RedAff (f.1.expr_to_eta.app ((expr_to_eta β).mkc a b))).fst = a := heq
          simp [h]
          split
          simp
          let ha := (hrt.out_eq ▸ hrt).eq
          rename_i a b
          let hb := ((RedAffNorm.mk a b).out_eq ▸ (RedAffNorm.mk a b)).eq
          have he := ha.trans hb.symm
          grind
        · rename_i hn
          exact (hn h).elim
    · grind
  | sndc =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    rename_i h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      cases heq'.left; cases heq'.right
      have hneq : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b))).fst ≠ β.expr_to_eta.mkc a b := fun h => by
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have heq := heq.symm.trans h
        cases heq
      split
      · contradiction
      case isFalse =>
        have h : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b))).fst.hole_mem_tm = true := by
          cases e_h
          rename_i e_h
          have h := e_h.sigr_hole_mem_tm
          rw [← heq] at h
          --simp [raw, Holes.v_elems, Vector.mk, get, hole_mem_tm, Vector.get] at h
          exact h
        split
        case isTrue =>
          dsimp
          simp [view_coup_bang?]
          have hn : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b))).fst = b := heq
          simp [hn]
          split
          · split
            have h := (hrt.out_eq ▸ hrt).eq
            simp
            rename_i x hr hn
            have hrt' := RedAffNorm.mk hr hn
            have hh := (hrt'.out_eq ▸ hrt').eq
            have he := h.trans hh.symm
            have hnnn : a ≠ b :=
              match e_h with
              | .tm₁ heq h => by cases heq; exact h.coup_points_neq
            grind
          · split
            have h := (hrt.out_eq ▸ hrt).eq
            simp
            rename_i x hr hn
            have hrt' := RedAffNorm.mk hr hn
            have hh := (hrt'.out_eq ▸ hrt').eq
            have he := h.trans hh.symm
            grind
        · contradiction
    · grind
  | eval =>
    rename_i f hn_f βt ahn₁ a₁ b hn_hole₁ f' hn' _ α hn_α e_f e_h hrt hn_mem heq_eta e_f'
    have heq := hrt.complete_fst
    have heq₀ := hrt.complete_snd
    have h_heq := e_h.complete
    cases e_f
    rename_i _heq h_dom
    have h_dom_eq := h_dom.complete
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      cases heq'.left; cases heq'.right
      rename_i e_hole hn_hole h_holes
      have hneq : (reduce RedAff (f.expr_to_eta.app (βt.expr_to_eta.mkc a₁ b))).fst ≠ βt.expr_to_eta.mkc a₁ b := fun h => by
        grind
      simp [hneq]
      have h_hole : (reduce RedAff (f.expr_to_eta.app (βt.expr_to_eta.mkc a₁ b))).fst.hole_mem_tm := by
        cases e_h
        rename_i e_h
        have h := e_h.sigl_hole_mem_tm
        grind
      simp [h_hole, view_coup_bang?]
      simp [heq]
      have hneq'a : (f'.app a₁).app b ≠ a₁ := fun heq => by
        cases heq
      have hneq'b : (f'.app a₁).app b ≠ b := fun heq => by
        cases heq
      simp [hneq'a, hneq'b]
      split
      case h_1 =>
        rename_i f'_raw a' b' hr' heq_match
        have heq''a : a' = a₁ := by grind
        subst heq''a
        have heq''b : b' = b := by grind
        subst heq''b
        have heq_whole : f'_raw = f' := by grind
        subst heq_whole
        have h_comp := e_f'.complete
        simp [hn_mem]
        cases heq_eta
        simp [h_comp]
        have h := (hrt.out_eq ▸ hrt).eq
        have hrt' := RedAffNorm.mk hr' hn'
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
          rw [h_red] at h
          exact h
        subst h_fst
        exact (heq_catchall f' a₁ b hr h_red).elim
    · grind
  | fstc' =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      rename_i e_hole hn_hole h_holes
      simp at heq'
      cases heq'.left; cases heq'.right
      have hneq : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst ≠ (β.expr_to_eta.mkc a b).box := fun h => by
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have heq := heq.symm.trans h
        cases heq
      simp [hneq]
      have h : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst.hole_mem_tm := by
        cases e_h
        rename_i e_h
        have h := e_h.sigl_hole_mem_tm_box
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have h := heq.symm ▸ h
        exact h
      simp [h]
      simp [raw] at heq
      simp [view_coup_bang?]
      have heq' : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst = a := by
        unfold NormExpr.to_eta at heq
        exact heq
      simp [heq']
      split
      simp
      have h := (hrt.out_eq ▸ hrt).eq
      rename_i x hr hn
      have hrt' := RedAffNorm.mk hr hn
      have hh   := (hrt'.out_eq ▸ hrt').eq
      have he   := h.trans hh.symm
      grind
    · grind
  | sndc' =>
    rename_i f β hn_coup a b hn_coup e_f e_h hrt
    have heq := hrt.complete_fst
    have h_heq := e_h.complete
    cases e_f
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      rename_i e_hole hn_hole h_holes
      simp at heq'
      cases heq'.left; cases heq'.right
      have hneq : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst ≠ (β.expr_to_eta.mkc a b).box := fun h => by
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have heq := heq.symm.trans h
        cases heq
      simp [hneq]
      have h : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst.hole_mem_tm := by
        cases e_h
        rename_i e_h
        have h := e_h.sigr_hole_mem_tm_box
        simp [raw] at heq
        unfold NormExpr.to_eta at heq
        simp at heq
        have h := heq.symm ▸ h
        exact h
      simp [h]
      simp [raw] at heq
      simp [view_coup_bang?]
      have heq' : (reduce RedAff (f.1.expr_to_eta.app (β.expr_to_eta.mkc a b).box)).fst = b := by
        unfold NormExpr.to_eta at heq
        exact heq
      simp [heq']
      split
      · split
        · simp
          have h := (hrt.out_eq ▸ hrt).eq
          have hnnn : a ≠ b :=
            match e_h with
            | .tm₁ heq h => by cases heq; exact h.bang_coup_points_neq
          grind
      · split
        · simp
          have h := (hrt.out_eq ▸ hrt).eq
          rename_i x hr hn
          have hrt' := RedAffNorm.mk hr hn
          have hh   := (hrt'.out_eq ▸ hrt').eq
          have he   := h.trans hh.symm
          grind
    · grind
  | par =>
    rename_i f' hn₂ e_f h_view e_h hrt hn_mem heq_eta e_f'
    have h := ViewCoupBang.complete_none h_view
    have heq := hrt.complete_fst
    have heq_whole := hrt.complete
    have h_heq := e_h.complete
    cases e_f
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      expose_names
      have hneq : (reduce RedAff (f_1.expr_to_eta.app hole₁)).fst ≠ hole₁ := by
        intro h
        simp at heq
        rw [heq] at h
        cases h
      have hneq' : ((reduce RedAff (f_1.expr_to_eta.app hole₁)).fst ≠ e_hole) := by
        grind
      split
      · grind
      case isFalse hn =>
        have h : hole_mem_tm hole₁ := by
          cases e_h
          rename_i e_h
          exact e_h.hole_mem_tm
        have h_mem : (reduce RedAff (f_1.expr_to_eta.app hole₁)).fst.hole_mem_tm = true := by
          simp_all [hole_mem_tm]
        split
        case isTrue =>
          rename_i hn_view _
          split
          · grind
          case h_2 =>
            cases heq'.left
            split
            case h_1 =>
              rename_i f'' e_hole' _ _
              have h_hole_eq : e_hole' = hole₁ := by
                grind
              have h_f'_eq : f'' = f'_2 := by
                grind
              subst h_hole_eq
              cases h_f'_eq
              cases heq_eta
              have h_view_f' := e_f'.complete
              simp [h_view_f']
              have h := (hrt.out_eq ▸ hrt).eq
              constructor
              · simp_all
              · rename_i hr' _
                have hrt' := RedAffNorm.mk hr' f'
                have hh   := (hrt'.out_eq ▸ hrt').eq
                have he   := h.trans hh.symm
                grind
            case h_2 x =>
              generalize h_red : reduce RedAff (f_1.expr_to_eta.app hole₁) = res
              cases res
              rename_i fst snd
              cases snd
              rename_i hr
              have h_fst : fst = f'_2.app hole₁ := by
                grind
              subst h_fst
              exact (x f'_2 hole₁ (match hrt with | ⟨a, _⟩ => a) h_red).elim
        · cases heq'.left
          grind
    · grind
  | quot₁ =>
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
    rw [h_heq]
    split
    case h_1 heq' =>
      rename_i e_hole hn_hole e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      expose_names
      have h_mem_hole : hole₁.hole_mem_tm := by
        cases e_h
        rename_i e_h
        exact e_h.hole_mem_tm
      have hn : (reduce RedAff (f_1.expr_to_eta.app hole₁)).fst ≠ hole₁ := fun h => by
        have h := heq.symm.trans h
        cases h
        have h := e_h.contains_hole₁
        grind
      split
      · grind
      case isFalse =>
        split
        · rename_i h_mem
          have h_mem' := heq ▸ h_mem
          have h := mem_imp_contains_hole (τ_c := τ_c) (e := e') (heq ▸ h_mem)
          grind
        · simp [heq.symm ▸ ViewQuot.complete_none hn_e'_1]
          have h := (hr_τ.out_eq ▸ hr_τ).eq
          simp_all
          aesop
    · grind
  | quot_bang =>
    expose_names
    have heq := hr_τ.complete_fst
    have heq_whole := hr_τ.complete
    have h_heq := e_h.complete
    cases e_f_1
    simp [canonicalize]
    unfold canonicalize₂
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      rename_i e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      expose_names
      have h_contains : (reduce RedAff ((f_1.expr_to_eta.app hole₁).app hole₂)).fst.hole_mem_tm ≠ true := fun h => by
        have h := heq ▸ h
        grind
      split
      · grind
      · simp
        have h := (hr_τ.out_eq ▸ hr_τ).eq
        simp_all
        aesop
    · grind
  | quot₂ =>
    expose_names
    have heq := hr_τ.complete_fst
    have heq_whole := hr_τ.complete
    have h_heq := e_h.complete
    cases e_f_1
    simp [canonicalize]
    unfold canonicalize₂
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      rename_i e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      expose_names
      have h_contains : (reduce RedAff ((f_1.expr_to_eta.app hole₁).app hole₂)).fst.hole_mem_tm ≠ true := fun h => by
        have h := heq ▸ h
        grind
      split
      · grind
      · simp
        have h := (hr_τ.out_eq ▸ hr_τ).eq
        simp_all
        aesop
    · grind
  | id₂ =>
    expose_names
    have heq := hr_τ.complete_fst
    have heqb := a.complete_fst
    have heq_whole := hr_τ.complete
    have heq_whole' := a.complete
    have h_heq := e_h.complete
    cases e_f_1
    simp [canonicalize]
    unfold canonicalize₂
    rw [h_heq]
    split
    case h_1 heq' =>
      simp at heq'
      rename_i e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      expose_names
      have h_mem₁ : hole₁.hole_mem_tm :=
        match e_h with
        | .tm₂ heq h _ _ => by cases heq; exact h.hole_mem_tm
      have h_mem : (reduce RedAff ((f_1.expr_to_eta.app hole₁).app hole₂)).fst.hole_mem_tm = true := by
        grind
      split
      case isTrue =>
        split
        case h_1 =>
          rename_i hole₃ hole₄ hr' heq'
          have heq_hole₁ : hole₃ = hole₁ := by grind
          have heq_hole₂ : hole₄ = hole₂ := by grind
          subst heq_hole₁
          subst heq_hole₂
          subst heq
          rename_i heq'
          subst heq'
          --cases heqb
          --subst heqb
          have h    := (hr_τ.out_eq ▸ hr_τ).eq
          have hrt' := RedAffNorm.mk hr' (by assumption)
          have hh   := (a.out_eq ▸ a).eq
          simp only
          simp_all
          constructor
          · simp [aff_sound, aff_sound']
            try grind
          · grind
        case h_2 x =>
          generalize h_red : reduce RedAff ((f_1.expr_to_eta.app hole₁).app hole₂) = res
          cases res
          rename_i fst snd
          cases snd
          rename_i hr
          have h_fst : fst = hole₁.app hole₂ := by
            grind
          subst h_fst
          exact (x hole₁ hole₂ (match a with | ⟨a, _⟩ => a) h_red).elim
      · grind
    · grind-/

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
