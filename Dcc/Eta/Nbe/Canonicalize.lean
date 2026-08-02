import Dcc.Eta.Nbe.Hole

namespace NormExpr

variable {τ_c : Type u}
variable [DecidableEq τ_c]

namespace EtaFn

open GenericExpr

inductive Canonicalize : (e_f : EtaFn (τ_c := τ_c) f doms)
  → (e_f' : EtaFn (τ_c := τ_c) f' doms)
  → Type u
  | id₁   : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (n_pi_α : ViewFnType α → False)
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → RedAffNorm (DCC? (f hole₁)) ⟨hole₁, hn_hole₁⟩
    → Canonicalize e_f (.tm₁ (_heq := (by
      simp [raw, arity]
      cases α
      any_goals (grind)
      case app f x =>
        cases f
        any_goals (grind)
        case pi =>
          exact (n_pi_α .pi).elim)) (.id ⟨.refl, hn_α⟩))
  | fstc  : (e_f : EtaFn f [⟨DCC? Coup(β), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦β⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.raw ⟦β⟧(a, b))) ⟨a, hn_hole₁.sigl⟩
    → Canonicalize e_f (.tm₁ (_heq := (by grind)) (.fstc ⟨.refl, hn_coup.coup⟩))
  | sndc  : (e_f : EtaFn f [⟨DCC? Coup(β), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦β⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.raw ⟦β⟧(a, b))) ⟨b, hn_hole₁.sigr⟩
    → Canonicalize e_f (.tm₁ (_heq := (by grind)) (.sndc ⟨.refl, hn_coup.coup⟩))
  | fstc' : (e_f : EtaFn f [⟨DCC? !(Coup(β)), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? &(⟦β⟧(a, b)), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.raw &(⟦β⟧(a, b)))) ⟨a, (fun ⟨_, hr⟩ => by
      have h := e_h.points_norm ⟨0, e_f.arity_pos⟩ ⟨0, by simp [dcc_size, raw, Holes.v_elems, Vector.get]⟩
      change IsNorm RedAff (β.mkc a b) at h
      exact h ⟨_, .sigl hr⟩)⟩
    → Canonicalize e_f
      (.tm₁
        (f := ⟨.unmap (.fstc β), fun ⟨_, h⟩ => nomatch h⟩)
        (_heq := (by grind))
        (.unmap ⟨.refl, fun ⟨_, h⟩ => nomatch h⟩ (.fstc ⟨.refl, fun ⟨_, h⟩ => hn_coup ⟨_, .bang (.coup h)⟩⟩)))
  | sndc' : (e_f : EtaFn f [⟨DCC? !(Coup(β)), hn_coup⟩])
    → (e_h : Holes e_f 0 [⟨DCC? &(⟦β⟧(a, b)), hn_hole₁⟩])
    → RedAffNorm (DCC? (f.raw &(⟦β⟧(a, b)))) ⟨b, (fun ⟨_, hr⟩ => by
      have h := e_h.points_norm ⟨0, e_f.arity_pos⟩ ⟨0, by simp [dcc_size, raw, Holes.v_elems, Vector.get]⟩
      change IsNorm RedAff (β.mkc a b) at h
      exact h ⟨_, .sigr hr⟩)⟩
    → Canonicalize e_f
      (.tm₁
        (f := ⟨.unmap (.sndc β), fun ⟨_, h⟩ => nomatch h⟩)
        (_heq := (by grind))
        (.unmap ⟨.refl, fun ⟨_, h⟩ => nomatch h⟩ (.sndc ⟨.refl, fun ⟨_, h⟩ => hn_coup ⟨_, .bang (.coup h)⟩⟩)))
  | par   : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (α.ViewCoupBang → False)
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → RedAffNorm (DCC? (f hole₁)) ⟨(DCC? (f' hole₁)), hn₂⟩
    → (e_f' : EtaFn ⟨f', hn₂.congrFun⟩ [⟨α, hn_α⟩])
    → Canonicalize e_f e_f'
  | eval  : (e_f : EtaFn ⟨f, hn_f⟩ [⟨DCC? Coup(β), hn₁⟩])
    → (e_h : Holes e_f 0 [⟨DCC? ⟦β⟧(a, b), hn_hole₁⟩])
    → RedAffNorm (DCC? (f ⟦β⟧(a, b))) ⟨DCC? (f' a b), hn'⟩
    → (e_f' : EtaFn ⟨f', hn'.congrFun.congrFun⟩ [⟨α, hn_α⟩, ⟨β, hn₁.coup⟩])
    → Canonicalize e_f (.tm₁ (_heq := by grind) (.eval (α := α) (β := β) (x := f') ⟨.refl, hn₁.coup⟩))
  | id₂   : (e_f : EtaFn ⟨f, hn_f⟩ [⟨DCC? (Π(f_α, f_β) x_α), hnτ⟩,
              ⟨DCC? `((Π(f_α, f_β) x_α), τ'), hn_x⟩])
    → (hr_τ : RedAffNorm (DCC? (f_α x_α)) ⟨τ', hn_τ'⟩)
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩, ⟨hole₂, hn_hole₂⟩])
    → RedAffNorm (DCC? (f hole₁ hole₂))
      ⟨(DCC? (hole₁ hole₂)), hn_nole'⟩
    → Canonicalize e_f (.tm₂ (_heq := by grind) (.id hr_τ ⟨.refl, hnτ⟩))
  | quot₁ : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩])
    → (hr_τ : RedAffNorm (DCC? (f hole₁)) ⟨e', hn_e'⟩)
    → (hn_e' : ViewQuot e' → False)
    → (¬ e'.hole_mem_tm)
    → Canonicalize e_f (.tm₁ (_heq := by
      cases e'
      any_goals (grind)
      case quot => exact (hn_e' .quot).elim) (.quot (x := e') ⟨.refl, hn_α⟩))
  | quot₂ : (e_f : EtaFn ⟨f, hn_f⟩ [⟨α, hn_α⟩, ⟨DCC? `(α, β), hn_quot⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩, ⟨hole₂, hn_hole₂⟩])
    → (hr_τ : RedAffNorm (DCC? (f hole₁ hole₂)) ⟨e', hn_e'⟩)
    → (¬ e'.hole_mem_tm)
    → Canonicalize e_f (.tm₂ (_heq := by grind) (.quot (x := e') ⟨.refl, hn_α⟩))
  | quot_bang : (e_f : EtaFn ⟨f, hn_f⟩ [⟨DCC? !(α), hn_α⟩, ⟨(DCC? !<β>), hn_β⟩])
    → (e_h : Holes e_f 0 [⟨hole₁, hn_hole₁⟩, ⟨hole₂, hn_hole₂⟩])
    → (hr_τ : RedAffNorm (DCC? (f hole₁ hole₂)) ⟨e', hn_e'⟩)
    → (¬ e'.hole_mem_tm)
    → Canonicalize e_f (.tm₂ (_heq := by grind) (.curr' ⟨.refl, fun ⟨_, h⟩ => hn_α ⟨_, .bang h⟩⟩ ⟨.refl, fun ⟨_, h⟩ => hn_β ⟨_, .map₀ h⟩⟩
      (x := (DCC? `(!(Coup(β)), e')))
      ⟨.refl, fun ⟨_, h⟩ => nomatch h⟩ (.quot
      (x := e')
      (β  := (DCC? !(Coup(β))))
      (β' := ⟨(DCC? !(Coup(β))), fun ⟨_, h⟩ => match h with | .bang (.coup h) => hn_β ⟨_, .map₀ h⟩⟩)
      ⟨.refl, fun ⟨_, h⟩ => match h with | .bang (.coup h) => hn_β ⟨_, .map₀ h⟩⟩)))

def canonicalize₁ {f : GenericExpr (@EtaConst τ_c)}
  {hn : IsNorm RedAff f}
  (α : GenericExpr EtaConst) (hn_α : IsNorm RedAff α) (e_f : EtaFn ⟨f, hn⟩ [mk α hn_α]) :
  Option ((f' : @EtaExpr.Norm τ_c) × (e_f' : EtaFn f' [mk α hn_α]) × e_f.Canonicalize e_f') :=
  match e_f.holes 0 with
  | .some ⟨[⟨e_hole, hn_hole⟩], h_holes⟩ =>
    if heq : (reduce RedAff (DCC? (f e_hole))).fst = e_hole then
      if heq₂ : (view_fn_type? α).isNone then by
        have h := aff_sound' (DCC? (f e_hole))
        simp [heq] at h
        exact .some ⟨_, _, .id₁ e_f (view_fn_type?_none_sound' heq₂) h_holes h⟩
      else .none
    else if h_contains : ((reduce RedAff (DCC? (f e_hole))).fst).hole_mem_tm then
      match heq_some : α.view_coup_bang? with
      | .some h => by
        cases h with
        | coup =>
          rename_i β
          match e_hole with
          | DCC? ⟦β₂⟧(a, b) =>
            if heqc : β₂ = β then
              if heqa : (reduce RedAff (DCC? (f ⟦β⟧(a, b)))).fst = a then
                have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                cases heqc
                exact .some ⟨_, _, .fstc e_f h_holes ⟨hr, hn⟩⟩
              else if heqa : (reduce RedAff (DCC? (f ⟦β⟧(a, b)))).fst = b then
                have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                cases heqc
                exact .some ⟨_, _, .sndc e_f h_holes ⟨hr, hn⟩⟩
              else
                match h_app_eq : (reduce RedAff (DCC? (f ⟦β⟧(a, b)))) with
                | ⟨DCC? (f' a' b'), ⟨hr⟩⟩ =>
                  have hn' := reduce_norm h_app_eq
                  if heqa : a' = a then
                    if heqb : b' = b then
                      let f' : EtaExpr.Norm := ⟨f', hn'.congrFun.congrFun⟩
                      match f'.view_eta_fn with
                      | .some ⟨doms, e_f'⟩ =>
                        match doms with
                        | [α, ⟨β', hn⟩] =>
                          if heq_β' : β' = β then
                            cases heq_β'; cases heqc; cases heqa; cases heqb
                            exact .some ⟨_, _, .eval e_f h_holes ⟨hr, hn'⟩ e_f'⟩
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
            if heqc : β₂ = β then
              if heqa : (reduce RedAff (DCC? (f &(⟦β⟧(a, b))))).fst = a then
                have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                cases heqc
                exact .some ⟨_, _, .fstc' e_f h_holes ⟨hr, hn⟩⟩
              else if heqa : (reduce RedAff (DCC? (f &(⟦β⟧(a, b))))).fst = b then
                have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
                cases heqc
                exact .some ⟨_, _, .sndc' e_f h_holes ⟨hr, hn⟩⟩
              else exact .none
            else exact .none
          | _ => exact .none
      | .none =>
        match h_red_eq : (reduce RedAff (DCC? (f e_hole))) with
        | ⟨DCC? (f' e_hole'), ⟨hr⟩⟩ =>
          have hn' := reduce_norm h_red_eq
          if h_hole_eq : e_hole' = e_hole then
            match view_eta_fn ⟨f', hn'.congrFun⟩ with
            | .some ⟨doms', e_fn'⟩ => by
              if heq_doms : doms' = [mk α hn_α] then
                cases heq_doms
                cases h_hole_eq
                exact .some ⟨_, _, .par e_f (view_coup_bang?_none_sound' (by grind)) h_holes ⟨hr, hn'⟩ e_fn'⟩
              else exact .none
            | _ => .none
          else .none
        | _ => .none
    else
      if h_some : (view_quot? ((reduce RedAff (DCC? (f e_hole))).fst)).isNone then
        .some ⟨_, _, .quot₁ e_f h_holes (aff_sound' _) (view_quot?_none_sound' h_some) h_contains⟩
      else .none
  | _ => .none

/-def canonicalize₁ {f : GenericExpr (@EtaConst τ_c)}
  {hn : IsNorm RedAff f}
  (α : GenericExpr EtaConst) (hn_α : IsNorm RedAff α) (e_f : EtaFn ⟨f, hn⟩ [mk α hn_α]) :
  Option ((f' : @EtaExpr.Norm τ_c) × (e_f' : EtaFn f' [mk α hn_α]) × e_f.Canonicalize e_f') :=
  match e_f.holes 0 with
  | .some ⟨[⟨e_hole, hn_hole⟩], h_holes⟩ =>
    if heq : (reduce RedAff (DCC? (f e_hole))).fst = e_hole then
      if heq₂ : (view_fn_type? α).isNone then by
        have h := aff_sound' (DCC? (f e_hole))
        simp [heq] at h
        exact .some ⟨_, _, .id₁ e_f (view_fn_type?_none_sound' heq₂) h_holes h⟩
      else .none
    else if h_contains : ((reduce RedAff (DCC? (f e_hole))).fst).hole_mem_tm then
      match α with
      | DCC? Coup(β) =>
        match e_hole with
        | DCC? ⟦β₂⟧(a, b) =>
          if heqc : β₂ = β then
            if heqa : (reduce RedAff (DCC? (f ⟦β⟧(a, b)))).fst = a then by
              have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
              cases heqc
              exact .some ⟨_, _, .fstc e_f h_holes ⟨hr, hn⟩⟩
            else if heqa : (reduce RedAff (DCC? (f ⟦β⟧(a, b)))).fst = b then by
              have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
              cases heqc
              exact .some ⟨_, _, .sndc e_f h_holes ⟨hr, hn⟩⟩
            else
              match h_app_eq : (reduce RedAff (DCC? (f ⟦β⟧(a, b)))) with
              | ⟨DCC? (f' a' b'), ⟨hr⟩⟩ =>
                have hn' := reduce_norm h_app_eq
                if heqa : a' = a then
                  if heqb : b' = b then
                    let f' : EtaExpr.Norm := ⟨f', hn'.congrFun.congrFun⟩
                    match f'.view_eta_fn with
                    | .some ⟨doms, e_f'⟩ =>
                      match doms with
                      | [α, ⟨β', hn⟩] =>
                        if heq_β' : β' = β then by
                          cases heq_β'; cases heqc; cases heqa; cases heqb
                          exact .some ⟨_, _, .eval e_f h_holes ⟨hr, hn'⟩ e_f'⟩
                        else .none
                      | _ => .none
                    | .none => .none
                  else .none
                else .none
              | _ => .none
          else .none
        | _ => .none
      | DCC? !(Coup(β)) =>
        match e_hole with
        | DCC? &(⟦β₂⟧(a, b)) =>
          if heqc : β₂ = β then
            if heqa : (reduce RedAff (DCC? (f &(⟦β⟧(a, b))))).fst = a then by
              have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
              cases heqc
              exact .some ⟨_, _, .fstc' e_f h_holes ⟨hr, hn⟩⟩
            else if heqa : (reduce RedAff (DCC? (f &(⟦β⟧(a, b))))).fst = b then by
              have ⟨hr, hn⟩ := reduce_sound_fst_norm heqa
              cases heqc
              exact .some ⟨_, _, .sndc' e_f h_holes ⟨hr, hn⟩⟩
            else .none
          else .none
        | _ => .none
      | α =>
        if heq_some : α.view_coup_bang?.isNone then
          match h_red_eq : (reduce RedAff (DCC? (f e_hole))) with
          | ⟨DCC? (f' e_hole'), ⟨hr⟩⟩ =>
            have hn' := reduce_norm h_red_eq
            if h_hole_eq : e_hole' = e_hole then
              match view_eta_fn ⟨f', hn'.congrFun⟩ with
              | .some ⟨doms', e_fn'⟩ => by
                if heq_doms : doms' = [mk α hn_α] then
                  cases heq_doms
                  cases h_hole_eq
                  exact .some ⟨_, _, .par e_f (view_coup_bang?_none_sound' heq_some) h_holes ⟨hr, hn'⟩ e_fn'⟩
                else exact .none
              | _ => .none
            else .none
          | _ => .none
        else .none
    else
      if h_some : (view_quot? ((reduce RedAff (DCC? (f e_hole))).fst)).isNone then
        .some ⟨_, _, .quot₁ e_f h_holes (aff_sound' _) (view_quot?_none_sound' h_some) h_contains⟩
      else .none
  | _ => .none-/

def canonicalize₂ {f : GenericExpr (@EtaConst τ_c)}
  {hn : IsNorm RedAff f} (α : GenericExpr EtaConst) (hn_α : IsNorm RedAff α) (β : GenericExpr EtaConst)
  (hn_β : IsNorm RedAff β) (e_f : (mk f hn).EtaFn [mk α hn_α, mk β hn_β]) :
  Option ((f' : EtaExpr.Norm) × (e_f' : EtaFn f' [mk α hn_α, mk β hn_β]) × e_f.Canonicalize e_f') :=
  match e_f.holes 0 with
  | .some ⟨[⟨e_hole₁, hn_hole₁⟩, ⟨e_hole₂, hn_hole₂⟩], h_holes⟩ =>
    if h_contains : ((reduce RedAff (DCC? (f e_hole₁ e_hole₂))).fst).hole_mem_tm then
      match h_red_eq : (reduce RedAff (DCC? (f e_hole₁ e_hole₂))) with
      | ⟨DCC? (e_hole₁' e_hole₂'), ⟨hr⟩⟩ =>
        have hn' := reduce_norm h_red_eq
        if heqa : e_hole₁' = e_hole₁ then
          if heqb : e_hole₂' = e_hole₂ then
            match α, β with
            | DCC? (Π(f_α, f_β) x_α), DCC? `((Π(f_α₂, f_β₂) x_α₂), τ') =>
              if heqc : (DCC? `((Π(f_α₂, f_β₂) x_α₂), τ')) = (DCC? `((Π(f_α, f_β) x_α), #((reduce RedAff (DCC? (f_α x_α))).fst))) then by
                cases heqc
                cases heqa
                cases heqb
                exact .some ⟨_, _, .id₂ e_f (aff_sound' (DCC? (f_α x_α))) h_holes ⟨hr, hn'⟩⟩
              else .none
            | _, _ => .none
          else .none
        else .none
      | _ => .none
    else
      match β with
      | (DCC? !<β>) =>
        match α with
        | DCC? !(α) =>
          .some ⟨_, _, .quot_bang e_f h_holes (aff_sound' _) h_contains⟩
        | _ => .none
      | DCC? `(α₂, β) =>
        if heq_α : α₂ = α then by
          cases heq_α
          exact .some ⟨_, _, .quot₂ e_f h_holes (aff_sound' _) h_contains⟩
        else .none
      | _ => .none
  | _ => .none

def canonicalize (e_f : EtaFn (τ_c := τ_c) ⟨f, hn⟩ doms) : Option ((f' : EtaExpr.Norm)
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

@[dcc_force_reduce]
def Canonicalize.deterministic (h₁ : Canonicalize (τ_c := τ_c) e_f e_f₁)
  (h₂ : Canonicalize (τ_c := τ_c) e_f e_f₂) : e_f₁ = e_f₂ := by
  induction h₁
  any_goals (
    focus
    try (
      cases h₂
      · grind
      · cases e_f₂
        rename_i h_dom
        cases h_dom
        rename_i hrn
        cases hrn
        rfl)
    done)
  case fstc' | sndc' =>
    cases h₂
    · grind
    · rename_i hn _ _ _
      exact (hn (by constructor)).elim
  · cases h₂
    rename_i hn _ _ _
    · exact (hn ⟨_, .id⟩).elim
    any_goals (
      focus
      try (
        rename_i h_hole₁ _ _ _ _ _ _ h_hole₂
        have ha := h_hole₁.unique h_hole₂
        simp_all
        cases ha
        rename_i hrt₁ _ _ _ _ hrt₂ _
        have ha := hrt₁.complete
        have hb := hrt₂.complete
        simp [raw] at ha
        rw [ha] at hb
        cases hb)
      done)
    · rename_i e_f₀ _ _ _ _ _ _ _ _
      exact e_f₀.eq (by assumption)
    · rename_i hn _ _ _
      exact (hn ⟨_, .quot⟩).elim
  any_goals (
    focus
    apply EtaFn.eq)

/-set_option maxHeartbeats 100000000000 in
def Canonicalize.some_complete {f f' : @EtaExpr.Norm τ_c}
  {e_f : EtaFn f doms}
  {e_f' : EtaFn f' doms}
  (h : Canonicalize e_f e_f') : e_f.canonicalize.isSome := by
  cases e_f with
  | tm₁ =>
    simp [canonicalize]
    unfold canonicalize₁
    split
    case h_1 =>
      split
      case isTrue heq_id =>
        cases h
        case id₁ hn _ _ _ _ _ _ _ =>
          have hneq := ViewFnType.complete_none hn
          simp [hneq]
        case fstc' hrt
          | sndc' hrt
          | par hrt _ _ _ _ _ _ _
          | sndc hrt _ _ _ _ _
          | eval hrt _ _ _ _ _ _ _
          | fstc hrt _ _ _ _ _ =>
          have heq := hrt.complete
          rename_i holes₁ _ holes₂
          have hole_eq := holes₁.unique holes₂
          simp at hole_eq
          cases hole_eq
          simp_all [raw, red_aff]
          try (cases heq)
        case quot₁ hrt _ hn_mem_hole _ _ _ holes₁ _ holes₂ =>
          have heq := hrt.complete
          have hole_eq := holes₁.unique holes₂
          simp at hole_eq
          cases hole_eq
          simp_all [red_aff]
          cases heq
          have h := holes₁.hole_mem_tm ⟨0, by grind⟩
          grind
      case isFalse =>
        split
        case isTrue =>
          split
          case h_1 hc _ =>
            simp_all only
            
            sorry
          case h_2 =>
            sorry
        case isFalse =>
          sorry
    case h_2 =>
      sorry
  | tm₂ =>
    sorry-/

set_option maxHeartbeats 100000000000 in
def Canonicalize.some_complete {f f' : @EtaExpr.Norm τ_c}
  {e_f : EtaFn f doms}
  {e_f' : EtaFn f' doms}
  (h : Canonicalize e_f e_f') : e_f.canonicalize.isSome := by
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
      exact ViewFnType.complete_none (by assumption)
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
      have hneq : (reduce RedAff (f.1.app (β.mkc a b))).fst ≠ β.mkc a b := fun h => by
        simp [raw, h] at heq
        cases heq
      split
      · contradiction
      · have h : (reduce RedAff (f.1.app (β.mkc a b))).fst.hole_mem_tm = true := by
          cases e_h
          rename_i e_h
          have h := e_h.sigl_hole_mem_tm
          rw [← heq] at h
          --simp [raw, Holes.v_elems, Vector.mk, get, hole_mem_tm, Vector.get] at h
          exact h
        split
        case isTrue =>
          dsimp
          simp [view_coup_bang?]
          have h : (reduce RedAff (f.1.app (β.mkc a b))).fst = a := heq
          simp [h]
          split
          simp
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
      have hneq : (reduce RedAff (f.1.app (β.mkc a b))).fst ≠ β.mkc a b := fun h => by
        simp [raw, h] at heq
        cases heq
      split
      · contradiction
      case isFalse =>
        have h : (reduce RedAff (f.1.app (β.mkc a b))).fst.hole_mem_tm = true := by
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
          have hn : (reduce RedAff (f.1.app (β.mkc a b))).fst = b := heq
          simp [hn]
          split
          · split
            simp
          · split
            simp
        · contradiction
    · grind
  | eval =>
    rename_i f hn_f βt ahn₁ a₁ b hn_hole₁ f' hn' α hn_α e_f e_h hrt e_f'
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
      have hneq : (reduce RedAff (f.app (βt.mkc a₁ b))).fst ≠ βt.mkc a₁ b := fun h => by
        grind
      simp [hneq]
      have h_hole : (reduce RedAff (f.app (βt.mkc a₁ b))).fst.hole_mem_tm := by
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
        simp [h_comp]
      case h_2 =>
        rename_i heq_catchall
        generalize h_red : reduce RedAff (f.app (βt.mkc a₁ b)) = res
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
      have hneq : (reduce RedAff (f.1.app (β.mkc a b).box)).fst ≠ (β.mkc a b).box := by
        intro h
        simp_all
        simp [raw] at heq
        rw [heq] at h
        cases h
      simp [hneq]
      have h : (reduce RedAff (f.1.app (β.mkc a b).box)).fst.hole_mem_tm := by
        cases e_h
        rename_i e_h
        have h := e_h.sigl_hole_mem_tm_box
        simp [raw] at heq
        grind
      simp [h]
      simp [raw] at heq
      simp [view_coup_bang?]
      simp [heq]
      split
      simp
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
      have hneq : (reduce RedAff (f.1.app (β.mkc a b).box)).fst ≠ (β.mkc a b).box := by
        intro h
        simp_all
        simp [raw] at heq
        rw [heq] at h
        cases h
      simp [hneq]
      have h : (reduce RedAff (f.1.app (β.mkc a b).box)).fst.hole_mem_tm := by
        cases e_h
        rename_i e_h
        have h := e_h.sigr_hole_mem_tm_box
        simp [raw] at heq
        grind
      simp [h]
      simp [raw] at heq
      simp [view_coup_bang?]
      simp [heq]
      split
      · split
        · simp
      · split
        · simp
    · grind
  | par =>
    rename_i f' hn₂ e_f h_view e_h hrt e_f'
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
      rename_i e_hole hn_hole h_holes
      simp at heq'
      --cases heq'.left; cases heq'.right
      rename_i f _ _ _ hole₁ hn_hole₁ _heq h_dom x
      have hneq : (reduce RedAff (f.app hole₁)).fst ≠ hole₁ := by
        intro h
        simp at heq
        rw [heq] at h
        cases h
      have hneq' : ((reduce RedAff (f.app hole₁)).fst ≠ e_hole) := by
        grind
      split
      · grind
      case isFalse hn =>
        have h : hole_mem_tm hole₁ := by
          cases e_h
          rename_i e_h
          exact e_h.hole_mem_tm
        have h_mem : (reduce RedAff (f.app hole₁)).fst.hole_mem_tm = true := by
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
              have h_f'_eq : f'' = f' := by
                grind
              subst h_hole_eq
              cases h_f'_eq
              have h_view_f' := e_f'.complete
              simp [h_view_f']
            case h_2 x =>
              generalize h_red : reduce RedAff (f.app hole₁) = res
              cases res
              rename_i fst snd
              cases snd
              rename_i hr
              have h_fst : fst = f'.app hole₁ := by
                grind
              subst h_fst
              exact (x f' hole₁ (match hrt with | ⟨a, _⟩ => a) h_red).elim
        · cases heq'.left
          grind
    · grind
  | quot₁ =>
    rename_i e_f e_h hrt h_view_quot h_mem
    have heq := hrt.complete_fst
    have heq_whole := hrt.complete
    have h_heq := e_h.complete
    cases e_f
    simp [canonicalize]
    unfold canonicalize₁
    rw [h_heq]
    split
    case h_1 heq' =>
      rename_i e_hole hn_hole e_h'
      have heq_hole := e_h.unique e_h'
      cases heq_hole
      simp at heq'
      rename_i f hn_f α hn_α hole₁ hn_hole₁ e' hn_e' _heq h_dom x
      have h_mem_hole : hole₁.hole_mem_tm := by
        cases e_h
        rename_i e_h
        exact e_h.hole_mem_tm
      have hn : (reduce RedAff (f.app hole₁)).fst ≠ hole₁ := fun h => by
        grind
      split
      · grind
      case isFalse =>
        have h : (reduce RedAff (f.app hole₁)).fst.hole_mem_tm = false := by
          grind
        split
        · grind
        · simp [heq.symm ▸ ViewQuot.complete_none h_view_quot]
    · grind
  | quot_bang =>
    rename_i e_f e_h hrt h_mem
    have heq := hrt.complete_fst
    have heq_whole := hrt.complete
    have h_heq := e_h.complete
    cases e_f
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
      rename_i f₀ _ _ _ _ _ hole₁ _ hole₂ _ _ _ _ _ _ _ _
      have h_contains : (reduce RedAff ((f₀.app hole₁).app hole₂)).fst.hole_mem_tm ≠ true := fun h => by
        have h := heq ▸ h
        grind
      split
      · grind
      · simp
    · grind
  | quot₂ =>
    rename_i e_f e_h hrt h_mem
    have heq := hrt.complete_fst
    have heq_whole := hrt.complete
    have h_heq := e_h.complete
    cases e_f
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
      rename_i f₀ _ _ _ _ _ hole₁ _ hole₂ _ _ _ _ _ _ _ _
      have h_contains : (reduce RedAff ((f₀.app hole₁).app hole₂)).fst.hole_mem_tm ≠ true := fun h => by
        have h := heq ▸ h
        grind
      split
      · grind
      · simp
    · grind
  | id₂ =>
    rename_i e_f hrt₁ e_h hrt
    have heq := hrt.complete_fst
    have heqb := hrt₁.complete_fst
    have heq_whole := hrt.complete
    have heq_whole' := hrt₁.complete
    have h_heq := e_h.complete
    cases e_f
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
      rename_i f₀ _ _ _ _ _ _ _ _ hole₁ _ hole₂ _ _ _ _ _ _ _
      have h_mem₁ : hole₁.hole_mem_tm :=
        match e_h with
        | .tm₂ h _ _ => h.hole_mem_tm
      have h_mem : (reduce RedAff ((f₀.app hole₁).app hole₂)).fst.hole_mem_tm = true := by
        grind
      split
      case isTrue =>
        split
        case h_1 =>
          simp_all
          aesop
        case h_2 x =>
          generalize h_red : reduce RedAff ((f₀.app hole₁).app hole₂) = res
          cases res
          rename_i fst snd
          cases snd
          rename_i hr
          have h_fst : fst = hole₁.app hole₂ := by
            grind
          subst h_fst
          exact (x hole₁ hole₂ (match hrt with | ⟨a, _⟩ => a) h_red).elim
      · grind
    · grind

end EtaFn

end NormExpr
