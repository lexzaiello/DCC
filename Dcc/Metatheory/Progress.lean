import Dcc.Judge3
import Dcc.Metatheory.SubjectReduction
import Lean.Elab.Tactic
import Qq

namespace Expr

open Dsl in
inductive Value : Expr → Type
  | sort        : Value (DCC (Sort u))
  | top         : Value (DCC 𝟙)
  | bot         : Value (DCC 𝟘)
  | bool        : Value (DCC 𝟚)
  | true        : Value (DCC 𝟙₂)
  | false       : Value (DCC 𝟘₂)
  | tintro      : Value (DCC ∗)
  | refl₁       : Value B → Value x → Value (DCC ((refl B) (& x)))
  | refl₂       : Value B → Value x → Value y → Value (DCC ((refl B) (& x) (& y)))
  | points₁     : (h_ar : point_arity e = 1) → Value (e.points.get ⟨0, by grind⟩) → Value e
  | points₂     : (h_ar : point_arity e = 2) → Value (e.points.get ⟨0, by grind⟩) → Value (e.points.get ⟨1, by grind⟩) → Value e
  | points₃     : (h_ar : point_arity e = 3)
    → Value (e.points.get ⟨0, by grind⟩)
    → Value (e.points.get ⟨1, by grind⟩)
    → Value (e.points.get ⟨2, by grind⟩)
    → Value e
  | points₄     : (h_ar : point_arity e = 4)
    → Value (e.points.get ⟨0, by grind⟩)
    → Value (e.points.get ⟨1, by grind⟩)
    → Value (e.points.get ⟨2, by grind⟩)
    → Value (e.points.get ⟨3, by grind⟩)
    → Value e
  | eql₁        : Value B → Value x → Value (DCC ((Eql B) (& x)))
  | eq'₁        : Value B → Value x → Value (DCC ((=' B) x))
  | eq'₂        : Value B → Value x → Value y → Value (DCC ((=' B) x y))
  | curr₁       : Value A → Value B → Value x → Value y → Value (DCC ((Λ A B x) y))
  | curr'₁      : Value A → Value B → Value x → Value y → Value (DCC ((!Λ A B x) (& y)))
  | ind_bool₁   : Value motive → Value x → Value y → Value z → Value (DCC ((𝟚.Rec motive x y) z))
  -- however the recursor applied to something is NOT a value, since bot is not inhabited
  | ind_bot₁    : Value motive → Value x → Value (DCC ((𝟘.Rec motive) x))
  | pi          : Value B → Value C → Value x → Value (DCC ((Π B C) x))

def Value.congrFun (hv : Value (DCC (f x))) : Value f := by
  cases hv
  any_goals (
    focus
    try (
      constructor
      any_goals (assumption)
      try (grind))
    done)
  any_goals (grind [point_arity])
  · exact eq'₁ (by assumption) (by assumption)
  any_goals (
    apply points₃
    any_goals (assumption)
    grind)
  any_goals (
    apply points₂
    any_goals (assumption)
    grind)

def Value.congrArg (hv : Value (DCC (f x))) : Value x := by
  cases hv
  any_goals (
    apply points₁
    any_goals (assumption)
    grind)
  any_goals (grind [point_arity])
  any_goals (assumption)

set_option maxHeartbeats 10000000 in
theorem Value.is_norm (h : Value e) : (Σ' e', Red e e') → False := by
  induction h
  any_goals (
    focus
    try (
      intro ⟨_, h⟩
      cases h
      grind [point_arity])
    done)
  all_goals (
    intro ⟨_, h⟩
    cases h)
  any_goals (grind [point_arity])
  case ind_bot₁.congrFun | curr'₁.congrArg | eq'₁.congrFun | eql₁.congrFun | eql₁.congrArg | refl₁.congrFun | refl₁.congrArg | refl₂.congrArg =>
    rename_i h
    match h with
    | .point 0 hn h =>
      aesop
  case refl₂.congrFun h =>
    match h with
    | .congrFun (.point 0 hn h) => aesop
    | .congrArg (.point 0 hn h) => aesop
  case points₁.point | points₂.point | points₃.point | points₄.point =>
    expose_names
    rw [h_ar] at h
    interval_cases n
    <;> aesop
  case ind_bot₁.congrArg | eq'₁.congrArg | eq'₂.congrArg | curr₁.congrArg | pi.congrArg | ind_bool₁.congrArg =>
    aesop
  case pi.congrFun =>
    rename_i h
    match h with
    | .point 0 hn h => aesop
    | .point 1 hn h => aesop
  case eq'₂.congrFun =>
    rename_i h
    match h with
    | .congrFun (.point 0 hn h) => aesop
    | .congrArg h => aesop
  case ind_bool₁.congrFun | curr₁.congrFun | curr'₁.congrFun =>
    rename_i h
    match h with
    | .point 0 hn h => aesop
    | .point 1 hn h => aesop
    | .point 2 hn h => aesop

set_option maxHeartbeats 10000000 in
theorem Value.is_norm' (h : Value e) : (Σ e', Red' e e') → False := by
  induction h
  any_goals (
    focus
    try (
      intro ⟨_, h⟩
      cases h
      grind [point_arity])
    done)
  all_goals (
    intro ⟨_, h⟩
    cases h)
  any_goals (grind [point_arity])
  case ind_bot₁.congrFun | curr'₁.congrArg | eq'₁.congrFun | eql₁.congrFun | eql₁.congrArg | refl₁.congrFun | refl₁.congrArg | refl₂.congrArg =>
    rename_i h
    match h with
    | .point 0 hn h =>
      aesop
  case refl₂.congrFun h =>
    match h with
    | .congrFun (.point 0 hn h) => aesop
    | .congrArg (.point 0 hn h) => aesop
  case points₁.point | points₂.point | points₃.point | points₄.point =>
    expose_names
    rw [h_ar] at h
    interval_cases n
    <;> aesop
  case ind_bot₁.congrArg | eq'₁.congrArg | eq'₂.congrArg | curr₁.congrArg | pi.congrArg | ind_bool₁.congrArg =>
    aesop
  case pi.congrFun =>
    rename_i h
    match h with
    | .point 0 hn h => aesop
    | .point 1 hn h => aesop
  case eq'₂.congrFun =>
    rename_i h
    match h with
    | .congrFun (.point 0 hn h) => aesop
    | .congrArg h => aesop
  case ind_bool₁.congrFun | curr₁.congrFun | curr'₁.congrFun =>
    rename_i h
    match h with
    | .point 0 hn h => aesop
    | .point 1 hn h => aesop
    | .point 2 hn h => aesop

open Lean Elab Tactic Qq in
elab "all_judge" thm_ih:ident goal:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let goal_tm ← elabTerm goal .none
    let some goal ← Meta.liftMetaM <| checkTypeQ goal_tm q(_root_.Expr → _root_.Expr → Type)
      | return ()
    let thm_ih_tm ← elabTerm thm_ih .none
    let hyps : Array (Σ' (_decl : LocalDecl) (_e : Q(_root_.Expr)) (_τ : Q(_root_.Expr)), Lean.FVarId) ← lctx.decls.toArray.filterMapM (fun (h : Option LocalDecl) => do
      let some h ← (pure h) | return none
      if h.isImplementationDetail then return none
      let some ty ← checkTypeQ h.type q(Type) | return none
      match ty with
      | ~q(Judge $e $τ) =>
        pure (.some ⟨h, e, τ, h.fvarId⟩)
      | _ => return .none)
    let hyps' : Array Meta.Hypothesis ← hyps.mapM (fun ⟨_h, e, τ, v⟩ => do
      let nm ← Meta.getUnusedUserName thm_ih.getId.eraseMacroScopes
      pure ⟨nm, q($goal $e $τ), (mkAppN thm_ih_tm #[e, τ, .fvar v]), .default, .default⟩)
    let ⟨_, g'⟩ ← g.assertHypotheses hyps'
    replaceMainGoal [g']

def Value.inv_box (hv : Value x) (ht : Judge x (open Dsl in (DCC (! A)))) : Σ' x₀, x = (DCC (& x₀)) := by
  cases hv
  any_goals (
    focus
    try (cases ht)
    done)
  case ind_bot₁ =>
    cases ht with
    | app =>
      expose_names
      cases a_3 with
      | ind_bot =>
        expose_names
        replace a_5 := a_5.push_head (.congrFun .quot)
        have heq := a_5.pi_eq
        cases heq
  case refl₁ =>
    cases ht with
    | app =>
      expose_names
      cases a_3 with
      | refl =>
        expose_names
        replace a_2 := a_2.push_head .quot
        have ⟨hn_δ, _⟩ := a_3.is_norm a_6.is_norm
        cases (a_2.elim_norml (bang_is_norm hn_δ)).elim_norm a_4.is_norm
        clear a_2
        replace a_5 := a_5.push_head (.congrFun .quot)
        have pi_eq := a_5.pi_eq
        simp [congr_reduce₁ (e := f_α'.map) (by grind), congr_reduce₁ (e := f_α'.eql) (by grind), congr_reduce₁ (e := x.box) (by grind), set_points, points] at pi_eq
  case refl₂ =>
    cases ht with
    | app =>
      expose_names
      cases a_4 with
      | app =>
        expose_names
        cases a_7 with
        | refl =>
          expose_names
          have ⟨hn_δ, _⟩ := a_7.is_norm a_10.is_norm
          replace a_4 := a_4.push_head .quot
          cases (a_4.elim_norml (bang_is_norm hn_δ)).elim_norm a_8.is_norm
          clear a_4
          replace a_9 := a_9.push_head (.congrFun .quot)
          have pi_eq := a_9.pi_eq
          simp [congr_reduce₁ (e := f_α'.map) (by grind), congr_reduce₁ (e := f_α'.eql) (by grind), congr_reduce₁ (e := x.box) (by grind), set_points, points] at pi_eq
          cases pi_eq.1.1; cases pi_eq.1.2; cases pi_eq.2
          clear pi_eq
          clear a_9
          replace a_6 := a_6.push_head .eql
          have a_6' : (((reduce Red f_α').fst.app (reduce Red x).fst).eq y y).RedNorm ((reduce Red ((reduce Red f_α').fst.app (reduce Red x).fst)).fst.eq (reduce Red y).fst (reduce Red y).fst) :=
            ⟨.trans (aff_mk_point' (n := 1) (reduce_sound rfl)) (.trans (aff_mk_point' (n := 2) (reduce_sound rfl)) (aff_mk_point' (n := 0) (reduce_sound rfl))),
              eq_is_norm
                (reduce_norm rfl)
                (reduce_norm rfl)
                (reduce_norm rfl)⟩
          cases a_6'.unique a_6
  case points₁ | points₂ | points₃ | points₄ =>
    expose_names
    cases x
    any_goals (grind [point_arity])
    try (any_goals (cases ht))
    try (exact ⟨_, rfl⟩)
  case eql₁ =>
    cases ht with
    | app =>
      expose_names
      cases a_3 with
      | eql =>
        expose_names
        replace a_2 := a_2.push_head .quot
        have ⟨hn_δ, _⟩ := a_3.is_norm a_6.is_norm
        cases (a_2.elim_norml (bang_is_norm hn_δ)).elim_norm a_4.is_norm
        replace a_5 := a_5.push_head (.congrFun .quot)
        have pi_eq := a_5.pi_eq
        simp [congr_reduce₁ (e := f_α'.map) (by grind), congr_reduce₁ (e := x.box) (by grind), set_points, points] at pi_eq
  case eq'₁ =>
    cases ht with
    | app =>
      expose_names
      cases a_3 with
      | eq_mk =>
        expose_names
        replace a_2 := a_2.push_head .quot
        have ⟨hn_δ, _⟩ := a_3.is_norm a_6.is_norm
        cases (a_2.elim_norml hn_δ).elim_norm a_4.is_norm
        replace a_5 := a_5.push_head (.congrFun .quot)
        have pi_eq := a_5.pi_eq
        simp [congr_reduce₃ (e := (α.curr f_α'
                ((f_α'.comp f_α'.fstc).pi
                  ((α.sigma f_α').curr (f_α'.comp f_α'.fstc)
                    (((α.sigma f_α').sigma (f_α'.comp f_α'.fstc)).quot (Expr.sort 0)))))) (by grind), set_points, points] at pi_eq
  case eq'₂ =>
    cases ht with
    | app =>
      expose_names
      cases a_4 with
      | app =>
        expose_names
        cases a_7 with
        | eq_mk =>
          expose_names
          replace a_4 := a_4.push_head .quot
          have ⟨hn_δ, _⟩ := a_7.is_norm a_10.is_norm
          cases (a_4.elim_norml hn_δ).elim_norm a_8.is_norm
          replace a_9 := a_9.push_head (.congrFun .quot)
          have pi_eq := a_9.pi_eq
          simp [congr_reduce₃ (e := (α_1.curr f_α'
                ((f_α'.comp f_α'.fstc).pi
                  ((α_1.sigma f_α').curr (f_α'.comp f_α'.fstc)
                    (((α_1.sigma f_α').sigma (f_α'.comp f_α'.fstc)).quot (Expr.sort 0)))))) (by grind), set_points, points] at pi_eq
          cases pi_eq.1.1; cases pi_eq.1.2; cases pi_eq.2
          clear pi_eq
          clear a_9
          cases a_7 with
          | simple =>
            expose_names
            have hn_A_1 : IsNorm Red A_1 := fun ⟨_, h⟩ => a_10.is_norm ⟨_, .congrFun (.point 0 (by grind) (.point 1 (by point_arity) h))⟩
            have hn_B_1 : IsNorm Red B_1 := fun ⟨_, h⟩ => a_10.is_norm ⟨_, .congrFun (.point 1 (by grind) (.point 1 (by point_arity) (.point 1 (by change _ < (A_1.quot B_1).point_arity; point_arity) h)))⟩
            cases a_7.elim_norm hn_A_1
            cases a_9.elim_norm hn_B_1
            replace a_6 := a_6.push_head .curr
            simp [congr_reduce₂ (e := ((f_α'.comp f_α'.fstc).pi
                ((α_1.sigma f_α').curr (f_α'.comp f_α'.fstc)
                  (((α_1.sigma f_α').sigma (f_α'.comp f_α'.fstc)).quot (Expr.sort 0))))) (by grind), points, set_points] at a_6
            replace a_6 := a_6.congrArg ⟨aff_mk_point' (n := 2) (reduce_sound rfl), (mk_is_norm (reduce_norm rfl) (reduce_norm rfl) (reduce_norm rfl))⟩
            cases a_6.elim_norm (pi_is_norm (reduce_norm rfl) (reduce_norm rfl) (mk_is_norm (reduce_norm rfl) (reduce_norm rfl) (reduce_norm rfl)))
  case curr₁ =>
    expose_names
    cases ht with
    | app =>
      expose_names
      cases a_5 with
      | curr =>
        expose_names
        replace a_4 := a_4.push_head .quot
        have ⟨hn_δ, _⟩ := a_5.is_norm a_10.is_norm
        cases (a_4.elim_norml hn_δ).elim_norm a_6.is_norm
        replace a_7 := a_7.push_head (.congrFun .quot)
        have pi_eq := a_7.pi_eq
        cases pi_eq
  case curr'₁ =>
    expose_names
    cases ht with
    | app =>
      expose_names
      cases a_5 with
      | curr' =>
        expose_names
        replace a_4 := a_4.push_head .quot
        have ⟨hn_δ, _⟩ := a_5.is_norm a_10.is_norm
        cases (a_4.elim_norml (bang_is_norm a_9.is_norm)).elim_norm a_6.is_norm
        replace a_7 := a_7.push_head (.congrFun .quot)
        have pi_eq := a_7.pi_eq
        cases pi_eq
  case ind_bool₁ =>
    expose_names
    cases ht with
    | app =>
      expose_names
      cases a_5 with
      | ind_bool =>
        expose_names
        replace a_4 := a_4.push_head .quot
        have ⟨hn_δ, _⟩ := a_5.is_norm a_9.is_norm
        cases (a_4.elim_norml hn_δ).elim_norm a_6.is_norm
        clear a_4
        replace a_7 := a_7.push_head (.congrFun .quot)
        have pi_eq := a_7.pi_eq
        cases pi_eq
  case pi =>
    expose_names
    cases ht with
    | app =>
      expose_names
      cases a_4 with
      | pi =>
        expose_names
        replace a_3 := a_3.push_head .quot
        have ⟨hn_δ, _⟩ := a_4.is_norm a_8.is_norm
        cases (a_3.elim_norml hn_δ).elim_norm a_5.is_norm
        replace a_6 := (a_6.push_head (.congrFun .quot)).push_head .quot
        cases a_6.elim_norm (by grind)

namespace Judge

def inv_pi (h : Judge (open Dsl in (DCC ((Π B C) x))) τ) : Σ' (u : Level), τ = (DCC (Sort u)) := by
  cases h with
  | app ht =>
    cases ht with
    | pi =>
      expose_names
      cases ((a_7.push_head (.congrFun .quot)).push_head .quot).elim_norm (by grind)
      exact ⟨_, rfl⟩

def inv_eql (h : Judge (DCC ((Eql B) (& x) (& y))) τ) : τ = (DCC (Sort 0)) := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | app =>
      expose_names
      cases a_4 with
      | eql =>
        expose_names
        have ⟨hn_δ, _⟩ := a_4.is_norm a_7.is_norm
        cases ((a_1.push_head .quot).elim_norml (bang_is_norm hn_δ)).elim_norm a_5.is_norm
        clear a_1
        replace a_6 := a_6.push_head (.congrFun .quot)
        have heq_pi := a_6.pi_eq
        simp [congr_reduce₁ (e := f_α'.map) (by grind), congr_reduce₃ (e := (δ.curr' f_α' ((δ.sigma f_α').bang.quot (Expr.sort 0)))) (by grind), congr_reduce₁ (e := x.box) (by grind), points, set_points] at heq_pi
        cases heq_pi.1.1; cases heq_pi.1.2; cases heq_pi.2
        clear heq_pi
        clear a_6
        simp [congr_reduce₂ (e := ((δ.sigma f_α').bang.quot (Expr.sort 0))) (by grind), points, set_points] at a_3
        replace a_3 := (a_3.push_head .curr').push_head .quot
        simp [elim_reduce_norm_fst (sort_is_norm)] at a_3
        cases a_3.elim_norm (by grind)
        rfl

def inv_refl (h : Judge (DCC ((refl B) (& x) (& y))) τ) : τ = (DCC (= #((reduce Red (B.app x)).fst) #((reduce Red y).fst) #((reduce Red y).fst))) := by
  cases h with
  | app =>
    expose_names
    cases a_1 with
    | app =>
      expose_names
      cases a_4 with
      | refl =>
        expose_names
        have ⟨hn_δ, _⟩ := a_4.is_norm a_7.is_norm
        cases ((a_1.push_head .quot).elim_norml (bang_is_norm hn_δ)).elim_norm a_5.is_norm
        clear a_1
        replace a_6 := a_6.push_head (.congrFun .quot)
        have heq := a_6.pi_eq
        simp [congr_reduce₁ (e := f_α'.map) (by grind), congr_reduce₁ (e := f_α'.eql) (by grind), congr_reduce₁ (e := x.box) (by grind), set_points, points] at heq
        cases heq.1.1; cases heq.1.2; cases heq.2
        clear heq
        clear a_6
        replace a_3 := a_3.push_head .eql
        have heq := a_3.complete_fst
        simp [congr_reduce₃ (e := (((reduce Red f_α').fst.app (reduce Red x).fst).eq y y)) (by grind)] at heq
        simp [set_points, points] at heq
        cases heq
        have heq₁ := a_8.complete_fst
        cases heq₁
        have h := reduce_self (r := Red) (e := B)
        simp
        rw [h]
        symm
        refine reduce_complete_fst ?_ ?_
        · refine .trans ?_ (reduce_sound rfl)
          exact .trans (congrFun' (reduce_sound rfl)) (congrArg' (reduce_sound rfl))
        · exact reduce_norm rfl

def elim_bot (ht : Judge e (DCC 𝟘)) (hv : Value e) : False := by
  cases ht with
  | app =>
    expose_names
    have hv_f := hv.congrFun
    have hv_x := hv.congrArg
    cases hv_f
    any_goals (
      focus
      try (cases a)
      done)
    case refl₁ =>
      expose_names
      cases a with
      | app =>
        expose_names
        cases a_6 with
        | refl =>
          expose_names
          replace a := a.push_head .quot
          have ⟨hn_δ, _⟩ := a_6.is_norm a_9.is_norm
          cases (a.elim_norml (bang_is_norm hn_δ)).elim_norm a_7.is_norm
          clear a
          replace a_8 := a_8.push_head (.congrFun .quot)
          have pi_eq := a_8.pi_eq
          simp [congr_reduce₁ (e := f_α'.map) (by grind),  congr_reduce₁ (e := f_α'.eql) (by grind), congr_reduce₁ (e := x_1.box) (by grind), points, set_points] at pi_eq
          cases pi_eq.1.1; cases pi_eq.1.2; cases pi_eq.2
          clear pi_eq
          clear a_8
          replace a_1 := ((a_1.push_head .map)).elim_normr a_2.is_norm
          have a_1' : ((reduce Red f_α').fst.app (reduce Red x_1).fst).bang.RedNorm (reduce Red ((reduce Red f_α').fst.app (reduce Red x_1).fst)).fst.bang := ⟨aff_mk_point' (n := 0) (reduce_sound rfl), bang_is_norm (reduce_norm rfl)⟩
          cases a_1'.unique a_1
          have ⟨x₀, heq⟩ := hv_x.inv_box (by assumption)
          cases heq
          replace a_3 := a_3.push_head .eql
          have a_3' : RedNorm (((reduce Red f_α').fst.app (reduce Red x_1).fst).eq x₀ x₀) ((reduce Red ((reduce Red f_α').fst.app (reduce Red x_1).fst)).fst.eq x₀ x₀) :=
            ⟨aff_mk_point' (n := 0) (reduce_sound rfl), eq_is_norm (reduce_norm rfl)
              (fun ⟨_, h⟩ => hv_x.is_norm ⟨_, .point 0 (by grind) h⟩) (fun ⟨_, h⟩ => hv_x.is_norm ⟨_, .point 0 (by grind) h⟩)⟩
          cases a_3'.unique a_3
    case refl₂ => cases inv_refl a
    any_goals (
      focus
      try (
        cases hv
        any_goals (grind [point_arity]))
      done)
    case points₁ =>
      expose_names
      cases hv
      case ind_bot₁ =>
        cases a with
        | ind_bot =>
          expose_names
          replace a_3 := a_3.push_head (.congrFun .quot)
          have heq := a_3.pi_eq
          cases heq
      case refl₁ | eql₁ =>
        cases a with
        | _ =>
          expose_names
          replace a_1 := a_1.push_head .quot
          have ⟨hn_δ, _⟩ := a_6.is_norm a_7.is_norm
          cases (a_1.elim_norml (bang_is_norm hn_δ)).elim_norm a_2.is_norm
          clear a
          replace a_8 := a_3.push_head (.congrFun .quot)
          have pi_eq := a_8.pi_eq
          simp [congr_reduce₁ (e := f_α'.map) (by grind),  congr_reduce₁ (e := f_α'.eql) (by grind), congr_reduce₁ (e := x.box) (by grind), points, set_points] at pi_eq
      any_goals (grind [point_arity])
      case eq'₁ =>
        cases a with
        | _ =>
          expose_names
          replace a_3 := a_3.push_head (.congrFun .quot)
          have pi_eq := a_3.pi_eq
          cases pi_eq
    case points₂ =>
      expose_names
      cases hv
      any_goals (grind [point_arity])
      case pi =>
        expose_names
        cases a
        case _ =>
          expose_names
          replace a_3 := (a_3.push_head (.congrFun .quot)).push_head .quot
          cases a_3.elim_norm (by grind)
    case points₃ =>
      expose_names
      cases hv
      any_goals (grind [point_arity])
      case curr₁ | curr'₁ | ind_bool₁ =>
        cases a with
        | _ =>
          expose_names
          replace a_3 := a_3.push_head (.congrFun .quot)
          have pi_eq := a_3.pi_eq
          cases pi_eq
    case eq'₁ =>
      cases hv
      any_goals (grind [point_arity])
      · expose_names
        cases a with
        | app =>
          expose_names
          cases a_9 with
          | eq_mk =>
            expose_names
            replace a_11 := a_11.push_head (.congrFun .quot)
            have ⟨hn_δ, _⟩ := a_9.is_norm a_12.is_norm
            cases a_11.elim_norm (pi_is_norm a_13.is_norm
              (curr_is_norm hn_δ a_13.is_norm
                (pi_is_norm₀ (comp_is_norm a_13.is_norm (fst_is_norm a_13.is_norm))
                             (curr_is_norm (sigma_is_norm hn_δ a_13.is_norm) (comp_is_norm a_13.is_norm (fst_is_norm a_13.is_norm)) (quot_is_norm (sigma_is_norm (sigma_is_norm hn_δ a_13.is_norm) (comp_is_norm a_13.is_norm (fst_is_norm a_13.is_norm))) (by grind)))))
              (fun ⟨_, h⟩ => a_5.is_norm ⟨_, h⟩))
            clear a_11
            replace a_3 := (a_3.push_head .curr)
            have heq := a_3.pi_eq
            cases heq

end Judge

def Value.inv_sigma (hv : Value x) (ht : Judge x (open Dsl in (DCC (Σ A B)))) : Σ' x₀ y₀, x = (DCC (,B x₀ y₀)) := by
  cases hv
  any_goals (
    focus
    try (cases ht)
    done)
  case ind_bot₁ | ind_bool₁ | refl₁ | eql₁ | curr₁ | curr'₁ | eq'₁ =>
    cases ht with
    | app a_3 b c d  =>
      expose_names
      cases a_3 with
      | _ =>
        expose_names
        cases (RedNorm.push_head (by assumption) (.congrFun .quot)).pi_eq
  case eq'₂ =>
    cases ht with
    | app a_3 b c d  =>
      expose_names
      cases a_3 with
      | app a_4 =>
        cases a_4 with
        | _ =>
          expose_names
          have heq := (RedNorm.push_head (by assumption) (.congrFun .quot)).pi_eq
          simp [congr_reduce₃ (e := (δ.curr f_α'
                    ((f_α'.comp f_α'.fstc).pi
                      ((δ.sigma f_α').curr (f_α'.comp f_α'.fstc)
                        (((δ.sigma f_α').sigma (f_α'.comp f_α'.fstc)).quot (Expr.sort 0)))))) (by grind), points, set_points] at heq
          cases heq.1.1; cases heq.1.2; cases heq.2
          clear heq
          replace d := d.push_head .curr
          simp [congr_reduce₂ (e := ((f_α'.comp f_α'.fstc).pi
                ((δ.sigma f_α').curr (f_α'.comp f_α'.fstc)
                  (((δ.sigma f_α').sigma (f_α'.comp f_α'.fstc)).quot (Expr.sort 0))))) (by grind), points, set_points] at d
          have h := d.congrArg ⟨reduce_sound rfl, reduce_norm rfl⟩
          cases h.elim_norm (pi_is_norm (reduce_norm rfl) (reduce_norm rfl) (reduce_norm rfl))
  case refl₂ => cases Judge.inv_refl ht
  case pi => cases (Judge.inv_pi (by assumption)).2
  case points₁ | points₂ | points₄ =>
    expose_names
    cases ht
    any_goals (grind [point_arity])
  case points₃ =>
    cases ht
    any_goals (grind [point_arity])
    case mk =>
      expose_names
      cases a_7.elim_norm (fun ⟨_, h⟩ => (Value.is_norm (by assumption)) ⟨_, h⟩)
      exact ⟨_, _, rfl⟩

namespace Judge

def progress_app (a : Judge f (Expr.app (.pi f_α f_β) x_α))
                 (h₁ : f.Value ⊕ (e' : Expr) × f.Red' e')
                 (a_1 : (f_α.app x_α).DefEq α)
                 (a_2 : Judge x α)
                 (h₂  : x.Value ⊕ (e' : Expr) × x.Red' e')
                 (a_3 : ((f_β.app x_α).app x).RedNorm τ) :
    Value (DCC (f x)) ⊕ (Σ e', Red' (DCC (f x)) e') := by
  expose_names
  match h₁ with
  | .inl h₁ =>
    match h₂ with
    | .inl h₂ =>
      cases h₁
      any_goals (
        focus
        cases a
        done)
      case refl₁ =>
        cases a with
        | app =>
          expose_names
          cases a_6 with
          | refl =>
            expose_names
            have ⟨hn_δ, _⟩ := a_6.is_norm a_9.is_norm
            replace a_5 := a_5.push_head .quot
            cases (a_5.elim_norml (bang_is_norm hn_δ)).elim_norm a_7.is_norm
            clear a_5
            replace a_8 := a_8.push_head (.congrFun .quot)
            have heq_pi := a_8.pi_eq
            simp [congr_reduce₁ (e := f_α'.map) (by grind),
              congr_reduce₁ (e := f_α'.eql) (by grind),
              congr_reduce₁ (e := x_1.box) (by grind),
              points,
              set_points] at heq_pi
            cases heq_pi.1.1; cases heq_pi.1.2; cases heq_pi.2
            clear heq_pi
            clear a_8
            replace a_1 := a_1.push_head .map
            have a_1' := a_1.elim_normr a_2.is_norm
            have a_1'' : RedNorm ((reduce Red f_α').fst.app (reduce Red x_1).fst).bang ((reduce Red ((reduce Red f_α').fst.app (reduce Red x_1).fst)).fst).bang :=
              ⟨aff_mk_point' (n := 0) (reduce_sound rfl), bang_is_norm (reduce_norm rfl)⟩
            cases a_1''.unique a_1'
            clear a_1''
            have ⟨_, heq⟩ := h₂.inv_box (by assumption)
            cases heq
            cases h₂
            any_goals (grind [point_arity])
            refine .inl ?_
            constructor <;> assumption
      case refl₂ =>
        expose_names
        cases a.inv_refl
      case points₁ =>
        cases f
        any_goals (grind [point_arity, points])
        case ind_bot =>
          expose_names
          exact .inl (.ind_bot₁ a_5 h₂)
        case map =>
          expose_names
          cases a
          case _ =>
            expose_names
            have h := Arrow.is_norm (by assumption) (Judge.is_norm (by assumption))
            have ⟨hn_δ, _⟩ := h
            cases ((DefEq.push_head (by assumption) .quot).elim_norml (bang_is_norm (by assumption))).elim_norm (Judge.is_norm (by assumption))
            have ⟨x₀, heq⟩ := Value.inv_box h₂ (by assumption)
            cases heq
            refine .inr ⟨_, by constructor⟩
        case unbox | fmap =>
          expose_names
          cases a
          case _ =>
            expose_names
            cases ((DefEq.push_head (by assumption) .quot).elim_norml (bang_is_norm (RedNorm.is_norm (by assumption)))).elim_norm (Judge.is_norm (by assumption))
            have ⟨x₀, heq⟩ := Value.inv_box h₂ (by assumption)
            cases heq
            refine .inr ⟨_, by constructor⟩
        any_goals (
          focus
          cases a
          done)
        case eql | refl =>
          expose_names
          cases a
          case _ =>
            expose_names
            have h := Arrow.is_norm (by assumption) (Judge.is_norm (by assumption))
            have ⟨hn_δ, _⟩ := h
            cases ((DefEq.push_head (by assumption) .quot).elim_norml (bang_is_norm (by assumption))).elim_norm (Judge.is_norm (by assumption))
            have a_3' := RedNorm.push_head (by assumption) (.congrFun .quot)
            have heq := a_3'.pi_eq
            cases heq
            have ⟨x₀, heq⟩ := Value.inv_box h₂ (by assumption)
            cases heq
            refine .inl ?_
            cases h₂
            first
            | exact .eql₁ (by assumption) (by assumption)
            | exact .refl₁ (by assumption) (by assumption)
            any_goals (grind [point_arity])
        case fstc =>
          cases a
          case _ =>
            expose_names
            have h := Arrow.is_norm (by assumption) (Judge.is_norm (by assumption))
            have ⟨hn_δ, _⟩ := h
            cases ((DefEq.push_head (by assumption) .quot).elim_norml (sigma_is_norm hn_δ a_7.is_norm)).elim_norm (Judge.is_norm (by assumption))
            have a_3' := (RedNorm.push_head (by assumption) (.congrFun .quot)).push_head .quot
            cases a_3'.elim_norm hn_δ
            
            sorry
    | .inr ⟨_, h₂⟩ => exact .inr ⟨_, .congrArg h₂⟩
  | .inr ⟨_, h₁⟩ => exact .inr ⟨_, .congrFun h₁⟩

def progress (e τ : Expr) (h : Judge e τ) : Value e ⊕ (Σ e', Red' e e') := by
  cases h
  case sort | top | bot | tintro | false | true | bool => exact .inl (by constructor)
  any_goals (
    focus
    all_judge progress (fun (e τ : Expr) => Value e ⊕ (Σ e', Red' e e'))
    casesm* _ ⊕ (Σ _, _)
    · expose_names
      first
      | exact .inl (.points₁ (by grind) (by assumption))
      | exact .inl (.points₂ (by grind) (by assumption) (by assumption))
      | exact .inl (.points₃ (by grind) (by assumption) (by assumption) (by assumption))
      | exact .inl (.points₄ (by grind) (by assumption) (by assumption) (by assumption) (by assumption))
    any_goals (
      casesm* Σ _, _
      first
      | exact .inr ⟨_, .point 0 (by grind) (by assumption)⟩
      | exact .inr ⟨_, .point 1 (by grind) (by assumption)⟩
      | exact .inr ⟨_, .point 2 (by grind) (by assumption)⟩
      | exact .inr ⟨_, .point 3 (by grind) (by assumption)⟩))
  case app =>
    expose_names
    have h₁ := a.progress
    have h₂ := a_2.progress
    apply progress_app
    <;> assumption

end Judge

end Expr
