import Dcc.Judge

universe u
variable {τ_c : Type u}
variable [DecidableEq τ_c]

syntax "dcc_constr" : tactic

macro_rules
  | `(tactic| dcc_constr) => `(tactic| dcc_aesop' [force_step])

namespace GenericExpr

namespace Judge

def is_norm (ht : Judge (τ_c := τ_c) A τ) : IsNorm RedAff τ := by
  induction ht
  any_goals (
    intro ⟨_, h⟩
    cases h
    done)
  any_goals (exact Reduces.is_norm (by assumption))
  · intro ⟨_, h⟩
    cases h
    expose_names
    exact a_ih ⟨_, h_1⟩

def preservation (ht : Judge (τ_c := τ_c) A τ) (hr : RedAff A B) : Judge B τ := by
  induction ht generalizing B with
  | eq ht₁ ht₂ ih₁ ih₂ =>
    cases hr with
    | eq₀ h =>
      constructor
      · exact ih₁ h
      · assumption
    | eq₁ h =>
      constructor
      · assumption
      · exact ih₂ h
  | refl _ _ _ ih =>
    cases hr with
    | refl₀ =>
      constructor
      · exact ih (by assumption)
      · assumption
      · expose_names
        unfold refl.type at *
        exact a_1.push_head (.congrFun (.pi₁ (.quot₁ (.pi₀ (.map₀ h_1)))))
          |>.push_head (.congrFun (.pi₁ (.quot₁ (.pi₁ (.eql₀ h_1)))))
  | eql _ _ _ ih =>
    cases hr with
    | eql₀ =>
      constructor
      · exact ih (by assumption)
      · assumption
      · expose_names
        unfold eql.type at *
        exact a_1.push_head (.congrFun (.pi₁ (.quot₁ (.pi₀ (.map₀ h_1)))))
          |>.push_head (.congrFun (.pi₁ (.quot₁ (.pi₁ (.curr₁ (.map₀ h_1))))))
          |>.push_head (.congrFun (.pi₁ (.quot₁ (.pi₁ (.curr₂ (.quot₀ (.coup₀ (.map₀ h_1))))))))
  | id _ _ ih =>
    cases hr with
    | id₀ =>
      constructor
      · exact ih (by assumption)
      · expose_names
        unfold id.type at *
        exact a.push_head (.congrArg h_1)
          |>.push_head (.congrFun (.pi₁ (.curr₂ (.quot₁ h_1))))
  | comp _ _ _ _ _ _ ih₁ ih₂ =>
    cases hr with
    | comp₀ =>
      constructor
      · assumption
      · exact ih₂ (by assumption)
      repeat assumption
    | comp₁ =>
      constructor
      · exact ih₁ (by assumption)
      repeat assumption
      · unfold comp.type at *
        expose_names
        exact a_3.push_head (.congrFun (.pi₁ (.quot₁ (.comp₁ h_2))))
  | comp' _ _ _ _ _ _ _ ih₁ ih₂ =>
    cases hr with
    | comp'₀ =>
      constructor
      · assumption
      · assumption
      · exact ih₂ (by assumption)
      repeat assumption
    | comp'₁ =>
      constructor
      · exact ih₁ (by assumption)
      repeat assumption
      · unfold comp'.type at *
        expose_names
        exact a_4.push_head (.congrFun (.pi₁ (.quot₁ (.comp'₁ h_2))))
  | comp₂ _ _ _ _ _ ih₁ ih₂ =>
    cases hr with
    | comp₂₀ =>
      constructor
      · assumption
      · assumption
      · exact ih₂ (by assumption)
      repeat assumption
    | comp₂₁ =>
      constructor
      · exact ih₁ (by assumption)
      repeat assumption
      · unfold comp.type at *
        expose_names
        exact a_2.push_head (.congrFun (.pi₁ (.quot₁ (.comp₂₁ h_2))))
  | coup _ _ _ ih =>
    cases hr
    case _ h =>
      constructor
      · exact ih h
      repeat assumption
  | fstc _ _ _ ih =>
    cases hr
    case _ h =>
      constructor
      · exact ih h
      repeat assumption
      · expose_names
        unfold fstc.type at a_1
        exact a_1.push_head (.congrArg (.coup₀ h))
  | sndc _ _ _ ih =>
    cases hr
    case _ h =>
      constructor
      · exact ih h
      repeat assumption
      · expose_names
        unfold sndc.type at a_1
        exact a_1.push_head (.congrArg (.coup₀ h))
          |>.push_head (.congrFun (.pi₁ (.quot₁ (.comp'₀ h))))
          |>.push_head (.congrFun (.pi₁ (.quot₁ (.comp'₁ (.fstc₀ h)))))
  | sigma _ _ _ _ _ _ ih =>
    cases hr
    case _ h =>
      expose_names
      have ha := ih h
      have hb := a_1.push_head h
      refine Judge.sigma ha a ?_ hb a_2 ?_
      repeat assumption
    case _ h =>
      expose_names
      have ha := a_ih h
      constructor <;> assumption
  | mk =>
    cases hr
    case _ h =>
      expose_names
      have ha := a_ih_1 (by assumption)
      have hb := a_1.push_head (.congrFun h)
      have hc := a_2.push_head (.coup₀ h)
      constructor <;> assumption
    case _ h =>
      expose_names
      have ha := a_ih (by assumption)
      have hb := a_1.push_head (.congrArg h)
      constructor <;> assumption
    case _ h =>
      expose_names
      have ha := a_ih_2 (by assumption)
      constructor <;> assumption
  | curr =>
    cases hr
    case curr₀ =>
      expose_names
      have ha := a_ih (by assumption)
      have hb := a_4.push_head h_3
      constructor <;> assumption
    case curr₁ =>
      expose_names
      have ha := a_1.push_head (.coup₀ (by assumption))
      unfold curr.type at a_4
      have hb := a_5.push_head (.congrFun (.pi₁ (.quot₁ (.pi₀ h_3))))
        |>.push_head (.congrFun (.pi₁ (.quot₁ (.pi₁ (.curr₁ h_3)))))
      have hc := a_ih_1 h_3
      constructor <;> assumption
    case curr₂ =>
      expose_names
      have ha := a_ih_2 (by assumption)
      constructor <;> assumption
  | curr' =>
    cases hr
    case curr'₀ =>
      expose_names
      have ha := a_ih h_3
      have hb := a_4.push_head h_3
      constructor <;> assumption
    case curr'₁ =>
      expose_names
      have ha := a_1.push_head (.bang₀ (.coup₀ (by assumption)))
      unfold curr.type at a_4
      have hb := a_5.push_head (.congrFun (.pi₁ (.quot₁ (.pi₀ (.map₀ h_3)))))
        |>.push_head (.congrFun (.pi₁ (.quot₁ (.pi₁ (.curr'₁ h_3)))))
      have hc := a_ih_1 h_3
      constructor <;> assumption
    case curr'₂ =>
      expose_names
      have ha := a_ih_2 (by assumption)
      constructor <;> assumption
  | unmap | box | bang | fmap | map =>
    cases hr
    expose_names
    have ha := a_ih h_1
    constructor <;> assumption
  | eval =>
    cases hr
    case eval₀ =>
      expose_names
      unfold Eval.type at *
      have ha := a_ih_1 (by assumption)
      have hb := a.push_head h_3
      have hc := a_6.push_head (.congrFun (.pi₁ (.quot₁ (.eval₀ h_3))))
      constructor <;> assumption
    case eval₁ =>
      expose_names
      unfold Eval.type at *
      have ha := a_1.push_head h_3
      have hb := a_6.push_head (.congrArg (.coup₀ h_3))
        |>.push_head (.congrFun (.pi₁ (.quot₁ (.eval₁ h_3))))
      have hc := a_ih_2 h_3
      constructor <;> assumption
    case eval₂ =>
      expose_names
      unfold Eval.type at *
      have hc := a_ih h_3
      constructor <;> assumption
  | quot =>
    cases hr
    case quot₀ =>
      expose_names
      have ha := a_ih_1 h_2
      have hb := a.push_head h_2
      constructor <;> assumption
    case quot₁ =>
      expose_names
      have ha := a_ih h_2
      constructor <;> assumption
  | pair =>
    cases hr
    case pair₀ =>
      expose_names
      have ha := a_1.push_head h_2
      constructor <;> assumption
    case pair₁ =>
      expose_names
      have ha := a_ih h_2
      constructor <;> assumption
    case pair₂ =>
      expose_names
      have ha := a_ih_1 h_2
      constructor <;> assumption
  | pi =>
    cases hr
    case pi₀ =>
      expose_names
      have ha := a_ih h_2
      have hb := a_1.push_head h_2
      constructor <;> assumption
    case pi₁ =>
      expose_names
      have ha := a_ih_1 h_2
      constructor <;> assumption
  | tintro | bot | top | sort => cases hr
  | app =>
    cases hr with
    | congrFun hr =>
      expose_names
      have ha := a_ih hr
      constructor <;> assumption
    | congrArg hr =>
      expose_names
      have ha := a_ih_1 hr
      have hb := a_1.push_head (.congrArg hr)
      constructor <;> assumption
    | curr =>
      expose_names
      apply GenericExpr.Judge.preservation.extracted_1 <;> assumption

end Judge

end GenericExpr
