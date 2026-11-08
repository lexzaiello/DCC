import Dcc.Judge

variable {τ_c : Type u}
variable [DecidableEq τ_c]
variable [BEq τ_c]

namespace GenericExpr

namespace Reduces

--def pi 

end Reduces

namespace Judge

theorem preservation (h : Judge (τ_c := τ_c) e τ) (hr : RedAff e e') : Nonempty (Judge e' τ) := by
  induction h generalizing e'
  any_goals (
    focus
    cases hr
    done)
  case eq =>
    expose_names
    cases hr with
    | eql' hr =>
      have h := a_ih hr
      cases h with
      | intro h =>
        constructor
        exact .eq h a_1
    | eqr' hr =>
      have h := a_ih_1 hr
      cases h with
      | intro h =>
        constructor
        exact .eq a h
  case coup =>
    expose_names
    cases hr with
    | coup h =>
      cases a_ih h with
      | intro h =>
        constructor
        exact .coup h a_1 a_2
  case mk =>
    expose_names
    cases hr with
    | sigl hr =>
      cases a_ih hr with
      | intro h =>
        constructor
        exact .mk h (by assumption) a_2 (a_3.push_head (.congrArg hr)) a_4 a_5
    | sigr hr =>
      cases a_ih_2 hr with
      | intro h =>
        constructor
        exact .mk a (by assumption) a_2 a_3 h a_5
  case map =>
    expose_names
    cases hr with
    | map₀ h =>
      cases a_ih h with
      | intro h =>
        constructor
        exact .map h a_1 a_2
  case pair =>
    expose_names
    cases hr with
    | pairl hr =>
      cases a_ih hr with
      | intro h =>
        constructor
        apply Judge.pair <;> assumption
    | pairr hr =>
      cases a_ih_1 hr with
      | intro h =>
        constructor
        apply Judge.pair <;> assumption
  case pi =>
    expose_names
    cases hr with
    | pil hr =>
      have ha := a_3.push_head hr
      cases a_ih hr with
      | intro hr' =>
        constructor
        apply Judge.pi
        any_goals (assumption)
    | pir hr =>
      cases a_ih_1 hr with
      | intro h =>
        constructor
        apply Judge.pi
        · exact a
        · exact a_1
        · exact h
        · exact a_3
        · exact a_4
        · exact a_5
  case bang =>
    expose_names
    cases hr with
    | bang h =>
      cases a_ih h with
      | intro h =>
        constructor
        apply Judge.bang
        assumption
  case app =>
    cases hr
    case eql =>
      expose_names
      cases a_3 with
      | box =>
        expose_names
        cases a_2 with
        | app =>
          expose_names
          cases a_6 with
          | eql =>
            expose_names
            simp [eql.type] at a_10
            
            sorry

end Judge

end GenericExpr
