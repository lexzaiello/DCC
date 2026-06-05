import Dcc.Judge
import Dcc.Relation
import Dcc.Metatheory.Congr
import Dcc.Aff.Red

namespace Reduces

-- might need to strengthen this
theorem eql (h : Reduces (DCC (Eql(f_α) env &(x))) B) : ∃ x', (B = (DCC (x' = x'))) := by
  match h with
  | ⟨ha, hb, hc, hd⟩ =>
    match ha.cases_head with
    | .inl h =>
      cases h
      exact (hb ⟨_, .eql⟩).elim
    | .inr ⟨_, h₁, h₂⟩ =>
      cases h₁ with
      | eql =>
        match h₂.cases_head with
        | .inl h =>
          cases h
          match hc.cases_head with
          | .inl h =>
            cases h
            exact ⟨_, rfl⟩
          | .inr ⟨_, h₁, h₂⟩ => cases h₁
        | .inr ⟨_, h₁, h₂⟩ =>
          cases h₁ with
          | eql' h =>
            
            sorry
      | congrFun h =>
        cases h with
        | congrFun h => cases h
        | congrArg h =>
          rename_i x'
          have h_dec := RedAff.instRedRel.decreasing h
          have h_dec' : (DCC (Eql(f_α) x' x)).size < (DCC (Eql(f_α) env x)).size := by
            grind
          exact eql ⟨h₂, hb, hc, hd⟩
      | congrArg h =>
        rename_i x'
        have h_dec := RedAff.instRedRel.decreasing h
        have h_dec' : (DCC (Eql(f_α) env x')).size < (DCC (Eql(f_α) env x)).size := by
          grind
        exact eql ⟨h₂, hb, hc, hd⟩
termination_by (DCC (Eql(f_α) env x)).size

end Reduces
