import Dcc.Tactic.Simp

example : IsStep ⟪K'.{[1, 1]} (Sort 1) (Sort 1) (Sort 0) (Sort 0)⟫ ⟪Sort 0⟫ := by
  simp
