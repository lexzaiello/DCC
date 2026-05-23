import Dcc.Attrs

namespace _tmp

@[dcc_step]
axiom ex₀ : 10 = 11

example : 10 = 11 := by
  dcc_simp_all

@[dcc_force_infer]
axiom ex' : 2 = 3

example : 2 = 3 := by
/-
∶ is for the simp set that "dangerously"
(as in causes nested timeout whnf) reduce simps about the
infer function

Try this:
  [apply] simp_all only [ex']
-/
  dcc_simp_all? ∶

@[dcc_force_reduce]
axiom ex'' : 5 = 8

@[dcc_force_reduce]
axiom ex''' : 6 = 4

example : 5 = 8 := by
  dcc_simp_all?
  -- does not close the goal, since ! is required to run "dangerous" reduction
  -- simps
  sorry

example : 5 = 8 := by
/-
27:2:
Try this:
  [apply] simp_all only [ex'']
-/
  dcc_simp_all? !

example : 5 = 8 := by
/-
27:2:
Try this:
  [apply] simp_all only [ex'']
-/
  dcc_simp? !

@[dcc_force_reduce]
axiom id_ex {x : Nat} : id x = 5

example : 2 = 3 := by
  have h_6_refl : id 6 = 6 := rfl
/-
27:2:
Try this:
  [apply] simp_all only [ex'']
-/
  dcc_simp? ! at h_6_refl
  -- does not close the goal, since this requires our axiom
  -- registered to force infer
  -- however, h_6_refl : True, since we registered id_ex
  sorry

end _tmp
