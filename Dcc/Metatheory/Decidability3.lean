import Dcc.Judge3

variable {τ_c : Type u}
variable [DecidableEq τ_c]
variable [BEq τ_c]

namespace GenericExpr

namespace Judge3

def Judge.complete (h : Judge (τ_c := τ_c) e τ) : e.infer = .ok ⟨τ, h⟩ := by
  induction h
  case eq =>
    dsimp only [infer]
    dcc_aesop!
  case eql | refl =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_1.read_complete, a_2.eq]
    grind
  case id =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_1.eq, a_2.eq]
    grind
  case comp =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_3.eq, a_5.eq, a_4.eq, a_2.eq]
    grind
  case comp₂ =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_3.eq, a_4.eq, a_1.complete]
    grind
  case comp' =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_3.eq, a_4.eq, a_1.eq, a_5.eq, a_1.complete, a_3.complete, a_6.eq]
    grind
  case coup =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_1.eq, a_1.complete, a_2.eq]
    grind
  case sndc | fstc =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_1.read_complete, a_2.eq, a_3.eq]
    grind
  case sigma =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_1.read_complete, a_3.complete, a_4.eq]
    grind
  case mk =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_ih_2, a_3.complete, a_3.eq, a_5.eq, a_2.read₁_complete]
    grind
  case curr' | curr =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_3.complete, a_3.eq, a_5.eq, a_2.complete, a_2.eq, a_4.eq, a_6.eq]
    grind
  case map =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_2.eq, a_1.read_complete]
    grind
  case fmap =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_2.eq, a_1.eq]
    grind
  case eval =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_ih_2, a_1.eq, a_2.eq, a_5.eq, a_6.eq, a_7.eq]
    grind
  case quot =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_2.eq, a_3.eq]
    grind
  case pair =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_1.eq, a_3.eq, a_4.eq, a_5.eq, a_6.eq, a_7.eq, a_8.eq]
    grind
  case pi =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_1.read_complete, a_3.eq, a_5.eq]
    cases a_3.complete
    cases a_5.complete
    simp only [a_4.complete]
  case tintro | top | bot | sort => dsimp only [infer]
  case box | bang =>
    expose_names
    dsimp only [infer]
    simp only [a_ih]
  case unmap =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_1.eq, a_2.eq]
    grind
  case unbox =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_1.eq]
    grind
  case app =>
    expose_names
    dsimp only [infer]
    simp only [a_ih, a_ih_1, a_1.eq, a_3.eq, a_4.eq]
    cases a_1.complete
    cases a_3.complete
    cases a_4.complete
    simp only [h.complete]

end Judge3

end GenericExpr
