import Dcc.Cubical.Ast

inductive CIsStep : CExpr → CExpr → Prop
  | transp₁ : CIsStep c⟪transp.{[m]} A i1 a⟫ a
  | transpu : CIsStep c⟪transp.{[m.succ]} _U i0 (Sort m)⟫ c⟪Sort m⟫
  | eq      : CIsStep c⟪=.{[m]} A⟫ c⟪PathP.{[m]} (KI.{[m.succ]} (Sort m) A)⟫
