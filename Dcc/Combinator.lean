class Combinator (α : Type) where
  -- Arity of only type points
  TyArity : α → ℕ → Prop
  -- Term arity excluding type points
  Arity   : α → ℕ → Prop

  
