import Mathlib.Data.Nat.Notation

-- Infinite sort universe hierarchy
abbrev Level := ℕ

inductive GenericExpr.{u} (τ : Type u) where
  | top     : GenericExpr τ
  | bot     : GenericExpr τ
  | tintro  : GenericExpr τ
  | sort    : Level → GenericExpr τ
  | map     : GenericExpr τ  → GenericExpr τ
  | fmap    : GenericExpr τ  → GenericExpr τ
  | bang    : GenericExpr τ  → GenericExpr τ
  | box     : GenericExpr τ  → GenericExpr τ
  | unmap   : GenericExpr τ  → GenericExpr τ
  | eql     : GenericExpr τ  → GenericExpr τ
  | refl    : GenericExpr τ  → GenericExpr τ
  | fstc    : GenericExpr τ  → GenericExpr τ
  | id      : GenericExpr τ  → GenericExpr τ
  | sndc    : GenericExpr τ  → GenericExpr τ
  | eval    : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | curr    : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | curr'   : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | pair    : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | mkc     : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | eq      : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | comp    : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | quot    : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | pi      : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | sigma   : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | coup    : GenericExpr τ  → GenericExpr τ
  | app     : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | const   : τ              → GenericExpr τ
  | dom     : GenericExpr τ  → GenericExpr τ
  | hole    : ℕ              → GenericExpr τ
deriving BEq, DecidableEq, Inhabited, Repr
