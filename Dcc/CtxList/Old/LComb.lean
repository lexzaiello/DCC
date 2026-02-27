import Mathlib.Data.Nat.Notation

inductive Idx where
  | zero : Idx
  | succ : Idx

inductive UExpr where
  | lam : 
