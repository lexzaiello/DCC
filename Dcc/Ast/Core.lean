import Mathlib.Data.Nat.Notation

-- Infinite sort universe hierarchy
abbrev Level := ℕ

inductive Expr where
  /-
  (≃.Ind motive x) (Cong.Mk toFun invFun h_comp_id h_id_comp) = x toFun invFun h_comp_id h_id_comp
  -/
  | ind_bool    : Expr → Expr → Expr → Expr -- Bool.Ind motive case_true case_false : (x : Bool) → ...
  | ind_bot     : Expr → Expr -- (⊥.Ind motive) (<not possible> : ⊥) : motive ⊥
  | bool        : Expr
  | true        : Expr
  | false       : Expr
  | top         : Expr
  | bot         : Expr
  | tintro      : Expr
  | sort        : Level → Expr
  | map         : Expr  → Expr
  | fmap        : Expr  → Expr
  | bang        : Expr  → Expr
  | box         : Expr  → Expr
  | unbox       : Expr  → Expr
  | eql         : Expr  → Expr
  | refl        : Expr  → Expr
  | fstc        : Expr  → Expr
  | sndc        : Expr  → Expr
  | id          : Expr  → Expr
  | swap        : Expr  → Expr → Expr
  | eval        : Expr  → Expr → Expr → Expr
  | curr        : Expr  → Expr → Expr → Expr
  | curr'       : Expr  → Expr → Expr → Expr
  | pair        : Expr  → Expr → Expr → Expr
  | mkc         : Expr  → Expr → Expr → Expr
  | eq_mk       : Expr  → Expr
  | eq          : Expr  → Expr → Expr → Expr
  | comp        : Expr  → Expr → Expr
  | quot        : Expr  → Expr → Expr
  | pi          : Expr  → Expr → Expr
  | sigma       : Expr  → Expr → Expr
  | sigma'      : Expr  → Expr → Expr
  | app         : Expr  → Expr → Expr
  | hole        : ℕ              → Expr
  | hole_ty     : Expr  → Expr
deriving BEq, DecidableEq, Inhabited
