import Mathlib.Data.Nat.Notation

-- Infinite sort universe hierarchy
abbrev Level := ℕ

#check False.rec

inductive GenericExpr.{u} (τ : Type u) where
  /-
  (≃.Ind motive x) (Cong.Mk toFun invFun h_comp_id h_id_comp) = x toFun invFun h_comp_id h_id_comp
  -/
  | dup         : GenericExpr τ → GenericExpr τ → GenericExpr τ
  | ind_bool    : GenericExpr τ → GenericExpr τ → GenericExpr τ → GenericExpr τ -- Bool.Ind motive case_true case_false : (x : Bool) → ...
  | ind_bot     : GenericExpr τ → GenericExpr τ -- (⊥.Ind motive) (<not possible> : ⊥) : motive ⊥
  | bool        : GenericExpr τ
  | true        : GenericExpr τ
  | false       : GenericExpr τ
  | top         : GenericExpr τ
  | bot         : GenericExpr τ
  | tintro      : GenericExpr τ
  | sort        : Level → GenericExpr τ
  | bimap       : GenericExpr τ  → GenericExpr τ → GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | assoc       : GenericExpr τ  → GenericExpr τ → GenericExpr τ  → GenericExpr τ
  | map         : GenericExpr τ  → GenericExpr τ
  | fmap        : GenericExpr τ  → GenericExpr τ
  | bang        : GenericExpr τ  → GenericExpr τ
  | box         : GenericExpr τ  → GenericExpr τ
  | unbox       : GenericExpr τ  → GenericExpr τ
  | eql         : GenericExpr τ  → GenericExpr τ
  | refl        : GenericExpr τ  → GenericExpr τ
  | fstc        : GenericExpr τ  → GenericExpr τ  → GenericExpr τ
  | sndc        : GenericExpr τ  → GenericExpr τ  → GenericExpr τ
  | id          : GenericExpr τ  → GenericExpr τ
  | swap        : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | eval        : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | curr        : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | curr'       : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | pair        : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | mkc         : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | eq          : GenericExpr τ  → GenericExpr τ → GenericExpr τ → GenericExpr τ
  | comp        : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | quot        : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | pi          : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | sigma       : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | app         : GenericExpr τ  → GenericExpr τ → GenericExpr τ
  | const       : τ              → GenericExpr τ
  | hole        : ℕ              → GenericExpr τ
  | hole_ty     : GenericExpr τ  → GenericExpr τ
deriving BEq, DecidableEq, Inhabited
