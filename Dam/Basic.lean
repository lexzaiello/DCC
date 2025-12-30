import Mathlib.Data.Nat.Notation

inductive Term where
  -- The initial object
  | init : Term
  | i    : Term
  | k    : Term
  | s    : Term
  | mi   : Term
  | mk   : Term
  | ms   : Term
  | ty   : ℕ
    → Term
  | app  : Term
    → Term
    → Term

notation "𝟙" => Term.init

abbrev Flag := ℕ
abbrev Code := ℕ

def FTy  : Flag := 1
def FApp : Flag := 2

def WithFlag (F : Flag) : Code → Code := (· * 10 + F)

def Term.code : Term → Code
  | 𝟙        => 0
  | .i       => 1
  | .k       => 2
  | .s       => 3
  | .mi      => 4
  | .mk      => 5
  | .ms      => 6
  | .ty n    => WithFlag FTy n
  | .app f x => WithFlag FApp <|
    (code f + code x) * (code f + code x + 1) / 2 + (code x)

def Term.decode : Code → Term
  | 1 => .i
  | 2 => .k
  | 3 => .s
  | 4 => .mi
  | 5 => .mk
  | 6 => .ms
  | n =>
    if n % 10 == 1 then
      .ty (n / 10)
    else if n % 10 == 2 then
      
