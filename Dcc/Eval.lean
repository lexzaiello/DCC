import Dcc.Ast
import Mathlib.Data.Nat.Notation

open Std (ToFormat Format)
open Std.ToFormat (format)

namespace Expr

def eval (e : Expr) : Except Format Expr :=
  match e with
  | ⸨K.{[_m, _n]} _α _β x _y⸩ => pure x
  | ⸨K'.{[_m, _n]} _α _β x _y⸩ => pure x
  | ⸨S.{[_m, _n, _o]} _α _β _γ x y z⸩ => return ⸨⸨x z⸩ ⸨y z⸩⸩
  | ⸨(Π.{[m]} α, β) x⸩ => return Π.{[m]} ⸨α x⸩, ⸨β x⸩
  | ⸨next f _x⸩ => pure f
  | ⸨read e⸩ => pure e
  | ⸨$ π f g x⸩ => pure ⸨π ⸨f x⸩ ⸨g x⸩⸩
  | e => .error <| "stuck: " ++ (format e)


/-
For parallel reduction:
- only proceed with the general app case if there are fewer arguments
to the innermost spine than its arity requires
-/
inductive Arity : Expr → ℕ → Prop
  | pi    : Arity (Π.{[m]} α, β) 1
  | k     : Arity (K.{[m, n]}) 2
  | k'    : Arity (K'.{[m, n]}) 2
  | s     : Arity (S.{[m, n, o]}) 3
  | next  : Arity next 2
  | read  : Arity read 1
  | next' : Arity $ 4
  | app   : Arity f n.succ → Arity ⸨f x⸩ n

abbrev Head  := Expr
abbrev Spine := List Expr

inductive Profile : Expr → Head → Spine → Prop
  | pi   : Profile (Π.{[m]} α, β) (Π.{[m]} α, β) []
  | comb : Profile (.comb c) (.comb c) []
  | app  : Arity e (Nat.succ n) -- e must be able to accept another arg
    → Profile e f args -- f represents the innermost combinator
    → Arity ⸨e x⸩ n -- Trivial, but useful for induction
    → Profile ⸨e x⸩ f (args ++ [x])

inductive ParRed : Expr → Expr → Prop
  | k         : ParRed x x' → ParRed ⸨K.{[m, n]} α β x y⸩ x'
  | k'        : ParRed x x' → ParRed ⸨K'.{[m, n]} α β x y⸩ x
  | s         : ParRed x x' → ParRed y y' → ParRed z z'
    → ParRed ⸨S.{[m, n, o]} α β γ x y z⸩ ⸨⸨x' z'⸩ ⸨y' z'⸩⸩
  | next      : ParRed f f' → ParRed ⸨next f x⸩ f'
  | read      : ParRed e e' → ParRed ⸨read e⸩ e'
  | pi        : ParRed α α' → ParRed β β' → ParRed x x'
    → ParRed (Π.{[m]} α, β) (Π.{[m]} ⸨α' x'⸩, ⸨β' x'⸩)
  | app'      : ParRed π π' → ParRed f f'
    → ParRed g g' → ParRed x x'
    → ParRed ⸨$ π f g x⸩ ⸨π' ⸨f' x'⸩ ⸨g' x'⸩⸩
  | refl_comb : ParRed (.comb c) (.comb c)
  | pi_val    : ParRed α α' → ParRed β β' → ParRed (Π.{[m]} α, β) (Π.{[m]} α', β')

end Expr
