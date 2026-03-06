import Dcc.Syn.Ast

inductive Expr.red : Expr → Expr → Prop
  | head : red SK(0 (quote (f x))) SK(quot f)
  | tail : red SK((tail xs) fn (quote (f x))) SK(xs fn (quote 
