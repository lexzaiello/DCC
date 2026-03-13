import Dcc.Ast

open Std (ToFormat Format)
open Std.ToFormat (format)

namespace Expr

def eval (e : Expr) : Except Format Expr :=
  match e with
  | ⸨(K _m _n) _α _β x _y⸩ => pure x
  | ⸨(K' _m _n) _α _β x _y⸩ => pure x
  | ⸨(S _m _n _o) _α _β _γ x y z⸩ => return ⸨⸨x z⸩ ⸨y z⸩⸩
  | ⸨((Π' m) α, β) x⸩ => return (Π' m) ⸨α x⸩, ⸨β x⸩
  | ⸨next f _x⸩ => pure f
  | ⸨read e⸩ => pure e
  | ⸨${π} f g x⸩ => pure ⸨π ⸨f x⸩ ⸨g x⸩⸩
  | e => .error <| "stuck: " ++ (format e)

end Expr
