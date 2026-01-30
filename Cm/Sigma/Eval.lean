import Cm.Sigma.Ast

open Expr

inductive is_step : Expr → Expr → Prop
  | sapp   : is_step ($ ::[α, β], x) ($ x, β)
  | nil    : is_step ($ (nil _o), α, _x) α
  | id     : is_step ($ (.id _o), _α, x) x
  | const  : is_step ($ (.const _o _p), _α, _β, c, _x) c
  | const' : is_step ($ (.const' _o _p), _α, _β, c, _x) c
  | both   : is_step ($ (.both _o _p _q), _α, _β, _γ, f, g, x) ($ ($ f, x), ($ g, x))
  | both'  : is_step ($ (.both _o _p _q), _α, f, g, x) ::[($ f, x), ($ g, x)]
  | left   : is_step f f'
    → is_step ($ f, x) ($ f', x)
  | right  : is_step x x'
    → is_step ($ f, x) ($ f, x')
