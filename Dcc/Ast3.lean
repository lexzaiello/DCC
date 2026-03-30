import Mathlib.Data.Nat.Notation
import Batteries.Data.String.Matcher
import Mathlib.Tactic
open Std (ToFormat Format)
open Std.ToFormat (format)

-- Infinite sort universe hierarchy
abbrev Level := ℕ

inductive SkComb where
  | K'     : Level → Level → SkComb
  | K      : Level → Level → SkComb
  | S      : Level → Level → Level → SkComb
deriving BEq, Repr, DecidableEq

inductive CTy where
  | sort  : Level     → CTy
  | arrow : CTy → CTy → CTy
  | prod  : CTy → CTy → CTy
deriving BEq, Repr, DecidableEq

inductive CcExpr where
  | id   : CTy → CcExpr
  | id'  : CcExpr
  | comp : CcExpr → CcExpr → CcExpr
  | pair : CcExpr → CcExpr → CcExpr
  | coup : CcExpr → CcExpr → CcExpr
  | fst  : CTy    → CTy    → CcExpr
  | fst' : CcExpr
  | snd  : CTy    → CTy    → CcExpr
  | snd' : CcExpr
  | curr : CcExpr → CcExpr
  | App  : CTy    → CTy    → CcExpr
  | App' : CcExpr
  | app  : CcExpr → CcExpr → CcExpr
deriving BEq, Repr, DecidableEq

inductive Expr where
  | cc  : CcExpr → Expr
  | sk  : SkComb → Expr
  | app : Expr   → Expr → Expr

declare_syntax_cat ccexpr
declare_syntax_cat cty
declare_syntax_cat skexpr
declare_syntax_cat expr

syntax "(" cty ")"             : cty
syntax "(" ccexpr+ ")"         : ccexpr
syntax "#(" term ")"           : ccexpr
syntax:max "Id(" cty ")"       : ccexpr
syntax:50 ident                : cty
syntax "#(" term ")"           : cty
syntax "Fst"                   : ccexpr
syntax "Snd"                   : ccexpr
syntax "App"                   : ccexpr
syntax:max (priority := high) "Λ(" ccexpr ")"  : ccexpr
syntax ccexpr "∘" ccexpr       : ccexpr
syntax:max "Fst(" cty,* ")"    : ccexpr
syntax:max "Snd(" cty,* ")"    : ccexpr
syntax:max "App(" cty,* ")"    : ccexpr
syntax "Id"                    : ccexpr
syntax cty "×" cty             : cty
syntax cty "→" cty             : cty
syntax "Sort" term             : cty
syntax (priority := high) "⟨" ccexpr,* "⟩" : ccexpr
syntax (priority := high) "(" ccexpr,* ")" : ccexpr
syntax:40 ident                : ccexpr
syntax cty                     : ccexpr
syntax:30 ident                : expr

syntax "CC" ccexpr             : term
syntax "CTY" cty               : term

syntax "K.{" term "}" : skexpr
syntax "K'.{" term "}" : skexpr
syntax "S.{" term "}" : skexpr

syntax:lead (priority := low) "(" expr+ ")" : expr
syntax:max (priority := high) "(" expr expr+ ")" : expr
syntax "#(" term ")" : expr
syntax skexpr        : expr
syntax ccexpr        : expr

syntax "SK" expr     : term

macro_rules
  | `(SK ($f:expr $x:expr))                 => `(Expr.app   (SK $f:expr)   (SK $x:expr))
  | `(SK ($f:expr $x:expr $xs:expr*))       => `(SK (($f:expr $x:expr) $xs:expr*))
  | `(CC ($f:ccexpr $x:ccexpr))             => `(CcExpr.app (CC $f:ccexpr) (CC $x:ccexpr))
  | `(CC ($f:ccexpr $x:ccexpr $xs:ccexpr*)) => `(CC (($f:ccexpr $x:ccexpr) $xs:ccexpr*))
  | `(CC Λ($e:ccexpr))                      => `(CcExpr.curr (CC $e))
  | `(CC ⟨$x:ccexpr, $y:ccexpr⟩)            => `(CcExpr.pair (CC $x) (CC $y))
  | `(CC ($x:ccexpr, $y:ccexpr))            => `(CcExpr.coup (CC $x) (CC $y))
  | `(SK S.{[$m, $n, $o]})                  => `(Expr.sk (SkComb.S $m $n $o))
  | `(SK K.{[$m, $n]})                      => `(Expr.sk (SkComb.K $m $n))
  | `(SK K'.{[$m, $n]})                     => `(Expr.sk (SkComb.K' $m $n))
  | `(CTY ($e:cty))                         => `(CTY $e)
  | `(CTY Sort $m:term)                     => `(CTy.sort $m)
  | `(CTY $α:cty × $β:cty)                  => `(CTy.prod  (CTY $α) (CTY $β))
  | `(CTY $α:cty → $β:cty)                  => `(CTy.arrow (CTY $α) (CTY $β))
  | `(CC Id($α:cty))                        => `(CcExpr.id (CTY $α))
  | `(CC Fst($α:cty, $β:cty))               => `(CcExpr.fst (CTY $α) (CTY $β))
  | `(CC Snd($α:cty, $β:cty))               => `(CcExpr.snd (CTY $α) (CTY $β))
  | `(CC App($α:cty, $β:cty))               => `(CcExpr.App (CTY $α) (CTY $β))
  | `(CC App)                               => `(CcExpr.App')
  | `(CC Fst)                               => `(CcExpr.fst')
  | `(CC Snd)                               => `(CcExpr.snd')
  | `(CC Id)                                => `(CcExpr.id')
  | `(CC $f:ccexpr ∘ $g:ccexpr)             => `(CcExpr.comp (CC $f:ccexpr) (CC $g:ccexpr))
  | `(SK #($t:term))                        => `($t)
  | `(CTY #($t:term))                       => `($t)
  | `(CC #($t:term))                        => `($t)
  | `(CC $idt:ident)                        => `($idt:term)
  | `(CTY $idt:ident)                       => `($idt:term)
  | `(SK $idt:ident)                        => `($idt:term)
  | `(CC $t:cty)                            => `(CcExpr.ty (CTY $t))
  | `(CC ($t:cty))                          => `(CcExpr.ty (CTY $t))
  | `(CC ($c:ccexpr))                       => `(CC $c)
  | `(SK ($e:expr))                         => `(SK $e)
  | `(SK $e:ccexpr)                         => `(Expr.cc (CC $e))

def CTy.toFormat (e : CTy) : Format :=
  match e with
  | (CTY Sort m) => s!"Sort {m}"
  | (CTY α → β)  => α.toFormat ++ " → " ++ β.toFormat
  | (CTY α × β)  => α.toFormat ++ " × " ++ β.toFormat

def CcExpr.toFormat (e : CcExpr) : Format :=
  match e with
  | (CC Id(α))     => "Id(" ++ α.toFormat ++ ")"
  | (CC Id)        => "Id"
  | (CC Fst(α, β)) => "Fst(" ++ α.toFormat ++ ", " ++ β.toFormat ++ ")"
  | (CC Fst) => "Fst"
  | (CC Snd(α, β)) => "Snd(" ++ α.toFormat ++ ", " ++ β.toFormat ++ ")"
  | (CC Snd) => "Snd"
  | (CC App(α, β)) => "App(" ++ α.toFormat ++ ", " ++ β.toFormat ++ ")"
  | (CC App)       => "App"
  | (CC Λ(e))      => "Λ(" ++ e.toFormat ++ ")"
  | (CC ⟨a, b⟩)    => .bracket "⟨" (a.toFormat ++ ", " ++ b.toFormat) "⟩"
  | (CC (a, b))    => .bracket "(" (a.toFormat ++ ", " ++ b.toFormat) ")"
  | (CC f ∘ g)     => f.toFormat ++ " ∘ " ++ g.toFormat
  | (CC (f x))     => .bracket "(" (f.toFormat ++ " " ++ x.toFormat) ")"

def Expr.toFormat (e : Expr) : Format :=
  match e with
  | .cc e => e.toFormat
  | SK S.{[m, n, o]} => "S.{[" ++ s!"{m}, {n}, {o}" ++ "]}"
  | SK K.{[m, n]} => "K.{[" ++ s!"{m}, {n}" ++ "]}"
  | SK K'.{[m, n]} => "K'.{[" ++ s!"{m}, {n}" ++ "]}"
  | SK (f x)       => .bracket "(" (f.toFormat ++ " " ++ x.toFormat) ")"

instance CTy.instToFormat : Std.ToFormat CTy := ⟨CTy.toFormat⟩
instance CcExpr.instToFormat : Std.ToFormat CcExpr := ⟨CcExpr.toFormat⟩
instance Expr.instToFormat : Std.ToFormat Expr := ⟨Expr.toFormat⟩
instance : ToString Expr := ⟨toString ∘ Expr.toFormat⟩
instance : ToString CcExpr := ⟨toString ∘ CcExpr.toFormat⟩
instance : ToString CTy := ⟨toString ∘ CTy.toFormat⟩
