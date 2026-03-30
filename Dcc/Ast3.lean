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

inductive CTy where
  | sort  : Level     → CTy
  | arrow : CTy → CTy → CTy
  | prod  : CTy → CTy → CTy

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
  | ty   : CTy    → CcExpr

inductive Expr where
  | cc  : CcExpr → Expr
  | sk  : SkComb → Expr
  | app : Expr   → Expr → Expr

declare_syntax_cat ccexpr
declare_syntax_cat cty
declare_syntax_cat skexpr
declare_syntax_cat expr

syntax "(" ccexpr* ")"     : ccexpr
syntax "(" skexpr* ")"     : skexpr
syntax "#(" term ")"       : ccexpr
syntax "Id(" cty ")"       : ccexpr
syntax ident               : cty
syntax "#(" term ")"       : cty
syntax "Fst"               : ccexpr
syntax "Snd"               : ccexpr
syntax "App"               : ccexpr
syntax "Λ(" ccexpr ")"     : ccexpr
syntax ccexpr "∘" ccexpr   : ccexpr
syntax "Fst(" cty,* ")"    : ccexpr
syntax "Snd(" cty,* ")"    : ccexpr
syntax "App(" cty,* ")"    : ccexpr
syntax "Id"                : ccexpr
syntax cty "×" cty         : cty
syntax cty "→" cty         : cty
syntax "Sort" term         : cty
syntax "⟨" ccexpr,* "⟩"    : ccexpr
syntax "(" ccexpr,* ")"    : ccexpr
syntax ident               : ccexpr
syntax cty                 : ccexpr
syntax ident               : cty

syntax "CC" ccexpr         : term
syntax "CTy" cty           : term

syntax "K.{" term "}" : skexpr
syntax "K'.{" term "}" : skexpr
syntax "S.{" term "}" : skexpr

syntax "(" expr* ")" : expr
syntax "#(" term ")" : expr
syntax skexpr        : expr
syntax ccexpr        : expr
syntax ident : expr

syntax "SK" expr     : term

macro_rules
  | `(SK $e:ccexpr)              => `(CC $e)
  | `(CC $t:cty)                 => `(CExpr.ty (CTy $t))
  | `(CTy Sort $m:term)          => `(CTy.sort $m)
  | `(CTy $α:cty × $β:cty)       => `(CTy.prod (CTy $α) (CTy $β))
  | `(CTy $α:cty → $β:cty)       => `(CTy.arrow (CTy $α) (CTy $β))
  | `(CC Id($α:cty))             => `(CcExpr.id (CTy $α))
  | `(CC Fst($α:cty, $β:cty))    => `(CcExpr.fst (CTy $α) (CTy $β))
  | `(CC Snd($α:cty, $β:cty))    => `(CcExpr.snd (CTy $α) (CTy $β))
  | `(CC Fst)                    => `(CcExpr.fst')
  | `(CC Snd)                    => `(CcExpr.snd')
  | `(CC Id)                     => `(CcExpr.id')
  | `(CC Λ($e:ccexpr))           => `(CcExpr.curr (CC $e))
  | `(CC ⟨$x:ccexpr, $y:ccexpr⟩) => `(CcExpr.pair (CC $x) (CC $y))
  | `(CC ($x:ccexpr, $y:ccexpr)) => `(CcExpr.coup (CC $x) (CC $y))
  | `(CC $f:ccexpr ∘ $g:ccexpr)  => `(CcExpr.comp (CC $f) (CC $g))
  | `(SK #($t:term))             => `($t)
  | `(CTy #($t:term))            => `($t)
  | `(CC #($t:term))             => `($t)
  | `(SK $idt:ident)             => `($idt:term)
  | `(CC $idt:ident)             => `($idt:term)
  | `(CTy $idt:ident)            => `($idt:term)
