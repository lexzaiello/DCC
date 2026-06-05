import Dcc.Attrs
import Dcc.Ast
import Dcc.Aff.Size
import Dcc.Relation
import Dcc.Metatheory.Value

/-
Normalization by evaluation is only used to reduce types via η-reduction.

i.e., TyValue
-/

namespace Semantic

mutual

inductive Neutral where
  | var   (idx : ℕ)             : Neutral
  | fstc  (f_β : Val)           : Neutral
  | sndc  (f_β : Val)           : Neutral
  | id    (α   : Val)           : Neutral
  | eql   (f_α : Val)           : Neutral
  | refl   (f_α : Val)          : Neutral
  | unbox (α   : Val)           : Neutral
  | app (f : Neutral) (x : Val) : Neutral
  | map (f : Val)               : Neutral
  | fmap (f : Val)              : Neutral
  | pair (β x y : Val)          : Neutral
  | eval (α β x : Val)          : Neutral
  | sigma (α β  : Val)          : Neutral
  | quot (β x : Val)            : Neutral
  | comp' (f g : Val)           : Neutral
  | comp (f g : Val)            : Neutral
  | comp₂ (f g : Val)           : Neutral
  | curr (α β x : Val)          : Neutral
  | curr' (α β x : Val)         : Neutral
  | eq (x y : Val)              : Neutral
  | bang (x : Val)              : Neutral
  | boxed (x : Val)             : Neutral
  | coup  (β x y : Val)         : Neutral
  | t_coup (β : Val)            : Neutral
  | top                         : Neutral
  | bot                         : Neutral
  | tintro                      : Neutral
  | sort (m : Level)            : Neutral

inductive Val where
  -- Combinators get translated into these
  -- quotation / reflection / reification
  -- ideally η-simplify these
  /-
    For example,
    env -> e
    Eql(f_α) env -> .lam [e] 1 Eql(f_α)
  -/
  | pi   (env : List Val) (arity : ℕ) (f_α f_β : Val) : Val
  | lam  (env : List Val) (arity : ℕ) (bdy : Neutral) : Val
  | neut (nv  : Neutral)                              : Val
  /-
  Thse are handled in neutral now
  -- vars, partial apps
  | neut (nv : Neutral) : Val
  -- Coup(f_β). Reduce inside f_β
  | coup (f_β : Val) : Val
  -- = does not reduce.
  | eq (x : Val) : Val
  -- ⊤
  | top : Val
  -- ∗
  | tintro : Val
  -- ⊥
  | bot : Val
  -- Sort
  | sort (m : Level) : Val-/

end

declare_syntax_cat val_expr
declare_syntax_cat val_list
declare_syntax_cat neut_expr
declare_syntax_cat neut_atom

syntax "#(" term ")"                                         : neut_atom
syntax "var(" term ")"                                       : neut_atom
syntax:max ident                                             : neut_expr

syntax neut_expr "(" neut_expr ")"                           : neut_expr
syntax neut_expr neut_atom                                   : neut_expr
syntax neut_expr ident                                       : neut_expr
--syntax:1024 neut_expr:1024 neut_expr:1025         : neut_expr
syntax val_expr                                              : neut_atom
syntax neut_atom                                             : neut_expr

syntax "⟦" val_expr,* "⟧"                                    : val_list
syntax val_expr noWs "::" noWs val_list                      : val_list
syntax ident noWs "::" noWs val_list                         : val_list
syntax:max ident                                             : val_list

syntax "Sndc(" val_expr,* ")"                                : neut_expr
syntax "Fstc(" val_expr,* ")"                                : neut_expr
syntax "*(" val_expr,* ")"                                   : neut_expr
syntax "Id" val_expr,* ")"                                   : neut_expr
syntax "Eql(" val_expr,* ")"                                 : neut_expr
syntax "refl(" val_expr,* ")"                                : neut_expr
syntax "Σ(" val_expr,* ")"                                   : neut_expr
syntax "Id(" val_expr,* ")"                                  : neut_expr
syntax "!<" val_expr ">"                                     : neut_expr
syntax "$<" val_expr ">"                                     : neut_expr
syntax "Eval(" val_expr,* ")"                                : neut_expr
syntax:max "`(" val_expr,* ")"                               : neut_expr
syntax "⟦" val_expr "⟧" "⟨" val_expr,* "⟩"                   : neut_expr
syntax val_expr "∘'" val_expr                                : neut_expr
syntax val_expr "∘" val_expr                                 : neut_expr
syntax val_expr "∘∘" val_expr                                : neut_expr
syntax:max (priority := high) "!Λ(" val_expr,* ")"           : neut_expr
syntax:max (priority := high) "Λ(" val_expr,* ")"            : neut_expr

syntax (priority := low) "⟦" val_expr "⟧" "(" val_expr,* ")" : neut_expr
syntax "λ" val_list term "=>" neut_expr                      : val_expr
syntax "Π" "(" val_expr ")" val_list term  "," val_expr      : val_expr
syntax val_expr "=" val_expr                                 : neut_expr
syntax "!(" val_expr ")"                                     : neut_expr
syntax "&(" val_expr ")"                                     : neut_expr
syntax "neutral(" neut_expr ")"                              : val_expr
syntax "Coup(" val_expr ")"                                  : neut_expr
syntax:max ident                                             : val_expr
syntax "#(" term ")"                                         : val_expr
syntax "⊤"                                                   : neut_expr
syntax "⊥"                                                   : neut_expr
syntax "∗"                                                   : neut_expr
syntax "Sort" term                                           : neut_expr

syntax "Vals(" val_list ")"         : term
syntax "Val(" val_expr ")"          : term
syntax "Neutral(" neut_expr ")"     : term
syntax "NeutralAtom(" neut_atom ")" : term

open Lean in
macro_rules
  | `(Neutral(Id($α:val_expr))) => `(Neutral.id Val($α:val_expr))
  | `(Neutral(Fstc($α:val_expr))) => `(Neutral.fstc Val($α:val_expr))
  | `(Neutral(Sndc($α:val_expr))) => `(Neutral.sndc Val($α:val_expr))
  | `(Neutral(Eql($α:val_expr))) => `(Neutral.eql Val($α:val_expr))
  | `(Neutral(refl($α:val_expr))) => `(Neutral.refl Val($α:val_expr))
  | `(Neutral(*($α:val_expr))) => `(Neutral.unbox Val($α:val_expr))
  | `(Neutral(!<$f:val_expr>)) => `(Neutral.map Val($f:val_expr))
  | `(Neutral($<$f:val_expr>)) => `(Neutral.fmap Val($f:val_expr))
  | `(Neutral(⟦$β:val_expr⟧⟨$M:val_expr, $N:val_expr⟩)) => `(Neutral.pair Val($β:val_expr) Val($M:val_expr) Val($N:val_expr))
  | `(Neutral(Eval($α:val_expr, $β:val_expr, $x:val_expr))) => `(Neutral.eval Val($α:val_expr) Val($β:val_expr) Val($x:val_expr))
  | `(Neutral(`($β:val_expr, $x:val_expr))) => `(Neutral.quot Val($β:val_expr) Val($x:val_expr))
  | `(Neutral($f:val_expr ∘ $g:val_expr)) => `(Neutral.comp Val($f:val_expr) Val($g:val_expr))
  | `(Neutral($f:val_expr ∘' $g:val_expr)) => `(Neutral.comp' Val($f:val_expr) Val($g:val_expr))
  | `(Neutral($f:val_expr ∘∘ $g:val_expr)) => `(Neutral.comp₂ Val($f:val_expr) Val($g:val_expr))
  | `(Neutral(Σ($f_α:val_expr, $f_β:val_expr))) => `(Neutral.sigma Val($f_α:val_expr) Val($f_β:val_expr))
  | `(Neutral(Λ($α:val_expr, $β:val_expr, $x:val_expr))) => `(Neutral.curr Val($α:val_expr) Val($β:val_expr) Val($x:val_expr))
  | `(Neutral(!Λ($α:val_expr, $β:val_expr, $x:val_expr))) => `(Neutral.curr' Val($α:val_expr) Val($β:val_expr) Val($x:val_expr))
  | `(Neutral(⊤)) => `(Neutral.top)
  | `(Neutral(⊥)) => `(Neutral.bot)
  | `(Neutral(∗)) => `(Neutral.tintro)
  | `(Neutral(Sort $m:term)) => `(Neutral.sort $m:term)
  | `(NeutralAtom(var($n:term))) => `(Neutral.var $n:term)
  | `(Neutral(Coup($β:val_expr))) => `(Neutral.t_coup Val($β:val_expr))
  | `(Vals($list:ident)) => `($list:term)
  | `(Neutral(⟦$β:val_expr⟧($args:val_expr,*))) => do
    let elems ← args.getElems.mapM (fun (v : TSyntax `val_expr) => `(Val($v)))
    `(Neutral.coup (Val($β:val_expr)) $elems*)
  | `(Val($e:ident))     => `($e:term)
  | `(Vals(⟦$vals:val_expr,*⟧)) => do
    let elems ← vals.getElems.mapM (fun (v : TSyntax `val_expr) => `(Val($v:val_expr)))
    `([$elems,*])
  | `(Vals($x:val_expr::$xs:val_list)) => `((Val($x))::(Vals($xs)))
  | `(Vals($x:ident::$xs:val_list)) => `($x:term::(Vals($xs)))
  | `(Neutral($x:val_expr = $y:val_expr)) => `(Neutral.eq (Val($x:val_expr)) (Val($y:val_expr)))
  | `(Neutral(!($x:val_expr))) => `(Neutral.bang (Val($x)))
  | `(Neutral(&($x:val_expr))) => `(Neutral.boxed (Val($x)))
  | `(Val(neutral($x:neut_expr))) => `(Val.neut (Neutral($x:neut_expr)))
  | `(Val(λ $env:val_list $n:term => $bdy:neut_expr)) => do
    `(Val.lam (Vals($env:val_list)) $n:term (Neutral($bdy:neut_expr)))
  | `(Val(Π ($f_α:val_expr) $env:val_list $n:term, $f_β:val_expr)) => do
    `(Val.pi (Vals($env:val_list)) $n:term Val($f_α:val_expr) Val($f_β:val_expr))
  | `(Val(#($tm:term))) => `($tm:term)

open Lean in
macro_rules
  | `(Neutral($v:neut_atom)) => `(NeutralAtom($v:neut_atom))
  | `(NeutralAtom(#($tm:term))) => `($tm:term)
  | `(NeutralAtom($x:val_expr)) => `(Val($x:val_expr))
  /-| `(Neutral($f:neut_expr $xs:neut_expr*)) => do
    let tm ← xs.toList
      |>.foldlM (init := ← `(term| Neutral($f:neut_expr)))
        (f := fun
          (acc : TSyntax `term)
          (x : TSyntax `neut_expr) => `(Neutral.app $acc:term Neutral($x:neut_expr)))
    return tm-/
  | `(Neutral($e:ident)) => `($e:term)
  | `(Neutral($e:neut_expr)) =>
    match e with
    | `(neut_expr| $f:neut_expr $x:val_expr) =>
      `(Neutral.app (Neutral($f)) Val($x:val_expr))
    | `(neut_expr| $f:neut_expr ($x:val_expr)) =>
      `(Neutral.app (Neutral($f)) (Val($x:val_expr)))
    | `(neut_expr| $f:neut_expr ($x:neut_expr)) =>
      `(Neutral.app (Neutral($f)) (Val(neutral($x))))
    | `(neut_expr| $f:neut_expr $idt:ident) =>
      `(Neutral.app (Neutral($f)) $idt:ident)
    | _ => Macro.throwUnsupported

/-
The plan:

- pass TyValue in at the top level
- use existing β-reducer to reduce apps we would have recursively eval'd.
fallback:
- decreasing measure proof?
-/
