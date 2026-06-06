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

inductive NeutralTm where
  | fstc  (f_β : Val)           : NeutralTm
  | sndc  (f_β : Val)           : NeutralTm
  | id    (α   : Val)           : NeutralTm
  | eql   (f_α : Val)           : NeutralTm
  | refl   (f_α : Val)          : NeutralTm
  | unbox (α   : Val)           : NeutralTm
  | app (f : Neutral) (x : Val) : NeutralTm
  | map (f : Val)               : NeutralTm
  | fmap (f : Val)              : NeutralTm
  | pair (β x y : Val)          : NeutralTm
  | eval (α β x : Val)          : NeutralTm
  | sigma (α β  : Val)          : NeutralTm
  | quot (β x : Val)            : NeutralTm
  | comp' (f g : Val)           : NeutralTm
  | comp (f g : Val)            : NeutralTm
  | comp₂ (f g : Val)           : NeutralTm
  | curr (α β x : Val)          : NeutralTm
  | curr' (α β x : Val)         : NeutralTm
  | eq (x y : Val)              : NeutralTm
  | bang (x : Val)              : NeutralTm
  | boxed (x : Val)             : NeutralTm
  | coup  (β x y : Val)         : NeutralTm
  | t_coup (β : Val)            : NeutralTm
  | top                         : NeutralTm
  | bot                         : NeutralTm
  | tintro                      : NeutralTm
  | sort (m : ℕ)                : NeutralTm
deriving Repr, BEq

inductive Neutral where
  | var (idx : ℕ) (τ : Val) : Neutral
  | tm (tm :  NeutralTm)    : Neutral
deriving Repr, BEq

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
deriving Repr, BEq

end

declare_syntax_cat val_expr
declare_syntax_cat val_list
declare_syntax_cat neut_expr
declare_syntax_cat neut_atom
declare_syntax_cat neut_tm

syntax "#(" term ")"                                         : neut_atom
syntax "var(" "(" term ")" ":" val_expr ")"                  : neut_atom
syntax:max ident                                             : neut_tm

syntax neut_tm : neut_expr

syntax neut_tm "(" neut_tm ")"                               : neut_tm
syntax neut_tm neut_atom                                     : neut_tm
syntax neut_tm ident                                         : neut_tm
--syntax:1024 neut_tm:1024 neut_tm:1025         : neut_tm
syntax val_expr                                              : neut_atom
syntax neut_atom                                             : neut_tm

syntax "⟦" val_expr,* "⟧"                                    : val_list
syntax val_expr noWs "::" noWs val_list                      : val_list
syntax ident noWs "::" noWs val_list                         : val_list
syntax:max ident                                             : val_list

syntax "tm(" neut_tm ")"                                     : neut_tm
syntax "Sndc(" val_expr,* ")"                                : neut_tm
syntax "Fstc(" val_expr,* ")"                                : neut_tm
syntax "*(" val_expr,* ")"                                   : neut_tm
syntax "Id" val_expr,* ")"                                   : neut_tm
syntax "Eql(" val_expr,* ")"                                 : neut_tm
syntax "refl(" val_expr,* ")"                                : neut_tm
syntax "Σ(" val_expr,* ")"                                   : neut_tm
syntax "Id(" val_expr,* ")"                                  : neut_tm
syntax "!<" val_expr ">"                                     : neut_tm
syntax "$<" val_expr ">"                                     : neut_tm
syntax "Eval(" val_expr,* ")"                                : neut_tm
syntax:max "`(" val_expr,* ")"                               : neut_tm
syntax "⟦" val_expr "⟧" "⟨" val_expr,* "⟩"                   : neut_tm
syntax val_expr "∘'" val_expr                                : neut_tm
syntax val_expr "∘" val_expr                                 : neut_tm
syntax val_expr "∘∘" val_expr                                : neut_tm
syntax:max (priority := high) "!Λ(" val_expr,* ")"           : neut_tm
syntax:max (priority := high) "Λ(" val_expr,* ")"            : neut_tm

syntax (priority := low) "⟦" val_expr "⟧" "(" val_expr,* ")" : neut_tm
syntax "λ" val_list term "=>" neut_tm                      : val_expr
syntax "Π" "(" val_expr ")" val_list term  "," val_expr      : val_expr
syntax val_expr "=" val_expr                                 : neut_tm
syntax "!(" val_expr ")"                                     : neut_tm
syntax "&(" val_expr ")"                                     : neut_tm
syntax "neutral(" neut_tm ")"                                : val_expr
syntax "Coup(" val_expr ")"                                  : neut_tm
syntax:max ident                                             : val_expr
syntax "#(" term ")"                                         : val_expr
syntax "⊤"                                                   : neut_tm
syntax "⊥"                                                   : neut_tm
syntax "∗"                                                   : neut_tm
syntax "Sort" term                                           : neut_tm

syntax "Vals(" val_list ")"         : term
syntax "Val(" val_expr ")"          : term
syntax "NeutralTm(" neut_tm ")"     : term
syntax "Neutral(" neut_tm ")"       : term
syntax "NeutralAtom(" neut_atom ")" : term

open Lean in
macro_rules
  | `(NeutralTm(Id($α:val_expr))) => `((NeutralTm.id Val($α:val_expr)))
  | `(NeutralTm(Fstc($α:val_expr))) => `((NeutralTm.fstc Val($α:val_expr)))
  | `(NeutralTm(Sndc($α:val_expr))) => `((NeutralTm.sndc Val($α:val_expr)))
  | `(NeutralTm(Eql($α:val_expr))) => `((NeutralTm.eql Val($α:val_expr)))
  | `(NeutralTm(refl($α:val_expr))) => `((NeutralTm.refl Val($α:val_expr)))
  | `(NeutralTm(*($α:val_expr))) => `((NeutralTm.unbox Val($α:val_expr)))
  | `(NeutralTm(!<$f:val_expr>)) => `((NeutralTm.map Val($f:val_expr)))
  | `(NeutralTm($<$f:val_expr>)) => `((NeutralTm.fmap Val($f:val_expr)))
  | `(NeutralTm(⟦$β:val_expr⟧⟨$M:val_expr, $N:val_expr⟩)) => `(
    NeutralTm.pair Val($β:val_expr) Val($M:val_expr) Val($N:val_expr))
  | `(NeutralTm(Eval($α:val_expr, $β:val_expr, $x:val_expr))) => `(
    NeutralTm.eval Val($α:val_expr) Val($β:val_expr) Val($x:val_expr))
  | `(NeutralTm(`($β:val_expr, $x:val_expr))) =>
    `((NeutralTm.quot Val($β:val_expr) Val($x:val_expr)))
  | `(NeutralTm($f:val_expr ∘ $g:val_expr)) => `((NeutralTm.comp Val($f:val_expr) Val($g:val_expr)))
  | `(NeutralTm($f:val_expr ∘' $g:val_expr)) => `((NeutralTm.comp' Val($f:val_expr) Val($g:val_expr)))
  | `(NeutralTm($f:val_expr ∘∘ $g:val_expr)) => `((NeutralTm.comp₂ Val($f:val_expr) Val($g:val_expr)))
  | `(NeutralTm(Σ($f_α:val_expr, $f_β:val_expr))) => `((NeutralTm.sigma Val($f_α:val_expr) Val($f_β:val_expr)))
  | `(NeutralTm(Λ($α:val_expr, $β:val_expr, $x:val_expr))) => `((NeutralTm.curr Val($α:val_expr) Val($β:val_expr) Val($x:val_expr)))
  | `(NeutralTm(!Λ($α:val_expr, $β:val_expr, $x:val_expr))) => `((NeutralTm.curr' Val($α:val_expr) Val($β:val_expr) Val($x:val_expr)))
  | `(NeutralTm(⊤)) => `((NeutralTm.top))
  | `(NeutralTm(⊥)) => `((NeutralTm.bot))
  | `(NeutralTm(∗)) => `((NeutralTm.tintro))
  | `(NeutralTm(Sort $m:term)) => `((NeutralTm.sort $m:term))
  | `(NeutralAtom(var(($n:term) : $τ:val_expr))) => `(Neutral.var $n:term Val($τ:val_expr))
  | `(NeutralTm(Coup($β:val_expr))) => `((NeutralTm.t_coup Val($β:val_expr)))
  | `(Vals($list:ident)) => `($list:term)
  | `(NeutralTm(⟦$β:val_expr⟧($args:val_expr,*))) => do
    let elems ← args.getElems.mapM (fun (v : TSyntax `val_expr) => `(Val($v)))
    `((NeutralTm.coup (Val($β:val_expr)) $elems*))
  | `(Val($e:ident))     => `($e:term)
  | `(Vals(⟦$vals:val_expr,*⟧)) => do
    let elems ← vals.getElems.mapM (fun (v : TSyntax `val_expr) => `(Val($v:val_expr)))
    `([$elems,*])
  | `(Vals($x:val_expr::$xs:val_list)) => `((Val($x))::(Vals($xs)))
  | `(Vals($x:ident::$xs:val_list)) => `($x:term::(Vals($xs)))
  | `(NeutralTm($x:val_expr = $y:val_expr)) => `((NeutralTm.eq (Val($x:val_expr)) (Val($y:val_expr))))
  | `(NeutralTm(!($x:val_expr))) => `((NeutralTm.bang (Val($x))))
  | `(NeutralTm(&($x:val_expr))) => `((NeutralTm.boxed (Val($x))))
  | `(Val(neutral($x:neut_tm))) => `(Val.neut Neutral($x:neut_tm))
  | `(Val(λ $env:val_list $n:term => $bdy:neut_tm)) => do
    `(Val.lam (Vals($env:val_list)) $n:term Neutral($bdy:neut_tm))
  | `(Val(Π ($f_α:val_expr) $env:val_list $n:term, $f_β:val_expr)) => do
    `(Val.pi (Vals($env:val_list)) $n:term Val($f_α:val_expr) Val($f_β:val_expr))
  | `(Val(#($tm:term))) => `($tm:term)

open Lean in
macro_rules
  | `(NeutralTm(var(($v:term) : $τ:val_expr))) => `(Neutral.var $v:term Val($τ:val_expr))
  | `(NeutralTm($v:neut_atom)) => `(NeutralAtom($v:neut_atom))
  | `(NeutralAtom(#($tm:term))) => `($tm:term)
  | `(NeutralAtom($x:val_expr)) => `(Val($x:val_expr))
  /-| `(Neutral($f:neut_tm $xs:neut_tm*)) => do
    let tm ← xs.toList
      |>.foldlM (init := ← `(term| Neutral($f:neut_tm)))
        (f := fun
          (acc : TSyntax `term)
          (x : TSyntax `neut_tm) => `((NeutralTm.app $acc:term Neutral($x:neut_tm))))
    return tm-/
  | `(NeutralTm($e:ident)) => `($e:term)
  | `(NeutralTm($e:neut_tm)) =>
    match e with
    | `(neut_tm| $f:neut_tm $x:val_expr) =>
      `(NeutralTm.app (Neutral($f)) Val($x:val_expr))
    | `(neut_tm| $f:neut_tm ($x:val_expr)) =>
      `(NeutralTm.app (Neutral($f)) (Val($x:val_expr)))
    | `(neut_tm| $f:neut_tm ($x:neut_tm)) =>
      `(NeutralTm.app (Neutral($f)) (Val(neutral($x))))
    | `(neut_tm| $f:neut_tm $idt:ident) =>
      `(NeutralTm.app (Neutral($f)) $idt:ident)
    | _ => Macro.throwUnsupported
  | `(Neutral(var(($v:term) : $τ:val_expr))) => `(Neutral.var $v:term Val($τ:val_expr))
  | `(Neutral(tm($tm:neut_tm))) => `(Neutral.tm NeutralTm($tm:neut_tm))
  | `(Neutral($e:ident)) => `($e:term)
  | `(Neutral($tm:neut_tm)) => `(Neutral.tm NeutralTm($tm:neut_tm))


mutual

def Val.decide_eq (a b : Val) : Decidable (a = b) :=
  match heq₀ : a, b with
  | Val(λ x₁::xs₁ n₁ => bdy₁), Val(λ x₂::xs₂ n₂ => bdy₂) =>
    match x₁.decide_eq x₂, bdy₁.decide_eq bdy₂,
      Val(λ xs₁ n₁ => bdy₁).decide_eq Val(λ xs₂ n₂ => bdy₂) with
    | .isTrue h₁, .isTrue h₂, .isTrue h₃ =>
      if h₄ : n₁ = n₂ then
        .isTrue (by simp_all)
      else
        .isFalse (fun h => by simp_all)
    | .isFalse h₁, _, _ =>
      .isFalse (fun h => by simp_all)
    | _, .isFalse h₂, _ =>
      .isFalse (fun h => by simp_all)
    | _, _, .isFalse h₃ =>
      .isFalse (fun h => by simp_all)
  | Val(λ ⟦⟧ n₁ => bdy₁), Val(λ ⟦⟧ n₂ => bdy₂) =>
    if h₁ : n₁ = n₂ then
      match bdy₁.decide_eq bdy₂ with
      | .isTrue h₂ =>
        .isTrue (by simp_all)
      | .isFalse h => .isFalse (fun h => by simp_all)
    else .isFalse (fun h => by simp_all)
  | Val(Π (f_α₁) x₁::xs₁ n₁, f_β₁), Val(Π (f_α₂) x₂::xs₂ n₂, f_β₂) =>
    match x₁.decide_eq x₂, f_α₁.decide_eq f_α₂, f_β₁.decide_eq f_β₂,
      Val(Π (f_α₁) xs₁ n₁, f_β₁).decide_eq Val(Π (f_α₂) xs₂ n₂, f_β₂) with
    | .isTrue h₁, .isTrue h₂, .isTrue h₃, .isTrue h₄ =>
      if h₄ : n₁ = n₂ then
          .isTrue (by simp_all)
      else .isFalse (fun h => by simp_all)
    | .isFalse h₁, _, _, _ =>
        .isFalse (fun h => by simp_all)
    | _, .isFalse h₂, _, _ =>
        .isFalse (fun h => by simp_all)
    | _, _, .isFalse h₃, _ =>
      .isFalse (fun h => by simp_all)
    | _, _, _, .isFalse h₄ =>
      .isFalse (fun h => by simp_all)
  | Val(Π (f_α₁) ⟦⟧ n₁, f_β₁), Val(Π (f_α₂) ⟦⟧ n₂, f_β₂) =>
    if h₁ : n₁ = n₂ then
      match f_α₁.decide_eq f_α₂, f_β₁.decide_eq f_β₂ with
      | .isTrue h₂, .isTrue h₃ =>
        .isTrue (by simp_all)
      | .isFalse h₁, _ =>
        .isFalse (fun h => by simp_all)
      | _, .isFalse h₂ =>
        .isFalse (fun h => by simp_all)
    else .isFalse (fun h => by simp_all)
  | Val(Π (f_α₁) x₁::xs₁ n₁, f_β₁), Val(Π (f_α₂) ⟦⟧ n₂, f_β₂) => .isFalse (fun h => by
    simp_all)
  | Val(Π (f_α₁) ⟦⟧ n₁, f_β₁), Val(Π (f_α₂) x₂::xs₂ n₂, f_β₂) => .isFalse (fun h => by
    simp_all)
  | Val(λ x₁::xs₁ n₁ => bdy₁), Val(λ ⟦⟧ n₂ => bdy₂) => .isFalse (fun h => by
    simp_all)
  | Val(λ ⟦⟧ n₁ => bdy₁), Val(λ x₂::xs₂ n₂ => bdy₂) => .isFalse (fun h => by
    simp_all)
  | Val(neutral(nv₁)), Val(neutral(nv₂)) =>
    match nv₁.decide_eq nv₂ with
    | .isTrue h =>
      sorry
    | .isFalse h =>
      sorry
  | .pi _a _b _c _d, .lam __a __b __c => .isFalse (fun h => by
    simp_all)
  | .lam __a __b __c, .pi _a _b _c _d => .isFalse (fun h => by
    simp_all)
  | .neut nv, .lam __a __b __c => .isFalse (fun h => by
    simp_all)
  | .lam __a __b __c, .neut nv => .isFalse (fun h => by
    simp_all)
  | .neut nv, .pi __a __b __c __d => .isFalse (fun h => by
    simp_all)
  | .pi __a __b __c __d, .neut nv => .isFalse (fun h => by
    simp_all)
termination_by sizeOf a

def Neutral.decide_eq (a b : Neutral) : Decidable (a = b) := by
  
  sorry

def NeutralTm.decide_eq (a b : NeutralTm) : Decidable (a = b) :=
  sorry

end

end Semantic

/-
The plan:

- pass TyValue in at the top level
- use existing β-reducer to reduce apps we would have recursively eval'd.
fallback:
- decreasing measure proof?
-/
