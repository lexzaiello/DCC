import Dcc.Ast
import Dcc.Relation

namespace Expr

abbrev Arity := ℕ

-- Combinators that can make a step with their well-typed arguments
-- with a list of their points
inductive IsRedComb : Expr → Arity → Type
  -- Eql(f_α) env x -> (x = x)
  | eql   : IsRedComb (DCC Eql(f_α)) 2
  -- Id(α) x
  | id    : IsRedComb (DCC Id(α)) 1
  -- (f ∘ g) x
  | comp  : IsRedComb (DCC (f ∘ g)) 1
  | comp' : IsRedComb (DCC (f ∘' g)) 1
  -- Fstc(..) (x, y) -> x
  | fstc  : IsRedComb (DCC Fstc(β)) 1
  | sndc  : IsRedComb (DCC Sndc(β)) 1
  -- Σ(f_α, f_β) env -> Coup(...)
  | sigma : IsRedComb (DCC Σ(f_α, f_β)) 1
  -- `(β, x) y
  | quot  : IsRedComb (DCC `(β, x)) 1
  -- ⟨f, g⟩ x
  | pair  : IsRedComb (DCC ⟦β⟧⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsRedComb (DCC Λ(α, β, x)) 2

inductive IsRedCombApp : Expr → Arity → Type
  -- Eql(f_α) env x -> (x = x)
  | eql   : IsRedCombApp (DCC Eql(f_α)) 2
  -- Id(α) x
  | id    : IsRedCombApp (DCC Id(α)) 1
  -- (f ∘ g) x
  | comp  : IsRedCombApp (DCC (f ∘ g)) 1
  | comp' : IsRedCombApp (DCC (f ∘' g)) 1
  -- Fstc(..) (x, y) -> x
  | fstc  : IsRedCombApp (DCC Fstc(β)) 1
  | sndc  : IsRedCombApp (DCC Sndc(β)) 1
  -- Σ(f_α, f_β) env -> Coup(...)
  | sigma : IsRedCombApp (DCC Σ(f_α, f_β)) 1
  -- `(β, x) y
  | quot  : IsRedCombApp (DCC `(β, x)) 1
  -- ⟨f, g⟩ x
  | pair  : IsRedCombApp (DCC ⟦β⟧⟨f, g⟩) 1
  -- Λ(α, β, x) y z
  | curr  : IsRedCombApp (DCC Λ(α, β, x)) 2
  | app   : IsRedCombApp f (m + 1) → IsRedCombApp (DCC (f x)) m

/-
A normal form is either:
- a combinator with fewer than its arity arguments applied
  - and all arguments are values

- Π(f_α, f_β)
  - if f_β is a value
- Π(f_α, f_β) env
  - if f_β and env are values
- refl(f_α) env
  - if env is a value
- refl(f_α) env x
  - if env and x are values
- Coup(f_β)
- x = y

- a Sort m
- ⊤
- ⊥
- ∗
-/

/-
Sorts, ⊤, ⊥, ∗, and "combinators" that are no-op.
-/
inductive Atom : Expr → Prop
  | refl₀  : Atom (DCC refl(f_α))
  | refl₁  : Atom (DCC (refl(f_α) env))
  | refl₂  : Atom (DCC (refl(f_α) env x))
  | coup   : Atom (DCC Coup(f_β))
  | eq     : Atom (DCC (x = y))
  | top    : Atom (DCC ⊤)
  | tintro : Atom (DCC ∗)
  | bot    : Atom (DCC ⊥)
  | sort   : Atom (DCC Sort m)

inductive Value : Expr → Prop
  | pi₁    : Value f_β → Value (DCC Π(f_α, f_β))
  | pi₂    : Value f_β → Value env → Value (DCC (Π(f_α, f_β) env))
  | refl₁  : Value env → Value (DCC (refl(f_α) env))
  | refl₂  : Value env → Value x → Value (DCC (refl(f_α) env x))
  | coup   : Value f_β → Value (DCC Coup(f_β))
  | eq     : Value (DCC x = y)
  | comb   : IsRedComb c m → Value c
  | c_app  : IsRedComb f 2 → Value f → Value x → Value (DCC (f x))
  | top    : Value (DCC ⊤)
  | bot    : Value (DCC ⊥)
  | tintro : Value (DCC ∗)
  | sort   : Value (DCC Sort m)

inductive TyValue (P_pi : Expr → Prop) : Expr → Prop
  -- potentially sus IsNorm
  | pi     : P_pi f_β → Value env
    → TyValue P_pi (DCC (Π(f_α, f_β) env))
  | eq     : TyValue P_pi (DCC x = y)
  | top    : TyValue P_pi (DCC ⊤)
  | bot    : TyValue P_pi (DCC ⊥)
  | tintro : TyValue P_pi (DCC ∗)
  | sort   : TyValue P_pi (DCC Sort m)

end Expr

/-
For normalization by evaluation for η

Example:

α -> a
-------------------------------
Id(α) -> Lam (fun (x : α) => x)

Id(α) -> 

Use variables?

apps have an environment. This is either a couple or a neutral value.
-/
namespace Semantic

mutual

/-
Combinators that perform some computation
-/
inductive Comb where
  -- !<f>
  | map   (f : Val)       : Comb
  -- $<f>
  | fmap  (f : Val)       : Comb
  -- *(α)
  | unbox (α : Val)       : Comb
  -- ⟨M, N⟩
  | pair  (β M N : Val)   : Comb
  -- Eval(α, β, x)
  | eval  (α β x : Val)   : Comb
  -- `(β, x)
  | quot  (β x : Val)     : Comb
  -- Id(α)
  | id    (α : Val)       : Comb
  -- Fstc(β)
  | fstc  (β : Val)       : Comb
  -- Sndc(β)
  | sndc  (β : Val)       : Comb
  -- f ∘' g
  | comp' (f g : Val)     : Comb
  -- f ∘ g
  | comp  (f g : Val)     : Comb
  -- f ∘∘ g
  | comp₂ (f g : Val)     : Comb
  -- Λ(α, β, x)
  | curr  (α β x : Val)   : Comb
  -- !Λ(α, β, x)
  | curr' (α β x : Val)   : Comb
  -- Σ(f_α, f_β)
  | sigma (f_α f_β : Val) : Comb
  -- Π(f_α, f_β) env doesn't reduce but requires env argument
  | pi    (f_α f_β : Val) : Comb
  -- Eql does reduce Eql(f_α) env x = (x = x)
  | eql   (f_α : Val)     : Comb
  -- Refl does not reduce, but it requires arguments
  | refl  (f_α : Val)     : Comb

inductive Neutral where
  | var (idx : ℕ)               : Neutral
  | app (f : Neutral) (x : Val) : Neutral
  | comb (c : Expr)             : Neutral

inductive Val where
  | eq    : Val → Val → Val
  -- !(v)
  | bang  : Val → Val
  -- &(v)
  | boxed : Val → Val
  | coup  (β x y : Val) : Val
  | t_coup (β : Val)    : Val
  -- Combinators get translated into these
  -- quotation / reflection / reification
  -- ideally η-simplify these
  /-
    For example,
    env -> e
    Eql(f_α) env -> .lam [e] 1 Eql(f_α)
  -/
  | lam  (env : List Val) (arity : ℕ) (bdy : Expr) : Val
  | neut (nv  : Neutral)                           : Val
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

syntax "raw(" gen_dcc ")"                                    : neut_atom
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

syntax (priority := low) "⟦" val_expr "⟧" "(" val_expr,* ")" : val_expr
syntax "λ" val_list term "=>" gen_dcc                        : val_expr
syntax val_expr "=" val_expr                                 : val_expr
syntax "!(" val_expr ")"                                     : val_expr
syntax "&(" val_expr ")"                                     : val_expr
syntax "neutral(" neut_expr ")"                              : val_expr
syntax "Coup(" val_expr ")"                                  : val_expr
syntax:max ident                                             : val_expr
syntax "#(" term ")"                                         : val_expr

syntax "Vals(" val_list ")"         : term
syntax "Val(" val_expr ")"          : term
syntax "Neutral(" neut_expr ")"     : term
syntax "NeutralAtom(" neut_atom ")" : term

open Lean in
macro_rules
  | `(NeutralAtom(raw($e:gen_dcc))) => `(Neutral.comb (DCC($e:gen_dcc)))
  | `(NeutralAtom(var($n:term))) => `(Neutral.var $n:term)
  | `(Val(Coup($β:val_expr))) => `(Val.t_coup Val($β:val_expr))
  | `(Vals($list:ident)) => `($list:term)
  | `(Val(⟦$β:val_expr⟧($args:val_expr,*))) => do
    let elems ← args.getElems.mapM (fun (v : TSyntax `val_expr) => `(Val($v)))
    `(Val.coup (Val($β:val_expr)) $elems*)
  | `(Val($e:ident))     => `($e:term)
  | `(Vals(⟦$vals:val_expr,*⟧)) => do
    let elems ← vals.getElems.mapM (fun (v : TSyntax `val_expr) => `(Val($v:val_expr)))
    `([$elems,*])
  | `(Vals($x:val_expr::$xs:val_list)) => `((Val($x))::(Vals($xs)))
  | `(Vals($x:ident::$xs:val_list)) => `($x:term::(Vals($xs)))
  | `(Val($x:val_expr = $y:val_expr)) => `(Val.eq (Val($x:val_expr)) (Val($y:val_expr)))
  | `(Val(!($x:val_expr))) => `(Val.bang (Val($x)))
  | `(Val(&($x:val_expr))) => `(Val.boxed (Val($x)))
  | `(Val(neutral($x:neut_expr))) => `(Val.neut (Neutral($x:neut_expr)))
  | `(Val(λ $env:val_list $n:term => $bdy:gen_dcc)) => do
    `(Val.lam (Vals($env:val_list)) $n:term (DCC($bdy:gen_dcc)))
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

namespace Val

mutual

/-
which expressions can be converted to values,
given an environment.
-/
inductive Eval : List Val → Expr → Val → Type
  | top    : Eval env (DCC ⊤) Val(neutral(raw(⊤)))
  | tintro : Eval env (DCC ∗) Val(neutral(raw(∗)))
  | bot    : Eval env (DCC ⊥) Val(neutral(raw(⊥)))
  | sort   : Eval env (DCC Sort m) Val(neutral(raw(Sort m)))
  | map    : Eval env (DCC !<f>) Val(λ env 1 => !<f>)
  | fmap   : Eval env (DCC $<f>) Val(λ env 1 => $<f>)
  | boxed  : Eval env x x' → Eval env (DCC &(x)) Val(&(x'))
  | bang   : Eval env x x' → Eval env (DCC !(x)) Val(!(x'))
  | unbox  : Eval env (DCC *(x)) Val(λ env 1 => *(x))
  | eval   : Eval env (DCC Eval(α, β, x)) Val(λ env 1 => Eval(α, β, x))
  | quot   : Eval env (DCC `(β, x)) Val(λ env 1 => `(β, x))
  | id     : Eval env (DCC Id(α)) Val(λ env 1 => Id(α))
  | fstc   : Eval env (DCC Fstc(β)) Val(λ env 1 => Fstc(β))
  | sndc   : Eval env (DCC Sndc(β)) Val(λ env 1 => Sndc(β))
  | curr   : Eval env (DCC Λ(α, β, x)) Val(λ env 2 => Λ(α, β, x))
  | curr'  : Eval env (DCC !Λ(α, β, x)) Val(λ env 2 => !Λ(α, β, x))
  | pi     : Eval env (DCC Π(f_α, f_β)) Val(λ env 1 => Π(f_α, f_β))
  | pair   : Eval env (DCC ⟦β⟧⟨M, N⟩) Val(λ env 1 => ⟦β⟧⟨M, N⟩)
  | coup   : Eval env β β' → Eval env a a'
    → Eval env b b' → Eval env (DCC ⟦β⟧(a, b)) Val(⟦β'⟧(a', b'))
  | t_coup : Eval env β β' → Eval env (DCC Coup(β)) Val(Coup(β'))
  | sigma  : Eval env (DCC Σ(α, β)) Val(λ env 1 => Σ(α, β))
  | eq     : Eval env x x' → Eval env y y' → Eval env (DCC (x = y)) Val(x' = y')
  | eql    : Eval env (DCC Eql(f_α)) Val(λ env 2 => Eql(f_α))
  | refl   : Eval env (DCC refl(f_α)) Val(λ env 2 => refl(f_α))
  | comp   : Eval env (DCC f ∘ g) Val(λ env 1 => f ∘ g)
  | comp'  : Eval env (DCC f ∘' g) Val(λ env 1 => f ∘' g)
  | comp₂  : Eval env (DCC f ∘∘ g) Val(λ env 1 => f ∘∘ g)
  | app    : Eval env f f' → Eval env x x' → Apply f' x' e' → Eval env (DCC (f x)) e'

inductive Apply : (f : Val) → (x : Val) → Val → Type
  | eql    : Apply Val(λ env 1 => Eql(f_α)) Val(&(x)) x
  | map    : Apply Val(λ env 1 => !<f>) Val(&(x)) Val(!(neutral(raw(f) x)))
  | fmap   : Apply Val(λ env 1 => $<f>) Val(&(x)) Val(&(neutral(raw(f) x)))
  | unbox  : Apply Val(λ env 1 => *(α)) Val(&(x)) Val(x)
  | pair   : Apply Val(λ env 1 => ⟦β⟧⟨M, N⟩) Val(&(x)) Val(⟦neutral(raw(β))⟧(
    neutral(raw(M) x), neutral(raw(N) x (raw(M) x))))
  | eval   : Apply Val(λ env 1 => Eval(_α, _β, x)) Val(⟦__β⟧(y, z)) Val(neutral(raw(x) y z))
  | quot   : Apply Val(λ env 1 => `(β, x)) y Val(neutral(raw(x)))
  | id     : Apply Val(λ env 1 => Id(α)) x x
  | fstc   : Apply Val(λ env 1 => Fstc(_α)) Val(⟦β⟧(a, b)) a
  | sndc   : Apply Val(λ env 1 => Sndc(_α)) Val(⟦β⟧(a, b)) b
  | comp'  : Apply Val(neutral(raw(y))) z A → Apply Val(neutral(raw(x))) A B
    → Apply Val(λ env 1 => (x ∘' y)) z Val(neutral(raw(x) (raw(y) z)))
  | comp   : Apply Val(λ env 1 => (x ∘ y)) z Val(neutral(raw(x) (raw(y) z)))
  | comp₂  : Apply Val(λ env 1 => (x ∘∘ y)) z Val(neutral(raw(x) (raw(y) z)))
  | curr₁  : Apply Val(λ env 2 => Λ(α, β, x)) y Val(λ y::env 1 => Λ(α, β, x))
  | curr₂  : Apply Val(λ y::env 1 => Λ(α, β, x)) z Val(neutral(raw(x) ⟦neutral(raw(β))⟧(y, z)))
  | curr'₁ : Apply Val(λ env 2 => !Λ(α, β, x)) Val(&(y)) Val(λ &(y)::env 1 => !Λ(α, β, x))
  | curr'₂ : Apply Val(λ &(y)::env 1 => !Λ(α, β, x)) Val(&(z)) Val(neutral(raw(x) &(⟦neutral(raw(β))⟧(y, z))))
  | neut   : Apply Val(neutral(f)) x Val(neutral(f x))

end

def apply (f x : Val) : Val :=
  match f with
  | .lam ctx arity bdy =>
    match arity with
    | .succ (.succ n) =>
      .lam (x :: ctx) (.succ n) bdy
    | _ =>
      match bdy, ctx with
      | DCC (Eql(f_α)), _ :: (.boxed v) :: _xs => .eq v v
      

def quote (v : Val) : Expr :=
  match v with
  | 

end Val

end Semantic

namespace Expr

open Semantic

def eval (e : Expr) : Val :=


end Expr

/-
NbE η-reduction:

Check if 
-/
