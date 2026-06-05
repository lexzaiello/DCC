import Dcc.Attrs
import Dcc.Ast
import Dcc.Aff.Size
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

syntax (priority := low) "⟦" val_expr "⟧" "(" val_expr,* ")" : neut_expr
syntax "λ" val_list term "=>" gen_dcc                        : val_expr
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
  | `(Neutral(⊤)) => `(Neutral.top)
  | `(Neutral(⊥)) => `(Neutral.bot)
  | `(Neutral(∗)) => `(Neutral.tintro)
  | `(Neutral(Sort $m:term)) => `(Neutral.sort $m:term)
  | `(NeutralAtom(raw($e:gen_dcc))) => `(Neutral.comb (DCC($e:gen_dcc)))
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

mutual

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Neutral.size (nv : Neutral) : ℕ :=
  match nv with
  | Neutral(var(_m)) => 0
  | Neutral(f x) => f.size + x.size
  | Neutral(raw(c)) => c.size
  | Neutral(x = y) => x.size + y.size
  | Neutral(!(x)) => x.size
  | Neutral(&(x)) => x.size + x.size + x.size + 1
  | Neutral(⟦β⟧(x, y)) => x.size + y.size
  | Neutral(Coup(β)) => β.size
  | Neutral(⊤) => (DCC ⊤).size
  | Neutral(⊥) => (DCC ⊥).size
  | Neutral(∗) => (DCC ∗).size
  | Neutral(Sort m) => (DCC Sort m).size

@[aesop norm (rule_sets := [DccSize]), dcc_size, grind]
def Val.size (v : Val) : ℕ :=
  match v with
  | Val(neutral(x)) => x.size
  | Val(λ _env _n => bdy) => bdy.size

end

mutual

/-
which expressions can be converted to values,
given an environment.
-/
inductive Eval : List Val → Expr → Val → Type
  | top    : Eval env (DCC ⊤) Val(neutral(⊤))
  | tintro : Eval env (DCC ∗) Val(neutral(∗))
  | bot    : Eval env (DCC ⊥) Val(neutral(⊥))
  | sort   : Eval env (DCC Sort m) Val(neutral(Sort m))
  | map    : Eval env (DCC !<f>) Val(λ env 1 => !<f>)
  | fmap   : Eval env (DCC $<f>) Val(λ env 1 => $<f>)
  | boxed  : Eval env x x' → Eval env (DCC &(x)) Val(neutral(&(x')))
  | bang   : Eval env x x' → Eval env (DCC !(x)) Val(neutral(!(x')))
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
    → Eval env b b' → Eval env (DCC ⟦β⟧(a, b)) Val(neutral(⟦β'⟧(a', b')))
  | t_coup : Eval env β β' → Eval env (DCC Coup(β)) Val(neutral(Coup(β')))
  | sigma  : Eval env (DCC Σ(α, β)) Val(λ env 1 => Σ(α, β))
  | eq     : Eval env x x' → Eval env y y' → Eval env (DCC (x = y)) Val(neutral(x' = y'))
  | eql    : Eval env (DCC Eql(f_α)) Val(λ env 2 => Eql(f_α))
  | refl   : Eval env (DCC refl(f_α)) Val(λ env 2 => refl(f_α))
  | comp   : Eval env (DCC f ∘ g) Val(λ env 1 => f ∘ g)
  | comp'  : Eval env (DCC f ∘' g) Val(λ env 1 => f ∘' g)
  | comp₂  : Eval env (DCC f ∘∘ g) Val(λ env 1 => f ∘∘ g)
  | app    : Eval env f f' → Eval env x x'
    → Apply f' x' e' → Eval env (DCC (f x)) e'

inductive Apply : (f : Val) → (x : Val) → Val → Type
  | eql    : Apply Val(λ env 1 => Eql(f_α)) Val(neutral(&(x))) x
  | map    : Eval [] f f' → Apply f' x e' → Apply Val(λ env 1 => !<f>) Val(neutral(&(x))) Val(neutral(!(e')))
  | fmap   : Eval [] f f' → Apply f' x e' → Apply Val(λ env 1 => $<f>) Val(neutral(&(x))) Val(neutral(&(e')))
  | unbox  : Apply Val(λ env 1 => *(α)) Val(neutral(&(x))) Val(x)
  | pair   : Eval [] M M' → Eval [] N N' → Apply M' x a → Apply N' x b
    → Apply b a e'
    → Apply Val(λ env 1 => ⟦β⟧⟨M, N⟩) Val(neutral(&(x))) Val(neutral(⟦neutral(raw(β))⟧(
      neutral(raw(M) x), neutral(raw(N) x (raw(M) x)))))
  | eval   : Eval [] x x' → Apply x' y e₁ → Apply e₁ z e'
    → Apply Val(λ env 1 => Eval(_α, _β, x)) Val(neutral(⟦__β⟧(y, z))) e'
  | quot   : Eval [] x x' → Apply Val(λ env 1 => `(β, x)) y x'
  | id     : Apply Val(λ env 1 => Id(α)) x x
  | fstc   : Apply Val(λ env 1 => Fstc(_α)) Val(neutral(⟦β⟧(a, b))) a
  | sndc   : Apply Val(λ env 1 => Sndc(_α)) Val(neutral(⟦β⟧(a, b))) b
  -- f ∘ g x
  | comp'  : Eval [] f f' → Eval [] g g' → Apply g' x A → Apply f' A B → Apply Val(λ env 1 => (f ∘' g)) x B
  | comp   : Eval [] f f' → Eval [] g g' → Apply g' x A → Apply f' A B → Apply Val(λ env 1 => (f ∘ g)) x B
  | comp₂  : Eval [] f f' → Eval [] g g' → Apply g' x A → Apply f' A B → Apply Val(λ env 1 => (f ∘∘ g)) x B
  | curr₁  : Apply Val(λ env 2 => Λ(α, β, x)) y Val(λ y::env 1 => Λ(α, β, x))
  | curr₂  : Eval [] x x' → Apply x' Val(neutral(⟦neutral(raw(β))⟧(y, z))) e'
    → Apply Val(λ y::env 1 => Λ(α, β, x)) z e'
  | curr'₁ : Apply Val(λ env 2 => !Λ(α, β, x)) Val(neutral(&(y))) Val(λ neutral(&(y))::env 1 => Λ(α, β, x))
  | curr'₂ : Eval [] x x' → Apply x' Val(neutral(&(neutral(⟦neutral(raw(β))⟧(y, z))))) e'
    → Apply Val(λ neutral(&(y))::env 1 => !Λ(α, β, x)) Val(neutral(&(z))) e'
  | neut   : Apply Val(neutral(f)) x Val(neutral(f x))

end

mutual

theorem Apply.decreasing (h : Apply f x e') : e'.size < f.size + x.size := by
  sorry

theorem Eval.neut_size_leq (h : Eval _env e Val(neutral(v))) : v.size ≤ e.size := by
  cases h
  any_goals (grind)
  case t_coup h | bang h | boxed h =>
    have h := h.size_eq
    grind
  case eq h₁ h₂ | coup h₁ h₂ =>
    have ha := h₁.size_eq
    have hb := h₂.size_eq
    grind
  case app h₁ h₂ h₃ =>
    have ha := h₁.size_eq
    have hb := h₂.size_eq
    have hc := h₃.decreasing
    simp [Val.size] at hc
    grind

theorem Eval.size_eq (h : Eval _env e v) : v.size ≤ e.size := by
  induction e generalizing v
  case sigma ih₁ ih₂ | pair ih₁ ih₂ ih₃ | comp₂ ih₁ ih₂ | comp ih₁ ih₂ | comp' ih₁ ih₂ | fstc ih
    | sndc ih | eql ih | eq ih₁ ih₂ | refl _ _ _
    | eval _ _ _ | unbox ih | box ih | bang ih
    | coup ih₁ | mkc ih₁ ih₂ ih₃ | pi ih₁ ih₂
    | curr ih₁ ih₂ ih₃ | map ih₁ | fmap ih₁
    | curr' ih₁ ih₂ ih₃ | quot ih₁ ih₂ | id ih₁
    | top | bot | tintro | sort =>
      focus
      cases h
      · first
        | grind
        | (rename_i h
           first
           | have h := ih h
             grind
           | grind
           | (have ha := ih₁ (by assumption)
              grind)
           | (have ha := ih₁ (by assumption)
              have hb := ih₂ (by assumption)
              grind)
           | (have ha := ih₁ (by assumption)
              have hb := ih₂ (by assumption)
              have hc := ih₃ (by assumption)
              grind))
  case app ih₁ ih₂ =>
    cases h with
    | app hf hx happ =>
      have ha := ih₁ (by assumption)
      have hb := ih₂ (by assumption)
      have hc := happ.decreasing
      grind

/-theorem Eval.size_eq (h : Eval _env e v) : e.size = v.size := by
  cases h
  any_goals (grind)
  case bang x x' h | boxed x x' h =>
    have h := h.size_eq
    simp [Val.size, Neutral.size, Expr.size]
    grind
  case coup h₁ h₂ h₃ =>
    
    sorry-/

end

def apply (f x : Val) : ((e' : Val) × Apply f x e') :=
  match f, x with
  | Val(λ env 1 => Eql(f_α)), Val(neutral(&(x))) => ⟨_, .eql⟩
  | Val(λ env 1 => !<f>), Val(neutral(&(x))) =>
    
  | Val(λ env 1 => $<f>), Val(neutral(&(x))) => ⟨_, .fmap⟩
  | Val(λ env 1 => *(α)), Val(neutral(&(x))) => ⟨_, .unbox⟩
  | Val(λ env 1 => ⟦β⟧⟨M, N⟩), Val(neutral(&(x))) => ⟨_, .pair⟩
  | Val(λ env 1 => Eval(_α, _β, x)), Val(neutral(⟦__β⟧(y, z))) => ⟨_, .eval⟩
  | Val(λ env 1 => `(β, x)), y => ⟨_, .quot⟩
  | Val(λ env 1 => Id(α)), x => ⟨_, .id⟩
  | Val(λ env 1 => Fstc(_α)), Val(neutral(⟦β⟧(a, b))) => ⟨_, .fstc⟩
  | Val(λ env 1 => Sndc(_α)), Val(neutral(⟦β⟧(a, b))) => ⟨_, .sndc⟩
  | Val(λ env 1 => (x ∘' y)), z =>
    match 

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
