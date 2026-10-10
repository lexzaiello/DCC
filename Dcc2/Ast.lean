import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Defs
import Mathlib.Tactic

/-
Improvements to DCC:

Base Ob(C(DCC)) := { ℕ, 𝟙, 𝟘, 𝟚, Hom,

Hom ×

turning A → B into Π A.B

this is a substitution?

I want to keep it pure.

Σ and Π, no less.

I do like the idea of working in Pos.

terminal object in C / A for all types A is Id.

so we define an ordering on Hom.

Fst ∈ Hom(A × B, A)
Snd ∈ Hom(A × B, B)

- Holes / metavariables are not well-typed expressions, but they are unifiable
- Bool is renamed to 𝟚
- ⊤ is renamed to 𝟙
- ⊥ is renamed to 𝟘
- ℕ is a base type
- No combinator has an arity of more than 2 now, except "points" (Γ)
- Vector is not primitive, but we assume it exists
- Σ.size does a literal syntactic size count
  - The head of Σ is either a Value or a Comb (spine)
  - Congruence is represented through nested Comb.reduct
    - This way we might be able to even avoid congrFun and congrArg altogether and only have head reductions
      - Comb.type gives the list that is applied to Π
      - $ : (c : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c))) (x : Comb.dom c) → Comb.cod (, c x)
        - This subsumes Comb.mk
    - Comb.cod is only necessary if the combinator returns a Value.
    - e.g., (Id 𝟙) ∗, or (Fst <sigma containing values>)
      - n is just head, not maximal
    - Λ : Comb 1, as well. But its context must be extended with x.
      - Λ x redcues to Λ₁(x)
      - This way, $ is always of arity 1
      - All combinators have arity 1, so we can ditch that. Nice.
        - They are still distinguished however by n. Λ₁ is 1 (Λ)
- & is also a combinator, but it is not represented with a list it is just a normal function
  - It freezes reduction. No reduction happens under its point.
  - In order to run some function on its contents, you must prove that the function decreases the size
- Level  : Sort 0
- Value  : (u : Level) → (A : Sort u) → (x : A) → Sort u
- A combinator is an interpretation of a context, which is a Σ-list of terms
  - Comb : ℕ → Type 0
  - (Λ)  : Comb 3
  - Comb : Type 0
  - A combinator has a signature, which is the context it expects
    - The signature also contains the universe levels
  - Comb.name    : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c)) → Combinator
  - Comb.u_dom   : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c)) → Level
  - Comb.dom     : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c)) → (Sort (Comb.u_dom c))
  - Comb.u_cod   : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c)) → Level
  - Comb.cod     : (Σ (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c)) (x : Fst (Comb.dom n c Γ))) → (Sort (Comb.u_cod c))

  - Comb.arity   : (n : ℕ) → (c : Comb n)      → ℕ := n

  - Comb.mono    : (Σ (n : ℕ) (c : Comb (.succ n)) (Γ : Comb.sig (.succ n) c)) → (x : Comb.dom n c Γ) → (< $ (Id _) (,n c Γ x))
- Level is a base type
  - zero : Level
  - succ : Level → Level
  - max  : (A → Level) → (A → Level) → A → Level
- Sort : (lv : Level) → (∘ Sort Level.succ)
- (Σ B C) is the default now instead of just (Σ B)
- Nothing needs to index the environment anymore, since all combinators are curryable via lists.
- Lists are primitive, but not made of points
  - , : (u : Level) → (v : Level) → (A : (Sort u)) → (B : (x : A) → (Sort v)) → (x : A) → (y : (B x)) → (Σ A B)
- Parenthesized combinators as in past DCC, e.g., (Id A) expand to:
  (Id A) ⇒ (comb Id (, l_1 _ 𝟙 (`𝟙 (Sort _)) ∗

The meat of it. What will Π look like now?
We can use an even simpler encoding now. I think.

($ (,(, 4  Π (, ∗ u)) A))       := (, 3 Π (, u A))
($ (, (, 3 Π (, u A)) v))       := (, 2 Π (, u A v))
($ (, (, 2 Π (, u A v)) B))     := (, 1 Π (, u A v B))
($ (, (, 1 Π (, u A v B)) env)) := (Π u A v B env)

we definitely still want to keep the environment for Π. Or, the type-checker can duplicate it manually.

f : (Π u A₁ v B env)  x : A₂      (A₁ env) ≡ A₂
----------------------------------------------
B env x →ᵦ τ                           f x : τ

u : (env : Γ) → Level     A : (env : Γ) → Sort (u env)
v : (env : Γ) → Level     B : (env : Γ) → (x : A env) → Sort (v env)
                      env : Γ
----------------------------------------------------------------------
             (Π u A v B env) : Sort (max u v env)

u : (env : Γ) → Level     A : (env : Γ) → Sort (u env)
v : (env : Γ) → Level     B : (env : Γ) → (x : A env) → Sort (v env)
                      env : Γ
----------------------------------------------------------------------
             (Σ u A v B env) : Sort (max u v env)

---------------------------------------------------------
Comb.sig 1 Id := (Σ (Id (Sort 0)) (`(Sort 0) Sort) Level)

-------------
Id : ℕ → Comb

-------------------------------------------------------
Comb.dom (, 1 (,(Comb.sig 1) (Id 1) (,Sort u A))) := A

--------------------------------------------------------
Comb.u_dom (, 1 (,(Comb.sig 1) (Id 1) (,Sort u A))) := u

-------------------------------------------------------
Comb.u_cod (, 1 (,(Comb.sig 1) (Id 1) (,Sort u A))) := u

-------------------------------------------------------------
Comb.cod (, (, 1 (,(Comb.sig 1) (Id 1) (,Sort u A))) _x) := A

VERY IMPORTANT: CONGRFUN is avoided due to nested ($ indicating congrFun explicitly

general CongrFun is avoided easily since we just match nested $.
Combinators that make no "step" should not use $. e.g., Π.

Comb.type : (c : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c))) → ((∘ Sort (max Cod.u_dom Comb.u_cod)) c)
               := (Π Comb.u_dom
                     Comb.dom
                     Comb.u_cod
                     (Λ (Comb.cod))
                     c)

Let's get to it then.

Π is not represented by apps, but rather app of $ reducing into (Π with points

($ (, (, 1 "Sort") u)) := (Sort u)

App is only used for partial applications of $.
$ always denotes a head eventually.

We do congruences individually with $ on the right hand side of the rules that need it.
-/

inductive CombName where
  | snd        : CombName
  | quot       : CombName
  | sigma      : CombName
  | sort       : CombName
  | comb_sig   : CombName
  | comb_u_dom : CombName
  | comb_u_cod : CombName
  | comb_dom   : CombName
  | comb_cod   : CombName
  | comb_type  : CombName
  | id         : CombName
deriving Repr, DecidableEq

inductive Expr where
  | hole_ty   : Expr
  | zero_nat  : Expr
  | succ_nat  : Expr → Expr
  | comb_tm   : CombName → Expr -- "Λ" : Comb
  | comb_ty   : Expr -- Comb
  | zero_lv   : Expr -- 0ᵤ
  | succ_lv   : Expr → Expr -- Level.succ
  | max_lv    : Expr → Expr → Expr → Expr -- max f g env : Level
  | sort      : Expr → Expr -- Sort : (u : Level) → (∘ Sort Level.succ)
  | bot       : Expr -- 𝟘
  | top       : Expr → Expr -- 𝟙 lv : Sort lv
  | tintro    : Expr → Expr -- ∗
  | nat_ty    : Expr -- ℕ
  | true      : Expr
  | false     : Expr
  | bool      : Expr -- 𝟚
  /-
    Λ : (c : (Σ 2 (c : Comb 2), (Γ : Comb.sig 2 c)))
        (x : Comb.dom c)
        (y : Comb.dom ($ c x)) → (Λ Comb.cod ($ c x) y)
  -/
  | curr_tm   : Expr
  | sigma     : Expr → Expr -- (Σ u A v B env)
  | sigma_inv : Expr → Expr
  | pi        : Expr → Expr → Expr → Expr → Expr -- (Π u A v B env)
  | app_tm    : Expr
    -- $ : (c : (Σ (n : ℕ) (c : Comb (.succ n)), (Γ : Comb.sig (.succ n) c))) (x : Comb.dom c) → Comb.cod (, c x)
  | mk        : Expr → Expr → Expr → Expr
  | lv_ty     : Expr -- Level : Sort 0
  | hole      : Expr -- _ : ? n
  | mvar      : Expr → Expr -- ? : ℕ → Sort _
  | app       : Expr → Expr → Expr
deriving Repr, DecidableEq

declare_syntax_cat expr
declare_syntax_cat comb

namespace Dsl

scoped syntax "Snd"        : comb
scoped syntax "Comb.sig"   : comb
scoped syntax "Sort"       : comb
scoped syntax "Π"          : comb
scoped syntax "Σ"          : comb
scoped syntax "Comb.u_dom" : comb
scoped syntax "Comb.u_cod" : comb
scoped syntax "Comb.dom"   : comb
scoped syntax "Comb.cod"   : comb
scoped syntax "Comb.type"  : comb
scoped syntax "Id"         : comb
scoped syntax "Quot"       : comb

syntax "DCC_COMB" comb : term

macro_rules
  | `(DCC_COMB Snd) => `(CombName.snd)
  | `(DCC_COMB Quot) => `(CombName.quot)
  | `(DCC_COMB Comb.sig) => `(CombName.comb_sig)
  | `(DCC_COMB Σ) => `(CombName.sigma)
  | `(DCC_COMB Sort) => `(CombName.sort)
  | `(DCC_COMB Comb.u_dom) => `(CombName.comb_u_dom)
  | `(DCC_COMB Comb.u_cod) => `(CombName.comb_u_cod)
  | `(DCC_COMB Comb.dom) => `(CombName.comb_dom)
  | `(DCC_COMB Comb.cod) => `(CombName.comb_cod)
  | `(DCC_COMB Comb.type) => `(CombName.comb_type)
  | `(DCC_COMB Id) => `(CombName.id)

scoped syntax "Comb.sig"                                : expr
scoped syntax "Hole"                                    : expr
scoped syntax:max "('" comb ")"                         : expr
scoped syntax "('" "#(" term ")" ")"                    : expr
scoped syntax "(:" expr expr ")"                        : expr
scoped syntax "(Level.max" expr+ ")"                    : expr
scoped syntax "(Level.succ" expr+ ")"                   : expr
scoped syntax "(ℕ.succ" expr+ ")"                       : expr
scoped syntax "#(" term ")"                             : expr
scoped syntax "(Sort" expr ")"                          : expr
scoped syntax "𝟘₂"                                      : expr
scoped syntax "𝟙₂"                                      : expr
scoped syntax "𝟘"                                       : expr
scoped syntax "(𝟙" expr+ ")"                            : expr
scoped syntax "𝟚"                                       : expr
scoped syntax:max "Comb"                                : expr
scoped syntax:max "ℕ"                                   : expr
scoped syntax num                                       : expr
scoped syntax "(∗" expr+ ")"                            : expr
scoped syntax "(Σ" expr+ ")"                            : expr
scoped syntax "(Σ⁻¹" expr+ ")"                          : expr
scoped syntax "Λ"                                       : expr
scoped syntax "(Π" expr+ ")"                            : expr
scoped syntax "$"                                       : expr
scoped syntax "($*" expr+ ")"                           : expr
scoped syntax ("(," noWs expr) expr+ ")"                : expr
scoped syntax "Level"                                   : expr
scoped syntax "_"                                       : expr
scoped syntax "(?" expr+")"                             : expr
scoped syntax "(" expr expr+ ")"                        : expr
scoped syntax ident                                     : expr
scoped syntax "(" expr ")"                              : expr

end Dsl

syntax "DCC'" expr : term
syntax "DCC" expr  : term

open Dsl in
macro_rules
  | `(DCC' (Level.succ $x)) => `(Expr.succ_lv (DCC' $x))
  | `(DCC' (ℕ.succ $x)) => `(Expr.succ_nat (DCC' $x))
  | `(DCC' ℕ) => `(Expr.nat_ty)
  | `(DCC' $n:num) =>  do
    let n ← (List.replicate n.getNat (← `(term| Expr.succ_nat))).foldrM
      (fun (a : Lean.TSyntax `term) (b : Lean.TSyntax `term) => `(term| $a $b))
      (← `(term| Expr.zero_nat))
    pure n
  | `(DCC' (: $n:num ℕ)) => do
    let n ← (List.replicate n.getNat (← `(term| Expr.succ_nat))).foldrM
      (fun (a : Lean.TSyntax `term) (b : Lean.TSyntax `term) => `(term| $a $b))
      (← `(term| Expr.zero_nat))
    pure n
  | `(DCC' Comb) => `(Expr.comb_ty)
  | `(DCC' ('$f:comb)) =>
    `(Expr.comb_tm (DCC_COMB $f))
  | `(DCC' ('#($x:term))) =>
    `(Expr.comb_tm $x)
  | `(DCC' (: $n:num Level)) => do
    let n ← (List.replicate n.getNat (← `(term| Expr.succ_lv))).foldrM
      (fun (a : Lean.TSyntax `term) (b : Lean.TSyntax `term) => `(term| $a $b))
      (← `(term| Expr.zero_lv))
    pure n
  | `(DCC' (Level.max $f:expr $g:expr $x:expr)) => `(Expr.max_lv (DCC' $f) (DCC' $g) (DCC' $x))
  | `(DCC' (Sort $u:num)) => `(Expr.sort (DCC' (: $u:num Level)))
  | `(DCC' (Sort $u:expr)) => `(Expr.sort (DCC' $u))
  | `(DCC' 𝟘) => `(Expr.bot)
  | `(DCC' 𝟘₂) => `(Expr.false)
  | `(DCC' 𝟙₂) => `(Expr.true)
  | `(DCC' (𝟙 $lv:expr)) => `(Expr.top (DCC' $lv:expr))
  | `(DCC' 𝟚) => `(Expr.bool)
  | `(DCC' Hole) => `(Expr.hole_ty)
  | `(DCC' (∗ $lv:expr)) => `(Expr.tintro (DCC' $lv:expr))
  | `(DCC' (Σ $B:expr)) => `(Expr.sigma (DCC' $B))
  | `(DCC' (Σ⁻¹ $B:expr)) => `(Expr.sigma_inv (DCC' $B))
  | `(DCC' (Π $u:expr $A:expr $v:expr $B:expr)) => `(Expr.pi (DCC' $u) (DCC' $A) (DCC' $v) (DCC' $B))
  | `(DCC' Λ) => `(Expr.curr_tm)
  | `(DCC' $) => `(Expr.app_tm)
  | `(DCC' (,$β:expr $x:expr $y:expr)) => `(Expr.mk (DCC' $β) (DCC' $x) (DCC' $y))
  | `(DCC' Level) => `(Expr.lv_ty)
  | `(DCC' _) => `(Expr.hole)
  | `(DCC' (? $e:expr)) => `(Expr.mvar (DCC' $e))
  | `(DCC' ($f:expr)) => `(DCC' $f)
  | `(DCC' ($f:expr $args:expr*)) => do
    let x ← (← (args.mapM (fun x => `(DCC' $x)))).foldlM (fun f x => `(term| Expr.app $f $x)) (← `(DCC' $f:expr))
    pure x
  | `(DCC' #($x:term)) => `($x:term)
  | `(DCC' ($* $f:expr $args:expr*)) => do
    let x ← (← (args.mapM (fun x => `(DCC' $x)))).foldlM (fun f x => `(term| (DCC' ($ #($f:term) #($x:term))))) (← `(DCC' $f:expr))
    pure x
  | `(DCC' $idt:ident) => `($idt:term)
  | `(DCC' (: $u:ident Level)) => `($u:term)
  | `(DCC' (: $nm:ident Name)) => `(Expr.name (CombName.mk $nm:term))

open Dsl in
macro_rules
  | `(DCC $e:expr) => `(DCC' $e:expr)

namespace CombName

def to_format (f : CombName) : Std.Format :=
  match f with
  | .snd => "Snd"
  | .quot => "Quot"
  | .comb_sig => "Comb.sig"
  | .sigma => "Σ"
  | .sort => "Sort"
  | .comb_u_dom => "Comb.u_dom"
  | .comb_u_cod => "Comb.u_cod"
  | .comb_type => "Comb.type"
  | .comb_dom => "Comb.dom"
  | .comb_cod => "Comb.cod"
  | .id => "Id"

end CombName

instance : Std.ToFormat CombName := ⟨CombName.to_format⟩

namespace Expr

def nat_to_nat (e : Expr) : ℕ :=
  open Dsl in match e with
  | DCC' 0 => 0
  | DCC' (ℕ.succ x) => x.nat_to_nat.succ
  | _ => 0

def of_spine (f : Expr) (args : List Expr) : Expr :=
  args.foldl Expr.app f

def spine (f x : Expr) :
  Σ' (_h : Σ' (f₀ : Expr), sizeOf f₀ < sizeOf (Expr.app f x)), (List.{0} (Σ' (e : Expr), sizeOf e < sizeOf (Expr.app f x))) :=
  open Dsl in match f with
  | DCC' (a b) =>
    let ⟨⟨f₀, hlt⟩, xs₀⟩ := spine a b
    ⟨⟨f₀, by grind⟩, xs₀.map (fun ⟨a, b⟩ => ⟨a, by grind⟩) ++ [⟨x, by simp [sizeOf, Expr._sizeOf_1]⟩]⟩
  | f => ⟨⟨f, by grind⟩, [⟨x, by simp [sizeOf, Expr._sizeOf_1]⟩]⟩

open Std (Format) in
def to_format (e : Expr) : Format :=
  let sepD (l : List Std.Format) (sep : Std.Format := .line) (indent : ℕ := 2) : Std.Format :=
    .nest indent (.joinSep l sep)
  let paren (s : Std.Format) : Std.Format :=
    .bracket "(" (.fill s) ")"

  let comb (pre : Std.Format) (points : List Std.Format) (paren : Std.Format → Std.Format := paren) : Std.Format :=
    paren ((.align Bool.false) ++ (pre ++ " " ++ (.group (sepD points (indent := min pre.pretty.length.succ 30)))))

  open Dsl in match e with
  | DCC' (Σ⁻¹ x) => comb "Σ⁻¹" [x.to_format]
  | DCC' (Π u A v B) => comb "Π" [u.to_format, A.to_format, v.to_format, B.to_format]
  | DCC' (Σ a) => comb "Σ" [a.to_format]
  | DCC' (∗ x) => comb "∗" [x.to_format]
  | DCC' (𝟙 x) => comb "𝟙" [x.to_format]
  | DCC' (ℕ.succ x) => s!"{(DCC' (ℕ.succ x)).nat_to_nat}"
  | DCC' (Level.succ x) => comb "Level.succ" [x.to_format]
  | DCC' (Level.max f g x) => comb "Level.max" [f.to_format, g.to_format, x.to_format]
  | DCC' (Sort u) => comb "Sort" [u.to_format]
  | DCC' Λ => "Λ"
  | DCC' $ => "$"
  | DCC' Comb => "Comb"
  | DCC' ('#(f)) => comb "'" [f.to_format]
  | DCC' (: 0 Level) => comb ":" [s!"{0}", "Level"]
  | DCC' (: 0 ℕ) => "0"
  | DCC' 𝟘 => "𝟘"
  | DCC' 𝟘₂ => "𝟘₂"
  | DCC' 𝟙₂ => "𝟙₂"
  | DCC' 𝟚 => "𝟚"
  | DCC' Level => "Level"
  | DCC' _ => "_"
  | DCC' Hole => "Hole"
  | DCC' (? x) => comb "?" [x.to_format]
  | DCC' ℕ => "ℕ"
  | DCC' (,β x y) => comb ("," ++ β.to_format) [x.to_format, y.to_format]
  | DCC' (f x) =>
    let ⟨⟨f₀, _hlt⟩, args⟩ := spine f x
    let fmt_args := args.map (fun ⟨arg, _hlt⟩ => to_format arg)
    comb (to_format f₀) fmt_args
termination_by sizeOf e
decreasing_by any_goals (grind)

end Expr

instance : Std.ToFormat Expr := ⟨Expr.to_format⟩
instance : Repr Expr := ⟨fun e _ => .paren ("DCC" ++ .line ++ (.nest 2 e.to_format))⟩

namespace Dsl

syntax expr "→ᵦ" expr : term
syntax expr "≡" expr  : term

end Dsl
