import Dcc.Attrs
import Mathlib.Data.Nat.Notation
import Init.Data.String.Search
import Lean

-- Infinite sort universe hierarchy
abbrev Level := ℕ

def decode_level (e : Lean.Expr) : Lean.Elab.TermElabM ℕ := do
  let some n ← (pure e.nat?) | throwError s!"not a valid universe: {e}"
  return n

/-
Similar to the categorical combinators and contextual categories.

- Fst corresponds to truncation of contexts.
  Fst(α, β) : ∀ (s : Σ α, β), α

Σ corresponds to substitution:
⟦α, x⟧ : Σ Type, id(Type)
Fst(α, β) : Σ α β → α
Snd(α, β) : Σ (x : α) β → β x

we can derive `()

Λ(Fst(α, β)
-/

namespace GenAst

open Lean.Macro Lean.Parser.Command
open Lean (Parser.Command.derivingClass TSyntax MacroM mkIdent Name Syntax)
open Lean.Parser.Term (matchAlt matchAltExpr)

syntax "gen_ast" gen_flag_set                   : command

def field (s : String) : TSyntax `ident :=
    Lean.mkIdent (Lean.Name.mkSimple s).eraseMacroScopes

def mk_ext (my_name ext : TSyntax `ident) : MacroM (TSyntax ``ctor) := do
    `(ctor| | $(field "ext"):ident : $ext:ident → $my_name)

-- Expr → Expr → ... up to arity
structure AstField where
  nm           : String
  -- only self arity
  arity        : ℕ
  other_params : Array (TSyntax `ident) := #[]
  -- this field doesn't map onto an actual term-level constructor
  wildcard     : Bool := False
deriving Repr

def AstField.total_arity (fld : AstField) : ℕ :=
  fld.arity + fld.other_params.toList.length

def AstField.nm_camel (fld : AstField) : TSyntax `ident :=
  let parts := (fld.nm.splitOn "_").filter (· ≠ "")
  mkIdent (parts.foldl
    (fun acc p => Lean.Name.str acc (cap_first p)) Lean.Name.anonymous).eraseMacroScopes
where cap_first (s : String) : String :=
  match s.toList with
  | []      => ""
  | c :: cs => String.ofList (c.toUpper :: cs)

def AstField.nm_short : AstField → TSyntax `ident :=
  field ∘ AstField.nm

def AstField.name_long (ast_ind_name : TSyntax `ident) (fld : AstField) : Name :=
  (ast_ind_name.getId ++ Lean.Name.mkSimple fld.nm).eraseMacroScopes

def AstField.nm_long (ast_ind_name : TSyntax `ident) (fld : AstField) : TSyntax `ident :=
  mkIdent <| (ast_ind_name.getId ++ Lean.Name.mkSimple fld.nm).eraseMacroScopes

def AstField.type (ast_ind_name : TSyntax `ident) (fld : AstField) : MacroM (TSyntax `term) :=
  (fld.other_params ++ ⟨List.replicate fld.arity ast_ind_name⟩).foldrM
    (fun (e : TSyntax `ident) (acc : TSyntax `term) => `(term| $e:ident → $acc:term))
    ast_ind_name

def AstField.ctor (ast_ind_name : TSyntax `ident) (fld : AstField) : MacroM (TSyntax ``ctor) := do
  let nm  := fld.nm_short
  let typ ← fld.type ast_ind_name
  `(ctor| | $nm:ident : $typ:term)

-- const field
def AstField.nm_quoted (ast_ind_name : TSyntax `ident) (fld : AstField) : MacroM (Lean.TSyntax `term) :=
  let nm := fld.nm_long ast_ind_name
  `(Lean.Expr.const ``$(nm) [])

def AstField.is_ext (fld : AstField) : Bool := ¬ fld.other_params.toList.isEmpty

-- uses an alphabet of x1 x2 x3 x... to bind arguments
-- do_with operates on each bound variable
-- return .constructor at the end
def AstField.meta_matcher (rec_handler : TSyntax `term) (flags : Flag) (fld : AstField) :
  MacroM (TSyntax ``matchAlt) := do
  let rec_handler := (flags.decoder? fld.nm_short).getD rec_handler
  let from_ind_name : TSyntax `ident ← flags.get!' Flag.from?
  let to_ind_name   : TSyntax `ident ← flags.as!'

  let vars : List (TSyntax `ident) := (List.range fld.total_arity).map (fun n =>
      let idt : TSyntax `ident := mkIdent (Name.str .anonymous s!"x_{n}").eraseMacroScopes
      idt)
  let nm_long := fld.nm_long to_ind_name
  let apps_extra : List (TSyntax `term) ← (vars.take fld.other_params.toList.length).mapM
    (fun (e : TSyntax `ident) =>
      match flags.decoder? fld.nm_short with
      | .some dec => `(term| ← $dec:term $e:term)
      | _ => `(return $e:term))
  if fld.wildcard then
    `(matchAltExpr| | x => do return $nm_long:term x)
  else
    let lean_app : TSyntax `ident := mkIdent ``Lean.Expr.app
    let nm_quot ← fld.nm_quoted from_ind_name
    let bdr ← vars.foldlM (init := ← `(term| $nm_quot))
      (fun (acc : TSyntax `term) (e : TSyntax `ident) => `(term| $lean_app $acc:term $e:ident))
    let apps_main ← (vars.drop fld.other_params.toList.length).mapM
      (fun (e : TSyntax `ident) => `(term| (← $rec_handler:term $e:term)))
    let do_with   ← `(term| return $nm_long:term $(⟨apps_extra⟩)* $(⟨apps_main⟩)*)

    `(matchAltExpr| | $bdr => do $do_with:term)

def sort_field (flags : Flag) : MacroM AstField := do
  let default_ctor := mkIdent (``_root_.Level).eraseMacroScopes
  let ctor ← if (flags.decoder? (field "sort")).isSome then
    `(ident| Lean.Expr)
  else
    pure default_ctor

  return ⟨"sort", 0, #[ctor], False⟩

def ast_basic_fields : (Array AstField) :=
  #[
    ⟨"bang", 1, #[], False⟩,
    ⟨"box", 1, #[], False⟩,
    ⟨"unbox", 1, #[], False⟩,
    ⟨"eval", 3, #[], False⟩,
    ⟨"refl", 1, #[], False⟩,
    -- =(x, y)
    ⟨"eq", 2, #[], False⟩,
    ⟨"eql", 1, #[], False⟩,
    ⟨"fstc", 1, #[], False⟩,
    ⟨"sndc", 1, #[], False⟩,
    ⟨"comp'", 2, #[], False⟩,
    ⟨"comp", 2, #[], False⟩,
    ⟨"comp₂", 2, #[], False⟩,
    ⟨"pair", 3, #[], False⟩,
    ⟨"sigma", 2, #[], False⟩,
    ⟨"coup", 1, #[], False⟩,
    ⟨"mkc", 3, #[], False⟩,
    ⟨"pi", 2, #[], False⟩,
    ⟨"curr", 3, #[], False⟩,
    ⟨"map", 1, #[], False⟩,
    ⟨"fmap", 1, #[], False⟩,
    ⟨"curr'", 3, #[], False⟩,
    ⟨"quot", 2, #[], False⟩,
    ⟨"id", 1, #[], False⟩,
    ⟨"app", 2, #[], False⟩,
    ⟨"top", 0, #[], False⟩,
    ⟨"bot", 0, #[], False⟩,
    ⟨"tintro", 0, #[], False⟩]

def ast_base_fields (flags : Flag) : MacroM (Array AstField) := do
  return ast_basic_fields ++ #[← (sort_field flags)]

def Flag.ext_fields (flags : Flag) : Array AstField :=
  flags.with!.map (fun (fld, is_wc) =>
    let nm := fld.getId.eraseMacroScopes
    let nm_camel_case := nm.components.filterMap (fun c =>
      match c with
      | .str _ s => some (to_camel s)
      | _ => none)
  |> String.intercalate "_"
    { wildcard := is_wc, nm := nm_camel_case, other_params := #[fld], arity := 0})
where to_camel (s : String) : String :=
  s.foldl (init := "") (fun (acc : String) c =>
    if c.isUpper then
      s!"{acc}_{c.toLower}"
    else s!"{acc}{c}")
  |>.dropWhile (· == '_')
  |>.copy

-- Fields that mention types other than the inductive in ctor
def Flag.synth_fields (flags : Flag) : MacroM (Array AstField) := do
  return flags.ext_fields ++ #[← (sort_field flags)]

def Flag.basic_fields (_flags : Flag) : MacroM (Array AstField) :=
  pure ast_basic_fields

def Flag.all_fields (flags : Flag) : MacroM (Array AstField) := do
  return (← (ast_base_fields flags)) ++ flags.ext_fields

def mk_my_expr (flags : Flag) : MacroM (TSyntax `command) := do
  let my_name ← flags.as!'
  let all ← (← flags.all_fields).mapM (AstField.ctor my_name)
  flags.build_inductive all

macro_rules
  | `(command| gen_ast $flags:gen_flag_set) =>
    mk_my_expr (parse_flags flags)

namespace _test

gen_ast as StrExpr
  with String
  deriving Repr

#check StrExpr.string
#check Repr StrExpr

end _test

end GenAst

open GenAst in
open Lean (ToExpr) in
gen_ast as Expr
  deriving BEq, DecidableEq, Inhabited, Repr

#check Expr.sort

declare_syntax_cat gen_dcc

syntax "!<" gen_dcc ">"                                       : gen_dcc
syntax "$<" gen_dcc ">"                                       : gen_dcc
syntax "*(" gen_dcc ")"                                       : gen_dcc
syntax "!(" gen_dcc ")"                                       : gen_dcc
syntax "&(" gen_dcc ")"                                       : gen_dcc
syntax  gen_dcc "=" gen_dcc                                   : gen_dcc
syntax "Eval(" gen_dcc,* ")"                                  : gen_dcc
syntax "Eql(" gen_dcc,* ")"                                   : gen_dcc
syntax "refl(" gen_dcc,* ")"                                  : gen_dcc
syntax "#(" term ")"                                          : gen_dcc
syntax "⊤"                                                    : gen_dcc
syntax "∗"                                                    : gen_dcc
syntax "⊥"                                                    : gen_dcc
syntax:max "`(" gen_dcc,* ")"                                 : gen_dcc
syntax:max "Id(" gen_dcc,* ")"                                : gen_dcc
syntax:max "Fstc(" gen_dcc,* ")"                              : gen_dcc
syntax:max "Sndc(" gen_dcc,* ")"                              : gen_dcc
syntax "Σ(" gen_dcc,* ")"                                     : gen_dcc
syntax "Coup(" gen_dcc ")"                                    : gen_dcc
syntax:max (priority := high) "Λ(" gen_dcc,* ")"              : gen_dcc
syntax:max (priority := high) "!Λ(" gen_dcc,* ")"             : gen_dcc
syntax:max (priority := high) "Π(" gen_dcc,* ")"              : gen_dcc
syntax gen_dcc "∘'" gen_dcc                                   : gen_dcc
syntax gen_dcc "∘" gen_dcc                                    : gen_dcc
syntax gen_dcc "∘∘" gen_dcc                                   : gen_dcc
syntax:30 ident                                               : gen_dcc
syntax "(" gen_dcc+ ")"                                       : gen_dcc
syntax:max "Sort" term                                        : gen_dcc
syntax (priority := high) "⟦" gen_dcc "⟧" "⟨" gen_dcc,* "⟩"   : gen_dcc
syntax (priority := high) "⟦" gen_dcc,* "⟧" "(" gen_dcc,* ")" : gen_dcc

declare_syntax_cat gen_dcc_loc

syntax "."   : gen_dcc_loc
syntax ident : gen_dcc_loc

syntax "DCC" "[" gen_dcc_loc "]"  gen_dcc : term

def field (in_ty : Lean.TSyntax `gen_dcc_loc) (fld : String) : Lean.MacroM (Lean.TSyntax `term) := do
  match in_ty with
  | `(gen_dcc_loc| .) => return Lean.mkIdent (Lean.Name.mkSimple fld).eraseMacroScopes
  | `(gen_dcc_loc| $idt:ident) =>
    let nm := (idt.getId ++ Lean.Name.mkSimple fld).eraseMacroScopes
    return Lean.mkIdent nm
  | s => Lean.Macro.throwErrorAt in_ty s!"this is not a DCC-like: {s}"

open Lean.Syntax in macro_rules
  | `(DCC[$ty:gen_dcc_loc] Eval($α:gen_dcc, $β:gen_dcc, $x:gen_dcc)) => return mkApp (← field ty "eval") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] ⊤)                                        => field ty "top"
  | `(DCC[$ty:gen_dcc_loc] ⊥)                                        => field ty "bot"
  | `(DCC[$ty:gen_dcc_loc] ∗)                                        => field ty "tintro"
  | `(DCC[$ty:gen_dcc_loc] $x:gen_dcc = $y:gen_dcc)                  => do
    return mkApp (← field ty "eq") #[← `(DCC[$ty:gen_dcc_loc] $x), ← `(DCC[$ty:gen_dcc_loc] $y)]
  | `(DCC[$ty:gen_dcc_loc] !($x:gen_dcc))                  => do
    return mkApp (← field ty "bang") #[← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] &($x:gen_dcc))                  => do
    return mkApp (← field ty "box") #[← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] *($α:gen_dcc))                  => do
    return mkApp (← field ty "unbox") #[← `(DCC[$ty:gen_dcc_loc] $α)]
  | `(DCC[$ty:gen_dcc_loc] Eql($f_α:gen_dcc))                        => do
    return mkApp (← field ty "eql") #[← `(DCC[$ty:gen_dcc_loc] $f_α)]
  | `(DCC[$ty:gen_dcc_loc] refl($f_α:gen_dcc))                       => do
    return mkApp (← field ty "refl") #[← `(DCC[$ty:gen_dcc_loc] $f_α)]
  | `(DCC[$ty:gen_dcc_loc] ($f:gen_dcc $x:gen_dcc))                  => do
    return mkApp (← field ty "app") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $x:gen_dcc)]
  | `(DCC[$ty:gen_dcc_loc] ($f:gen_dcc $x:gen_dcc $xs:gen_dcc*))     =>
    `(DCC[$ty:gen_dcc_loc] (($f:gen_dcc $x:gen_dcc) $xs:gen_dcc*))
  | `(DCC[$ty:gen_dcc_loc] `($β:gen_dcc, $x:gen_dcc))                => do
    return mkApp (← field ty "quot") #[← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] Λ($α:gen_dcc, $β:gen_dcc, $e:gen_dcc))    => do
    return mkApp (← field ty "curr") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $e)]
  | `(DCC[$ty:gen_dcc_loc] !<$x:gen_dcc>)    => do
    return mkApp (← field ty "map") #[← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] $<$x:gen_dcc>)    => do
    return mkApp (← field ty "fmap") #[← `(DCC[$ty:gen_dcc_loc] $x)]
  | `(DCC[$ty:gen_dcc_loc] !Λ($α:gen_dcc, $β:gen_dcc, $e:gen_dcc))    => do
    return mkApp (← field ty "curr'") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $e)]
  | `(DCC[$ty:gen_dcc_loc] Π($α:gen_dcc, $β:gen_dcc))                => do
    return mkApp (← field ty "pi") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] ⟦$β:gen_dcc⟧⟨$x:gen_dcc, $y:gen_dcc⟩)     => do
    return mkApp (← field ty "pair") #[← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x), ← `(DCC[$ty:gen_dcc_loc] $y)]
  | `(DCC[$ty:gen_dcc_loc] ⟦$β:gen_dcc⟧($x, $y))                     => do
    return mkApp (← field ty "mkc") #[← `(DCC[$ty:gen_dcc_loc] $β), ← `(DCC[$ty:gen_dcc_loc] $x), ← `(DCC[$ty:gen_dcc_loc] $y)]
  | `(DCC[$ty:gen_dcc_loc] Sort $m:term)                             => do
    return mkApp (← field ty "sort") #[m]
  | `(DCC[$ty:gen_dcc_loc] Σ($α:gen_dcc, $β:gen_dcc))                => do
    return mkApp (← field ty "sigma") #[← `(DCC[$ty:gen_dcc_loc] $α), ← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] Coup($β:gen_dcc))                         => do
    return mkApp (← field ty "coup") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] Fstc($β:gen_dcc))                         => do
    return mkApp (← field ty "fstc") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] Sndc($β:gen_dcc))                         => do
    return mkApp (← field ty "sndc") #[← `(DCC[$ty:gen_dcc_loc] $β)]
  | `(DCC[$ty:gen_dcc_loc] Id($α:gen_dcc))                           => do
    return mkApp (← field ty "id") #[← `(DCC[$ty:gen_dcc_loc] $α)]
  | `(DCC[$ty:gen_dcc_loc] $f:gen_dcc ∘' $g:gen_dcc)                 => do
    return mkApp (← field ty "comp'") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $g:gen_dcc)]
  | `(DCC[$ty:gen_dcc_loc] $f:gen_dcc ∘ $g:gen_dcc)                  => do
    return mkApp (← field ty "comp") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $g:gen_dcc)]
  | `(DCC[$ty:gen_dcc_loc] $f:gen_dcc ∘∘ $g:gen_dcc)                  => do
    return mkApp (← field ty "comp₂") #[← `(DCC[$ty:gen_dcc_loc] $f:gen_dcc), ← `(DCC[$ty:gen_dcc_loc] $g:gen_dcc)]
  | `(DCC[$_ty:gen_dcc_loc] #($t:term))                              => `($t)
  | `(DCC[$_ty:gen_dcc_loc] $idt:ident)                              => `($idt:term)
  | `(DCC[$ty:gen_dcc_loc] ($t:gen_dcc))                             => `(DCC[$ty:gen_dcc_loc] $t)

syntax "gen_dsl" str "for" term : command

macro_rules
  | `(gen_dsl $pre:str for $ty:ident) =>
    `(command| macro $pre:str exp:gen_dcc : term => `(DCC[$ty:ident] $$exp))

gen_dsl "DCC" for Expr

#eval (DCC Sort 0)

def runDcc : Lean.Syntax → Lean.MacroM Lean.Syntax
  | `(gen_dcc| $e:gen_dcc) => `(DCC $e:gen_dcc)

inductive Bang.{u} (α : Type u) where
  | bang : α → Bang α
deriving Lean.ToExpr

inductive Shared.{u} (α : Type u) where
  | share : α → Shared α
deriving Lean.ToExpr

def Shared.deref.{u} {α : Type u} (s : Shared α) : α :=
  match s with
  | ⟨s⟩ => s

def Shared.map.{u, v} {α : Type u} {β : α → Type v} (f : ∀ (x : α), β x) (s : Shared α) : Bang (β s.deref) :=
  match s with
  | ⟨s⟩ => ⟨f s⟩

def Shared.fmap.{u, v} {α : Type u} {β : α → Type v} (f : ∀ (x : α), β x) (s : Shared α) : Shared (β s.deref) :=
  match s with
  | ⟨s⟩ => ⟨f s⟩

#check Shared.deref
