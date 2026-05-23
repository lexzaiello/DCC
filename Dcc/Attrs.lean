import Lean
import Lean.Elab
import Aesop

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_step ("Simplifies using single-step reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_reduce ("Simplifies using DCC reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_size ("Simplifies using size theorems in DCC")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_judge ("Simplifies using theorems about inference in DCC")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_infer ("Dsimp DCC inference function")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_rel ("Simplifies using theorems about DCC relations")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_reduce ("Simplifies by forcing DCC eta and affine reduction")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_aff ("Simplifies by forcing DCC eta and affine reduction")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_eta ("Simplifies by forcing DCC eta and affine reduction")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_rel ("Simplifies by forcing DCC eta and affine reduction")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_infer ("Runs the type-checker")

declare_aesop_rule_sets [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]

namespace attrs

declare_syntax_cat dcc_cmd
declare_syntax_cat dcc_flag
declare_syntax_cat dcc_target
declare_syntax_cat dcc_loc

syntax "dcc_simp"                                 : dcc_cmd
syntax "dcc_simp_all"                             : dcc_cmd
syntax "dcc_simp?"                                : dcc_cmd
syntax "dcc_simp_all?"                            : dcc_cmd

/-
Flags: see later for explanation
-/

inductive Flag where
  -- ?
  | trace : Flag
  -- !
  | force : Flag
  -- :
  | infer : Flag
  -- (!!!!!)
  | group : Flag → Flag → Flag
deriving Nonempty, Inhabited, BEq

def flag_priority (for_flag : Flag) (in_f : Flag) : Nat :=
  match in_f with
  | .group x xs => (flag_priority for_flag x) + (flag_priority for_flag xs)
  | f => if for_flag == f then 1 else 0

def Flag.has (flag : Flag) (flags : List Flag) : Bool :=
  0 < (flags.map (flag_priority flag)).sum

syntax "?" : dcc_flag
syntax "!" : dcc_flag
syntax "∶" : dcc_flag
syntax "(" dcc_flag+ ")"          : dcc_flag

syntax "f{" dcc_flag "}"          : term

partial def parse_flag  (stx : Lean.TSyntax `dcc_flag) : Lean.MacroM Flag :=
  match stx with
  | `(dcc_flag| ?) => return .trace
  | `(dcc_flag| !) => return .force
  | `(dcc_flag| ∶) => return .infer
  | `(dcc_flag| ($f:dcc_flag $x:dcc_flag)) => do
    let f' ← parse_flag f
    let x' ← parse_flag x
    return .group f' x'
  | `(dcc_flag| ($f:dcc_flag $fs:dcc_flag*)) => do
    let f' ← parse_flag f
    let fs' ← parse_flag (← `(dcc_flag| ($fs:dcc_flag*)))
    return .group f' fs'
  | _ => Lean.Macro.throwErrorAt stx "unexpected dcc_flag syntax"

syntax (Lean.Parser.Tactic.locationWildcard <|>
                Lean.Parser.Tactic.locationHyp)   : dcc_loc

syntax "[" Lean.Parser.Tactic.simpLemma,* "]"            : dcc_target
syntax ("at" (Lean.Parser.Tactic.locationWildcard <|>
                        Lean.Parser.Tactic.locationHyp)) : dcc_loc
syntax "nowhere"                                         : dcc_loc

syntax dcc_cmd dcc_flag* dcc_target* dcc_loc*     : tactic
syntax dcc_cmd dcc_flag* dcc_target* dcc_loc*     : conv

abbrev Dispatcher := Lean.TSyntax `tactic

abbrev SItems := Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma)
abbrev SSet := Dispatcher × SItems

abbrev STgt := Lean.TSyntax `dcc_target

abbrev SSet.concat (a b : SSet) : SSet :=
  match a, b with
  | ⟨dsp, a⟩, ⟨_, b⟩ =>
    ⟨dsp, a ++ b⟩

abbrev unwrap_locs (stx : Lean.TSyntaxArray `dcc_loc) : Lean.MacroM (Lean.TSyntax `dcc_loc) :=
  match stx.toList with
  | [locs] => pure locs
  | _      => `(dcc_loc| nowhere)

abbrev unwrap_target (stx : Lean.TSyntaxArray `dcc_target) : Lean.MacroM SSet :=
  match stx with
  | ⟨[tgt]⟩ =>
    match tgt with
    | `(dcc_target| [$lms,*]) => (⟨·, lms⟩) <$> `(tactic| simp)
    | _                       => (⟨·, ⟨[]⟩⟩) <$> `(tactic| simp)
  | _                         => (⟨·, ⟨[]⟩⟩) <$> `(tactic| simp)

abbrev get_flags (stx : Lean.TSyntaxArray `dcc_flag) : Lean.MacroM (List Flag) :=
  stx.toList.mapM parse_flag

/-
DCC top-level simp-sets:

- base - these are almost always safe
- dangerous_force - these will run reduction eagerly
  - dcc_force_rel is the most "dangerous" simp set we have
- infer_force - this will dsimp type-checker equalities

! = dangerous_force top-set
: = infer_force top-set

repeat ! or : to indicate how dangerous to go (how many sub-sets to choose. they are ordered as such)
-/

def mk_set (nms : Array Lean.Name) : Lean.MacroM SItems :=
  nms.mapM (`(Lean.Parser.Tactic.simpLemma| $(Lean.mkIdent ·):ident))

def dcc_base : Lean.MacroM SSet := do
  return ⟨← `(tactic| simp), ← mk_set ⟨[`dcc_step, `dcc_reduce, `dcc_size, `dcc_judge, `dcc_rel]⟩⟩

def dcc_dangerous_force : Lean.MacroM SSet := do
  return ⟨← `(tactic| simp), ← mk_set ⟨[`dcc_force_reduce, `dcc_force_rel]⟩⟩

def dcc_infer_force : Lean.MacroM SSet := do
  return ⟨← `(tactic| dsimp only), ← mk_set ⟨[`dcc_force_infer]⟩⟩

def prioritize_thms (n : Nat) (thms : SSet) : SSet :=
  match thms with
  | ⟨dsp, thms⟩ => ⟨dsp, thms.take n⟩

end attrs

open attrs in macro_rules
  | `(conv| $cmd:dcc_cmd $flags:dcc_flag* $tgt:dcc_target* $loc:dcc_loc*) =>
    `(conv| tactic => $cmd:dcc_cmd $flags:dcc_flag* $tgt:dcc_target* $loc:dcc_loc*)
  | `(tactic| dcc_simp_all? $flags:dcc_flag* $tgt:dcc_target* $loc:dcc_loc*) =>
    `(tactic| dcc_simp_all ? $flags:dcc_flag* $tgt:dcc_target* $loc:dcc_loc*)
  | `(tactic| dcc_simp? $flags:dcc_flag* $tgt:dcc_target* $loc:dcc_loc*) =>
    `(tactic| dcc_simp ? $flags:dcc_flag* $tgt:dcc_target* $loc:dcc_loc*)
  | `(tactic| $cmd:dcc_cmd $flags:dcc_flag* $tgt:dcc_target* $loc:dcc_loc*) => do
    let smp   ← `(tactic| simp)
    let loc   ← unwrap_locs loc
    let flags ← get_flags flags
    -- Number of ! flags dictates which number of "dangerous" sets to use
    -- ! = just dcc_force_reduce, !! = dcc_force_rel
    let flag_priority (fname : Flag) := (flags.map (fun (flag : Flag) => flag_priority fname flag)).sum

    -- Up to severity of dangerous thms
    let dangerous_thms := prioritize_thms (flag_priority .force) (thms := ← dcc_dangerous_force)
    -- Activate with : flag
    let infer_thms     := prioritize_thms (flag_priority .infer) (thms := ← dcc_infer_force)
    let user_thms      ← unwrap_target tgt
    -- Do dangerous theorems first. This is less likely (?) to cause infinite loops
    let base           ← dcc_base
    let thms           := base.concat (dangerous_thms.concat user_thms)

    let cases? (a b : Lean.MacroM (Lean.TSyntax `tactic)) : Lean.MacroM (Lean.TSyntax `tactic) := do
      if flags.contains .trace then a else b

    let discharge (thms : SSet) : Lean.MacroM (Lean.TSyntax `tactic) := do
      let dsp  := thms.1
      let thms := thms.2
      match cmd, loc with
      | `(dcc_cmd| dcc_simp), `(dcc_loc| at $locs) =>
        if dsp == smp then
          cases? `(tactic| simp? [$thms,*] at $locs) `(tactic| simp [$thms,*] at $locs)
        else cases? `(tactic| try dsimp? only [$thms,*] at $locs) `(tactic| try dsimp [$thms,*] at $locs)
      | `(dcc_cmd| dcc_simp), _ =>
        if dsp == smp then
          cases? `(tactic| simp? [$thms,*]) `(tactic| simp [$thms,*])
        else
          cases? `(tactic| try dsimp? only [$thms,*]) `(tactic| try dsimp only [$thms,*])
      | `(dcc_cmd| dcc_simp_all), _ =>
        if dsp == smp then
          cases? `(tactic| simp_all? [$thms,*]) `(tactic| simp_all [$thms,*])
        else
          cases? `(tactic| try simp_all? only [$thms,*]) `(tactic| try simp_all only [$thms,*])
      | _, _ => Lean.Macro.throwUnsupported
    let do_infer ← discharge infer_thms
    let do_rst   ← discharge thms
    `(tactic| (
      first
      | $do_rst:tactic
      | $do_infer:tactic
      | ($do_infer; $do_rst)))

syntax "dcc_aesop" (Aesop.tactic_clause)*  : tactic
syntax "dcc_aesop?" (Aesop.tactic_clause)* : tactic
syntax "dcc_aesop!" (Aesop.tactic_clause)* : tactic

macro_rules
  | `(tactic| dcc_aesop $clauses:Aesop.tactic_clause*) =>
    `(tactic| aesop (rule_sets := [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]) $clauses*)
  | `(tactic| dcc_aesop? $clauses:Aesop.tactic_clause*) =>
    `(tactic| aesop? (rule_sets := [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]) $clauses*)
  | `(tactic| dcc_aesop! $clauses:Aesop.tactic_clause*) =>
    `(tactic| aesop (config := {terminal := false, warnOnNonterminal := false}) (rule_sets := [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]) $clauses*)

open Lean Macro Parser.Command
open Lean (Parser.Command.derivingClass)
open Lean.Parser.Term

namespace GenAst

abbrev GenExt := TSyntax `ident × Bool

inductive Flag where
  | index   : TSyntax `term                   → Flag
  | enc     : TSyntax `ident → TSyntax `term  → Flag
  | dec     : TSyntax `ident → TSyntax `term  → Flag
  | src     : TSyntax `ident                  → Flag
  | as      : TSyntax `ident                  → Flag
  | ext     : Array GenExt                    → Flag
  | deriv   : Array (TSyntax ``derivingClass) → Flag
  | into    : TSyntax `term                   → Flag
  | and     : Flag → Flag                     → Flag
  | nil     : Flag
deriving Repr, Inhabited, Nonempty

instance : Append Flag := ⟨Flag.and⟩

--structure GenCfg where

declare_syntax_cat gen_flag
declare_syntax_cat gen_flag_set
declare_syntax_cat gen_flag_ext

syntax ident                       : gen_flag_ext
syntax ident "*"                   : gen_flag_ext

syntax ident "decoded_by" term            : gen_flag
syntax ident "encoded_by" term            : gen_flag
syntax "from" ident                       : gen_flag
syntax "as" ident                         : gen_flag
syntax "into" term                        : gen_flag
syntax "with" gen_flag_ext,*              : gen_flag
syntax "deriving" derivingClass,*         : gen_flag
syntax "indexed" term                     : gen_flag

syntax gen_flag*                          : gen_flag_set

def Flag.stx (flag : Flag) : Lean.MacroM (TSyntax `gen_flag_set) :=
  match flag with
  | .index tm    => `(gen_flag_set| indexed $tm:term)
  | .enc idt e   => `(gen_flag_set| $idt:ident encoded_by $e:term)
  | .dec idt e   => `(gen_flag_set| $idt:ident decoded_by $e:term)
  | .src e       => `(gen_flag_set| from $e)
  | .as  e       => `(gen_flag_set| as $e)
  | .ext e       => do
    let exts ← e.mapM (fun e => match e with
      | ⟨idt, .true⟩  => `(gen_flag_ext| $idt:ident *)
      | ⟨idt, .false⟩ => `(gen_flag_ext| $idt:ident))
    `(gen_flag_set| with $exts,*)
  | .deriv e     => `(gen_flag_set| deriving $e,*)
  | .into e      => `(gen_flag_set| into $e)
  | .and a b     => do
    let a' ← a.stx
    let b' ← b.stx
    match a' with
    | `(gen_flag_set| $x:gen_flag*) =>
      match b' with
      | `(gen_flag_set| $y:gen_flag*) =>
        `(gen_flag_set| $(x ++ y):gen_flag*)
      | _ => throwUnsupported
    | _ => throwUnsupported
  | .nil     => `(gen_flag_set| $(⟨[]⟩):gen_flag*)

def parse_ext (stx : TSyntax `gen_flag_ext) : Option GenExt :=
  match stx with
  | `(gen_flag_ext| $idt:ident *) => .some ⟨idt, True⟩
  | `(gen_flag_ext| $idt:ident)   => .some ⟨idt, False⟩
  | _ => .none

def parse_flag (stx : TSyntax `gen_flag) : (Option Flag) :=
  match stx with
  | `(gen_flag| from $idt:ident) => .some <| .src idt
  | `(gen_flag| as $idt:ident) => .some <| .as idt
  | `(gen_flag| with $idts:gen_flag_ext,*) => do
    let exts ← idts.getElems.toList.mapM parse_ext
    .some <| .ext ⟨exts⟩
  | `(gen_flag| deriving $idts:derivingClass,*) => .some <| .deriv idts
  | `(gen_flag| into $tm:term) => .some <| .into tm
  | `(gen_flag| $idt:ident decoded_by $tm:term) => .some <| .dec idt tm
  | `(gen_flag| $idt:ident encoded_by $tm:term) => .some <| .enc idt tm
  | `(gen_flag| indexed $tm:term) => .some <| .index tm
  | _ => .none

def parse_flags (stx : TSyntax `gen_flag_set) : Flag :=
  match stx with
  | `(gen_flag_set| $flags:gen_flag*) =>
    (Array.foldr Flag.and Flag.nil) <$> flags.mapM parse_flag
    |> (·.getD .nil)
  | _ => .nil

def Flag.get! {m : Type → Type} {α : Type} [Monad m] [MonadRef m]
  [MonadError m]
  (getter : Flag → Option α) (flag : Flag) : m α :=
  match getter flag with
  | .some x => pure x
  | _ => throwError m!"missing a required flag"

def Flag.get!' {α : Type}  (getter : Flag → Option α) (flag : Flag) : MacroM α :=
  match getter flag with
  | .some x => pure x
  | _ => Macro.throwError "missing a required flag"

def Flag.find? {α : Type} (f : Flag → Option α) (flag : Flag) : Option α :=
  match flag with
  | .and a b =>
    a.find? f <|> b.find? f
  | .nil => .none
  | flag => f flag

def Flag.indexes? (flag : Flag) : Option (TSyntax `term) :=
  flag.find? (fun flag => match flag with
    | .index tm => .some tm
    | _ => .none)

partial def Flag.elim? (flag : Flag) : Option (TSyntax `term) :=
  let rec get_elim (tm : TSyntax `term) : Option (TSyntax `term) :=
    match tm with
    | `(term| $_a:term → $xs:term) => get_elim xs
    | `(term| Sort $_m)
    | `(term| Type $_m)
    | `(term| Prop)    => .some tm
    | _ => .none

  flag.find? (fun flag => match flag with
    | .index tm => get_elim tm
    | _ => .none)

partial def Flag.index_n (flag : Flag) (n : Nat) : Option (TSyntax `term) :=
  let rec tm_param_n (n : Nat) (tm : TSyntax `term) : Option (TSyntax `term) :=
    match tm with
    | `(term| $a:term → $xs:term) =>
      match n with
      | .zero => .some a
      | .succ n' =>
        tm_param_n n' xs
    | _ => .none

  flag.find? (fun flag => match flag with
    | .index tm => tm_param_n n tm
    | _ => .none)

def Flag.encoder? (for_idt : TSyntax `ident) (flag : Flag) : Option (TSyntax `term) :=
  flag.find? (fun flag => match flag with
    | .enc idt tm =>
      if idt == for_idt then .some tm else .none
    | _ => .none)

def Flag.decoder? (for_idt : TSyntax `ident) (flag : Flag) : Option (TSyntax `term) :=
  flag.find? (fun flag => match flag with
    | .dec idt tm =>
      if idt == for_idt then .some tm else .none
    | _ => .none)

def Flag.from? (flag : Flag) : Option (TSyntax `ident) :=
  flag.find? (fun flag => match flag with
    | .src e => .some e
    | _ => .none)

def Flag.as? (flag : Flag) : Option (TSyntax `ident) :=
  flag.find? (fun flag => match flag with
    | .as e => .some e
    | _ => .none)

def Flag.with? (flag : Flag) : Option (Array GenExt) :=
  flag.find? (fun flag => match flag with
    | .ext e => .some e
    | _ => .none)

def Flag.with! (flag : Flag) : Array GenExt :=
  flag.with?.getD #[]

def Flag.as! {m : Type → Type} [Monad m] [MonadRef m]
  [MonadError m] (flag : Flag) : m (TSyntax `ident) :=
  flag.get! Flag.as?

def Flag.as!' (flag : Flag) : MacroM (TSyntax `ident) :=
  flag.get!' Flag.as?

def Flag.deriving? (flag : Flag) : Option (Array (TSyntax ``derivingClass)) :=
  flag.find? (fun flag => match flag with
    | .deriv e => .some e
    | _ => .none)

def Flag.into? (flag : Flag) : Option (TSyntax `term) :=
  flag.find? (fun flag => match flag with
    | .into e => .some e
    | _ => .none)

end GenAst

syntax (name := dcc_gen) "dcc_gen" gen_flag_set : attr

open Lean Macro Parser.Command in
open Lean (Parser.Command.derivingClass) in
open Lean.Parser.Term in
open GenAst in
initialize impl_dcc_gen : ParametricAttribute Flag ← registerParametricAttribute {
  name            := ``dcc_gen
  descr           := "marks code generated by DCC with the flags it was generated with"
  getParam nm stx :=
    match stx with
    | `(attr| dcc_gen $flags:gen_flag_set) =>
      return parse_flags flags
    | e => throwError s!"not supported: {e}"
}

namespace GenAst

def Flag.attrs (flags : Flag) : Lean.MacroM (TSyntax ``attrInstance) := do
  let flags_stx ← flags.stx
  `(attrInstance| dcc_gen $flags_stx:gen_flag_set)

def Flag.def_field (s : String) (flag : Flag) : MacroM (TSyntax `ident) := do
  let my_name := (← flag.as!').getId.eraseMacroScopes
  let f_name  := (Lean.Name.mkSimple s).eraseMacroScopes

  return mkIdent (my_name ++ f_name)

def mk_ident (s : String) : TSyntax `ident :=
  mkIdent (Lean.Name.mkSimple s).eraseMacroScopes

def Flag.build_inductive (ctors : TSyntaxArray ``ctor) (flag : Flag) : MacroM (TSyntax `command) := do
  let my_name  ← flag.as!'
  let my_attrs ← flag.attrs
  match flag.deriving? with
  | .some drvs =>
    let my_deriv : Syntax.TSepArray ``derivingClass "," := drvs
    `(command|
      @[$my_attrs]
      inductive $my_name:ident where
      $ctors:ctor*
      deriving $my_deriv,*)
  | .none =>
    `(command|
      @[$my_attrs]
      inductive $my_name:ident where
      $ctors:ctor*)

def Flag.has_wild_card (flag : Flag) : Bool :=
  flag.find? (fun flag =>
    match flag with
    | .ext ⟨exts⟩ =>
      (exts.find? (fun (e : GenExt) => match e with
        | ⟨_, .true⟩ => true
        | _ => false)).map (fun _ => true)
    | _ => .none)
  |> (Option.getD · Bool.false)

end GenAst
