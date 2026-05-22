import Lean
import Lean.Elab
import Aesop
import Mathlib.Data.Nat.Notation

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_step ("Simplifies using single-step reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_reduce ("Simplifies using DCC reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_size ("Simplifies using size theorems in DCC")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_judge ("Simplifies using theorems about inference in DCC")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_rel ("Simplifies using theorems about DCC relations")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_reduce ("Simplifies by forcing DCC eta and affine reduction")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_rel ("Simplifies relation instances eagerly")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_infer ("Runs the type-checker")

declare_aesop_rule_sets [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]

declare_syntax_cat dcc_cmd
declare_syntax_cat dcc_flag
declare_syntax_cat dcc_target
declare_syntax_cat dcc_loc

syntax "dcc_simp"                                 : dcc_cmd
syntax "dcc_simp_all"                             : dcc_cmd

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

def flag_priority (for_flag : Flag) (in_f : Flag) : ℕ :=
  match in_f with
  | .group x xs => (flag_priority for_flag x) + (flag_priority for_flag xs)
  | f => if for_flag == f then 1 else 0

syntax (name := flagq) "?"                        : dcc_flag
syntax (name := flagb) "!"                        : dcc_flag
syntax (name := flagc) ":"                        : dcc_flag
syntax (name := flagg) "(" dcc_flag+ ")"          : dcc_flag

syntax (name := parseFlag) "f{" dcc_flag "}"      : term

partial def parse_flag [Monad m] [Lean.MonadError m] [Lean.MonadQuotation m]
  (stx : Lean.TSyntax `dcc_flag) : m Flag :=
  match stx with
  | `(dcc_flag| ?) => return .trace
  | `(dcc_flag| !) => return .force
  | `(dcc_flag| :) => return .infer
  | `(dcc_flag| ($f:dcc_flag $fs:dcc_flag*)) => do
    let f' ← parse_flag f
    let fs' ← parse_flag (← `(dcc_flag| ($fs:dcc_flag*)))
    return .group f' fs'
  | _ => throwErrorAt stx "unexpected dcc_flag syntax"

syntax "[" Lean.Parser.Tactic.simpLemma,* "]"     : dcc_target
syntax ("at"
  (Lean.Parser.Tactic.locationWildcard <|>
                Lean.Parser.Tactic.locationHyp))  : dcc_loc
syntax "nowhere"                                  : dcc_loc

syntax dcc_cmd dcc_flag* dcc_target* dcc_loc*     : tactic

-- TODO: debug name checking right
def has_flag (flag : Flag) (flags : List Flag) : Bool :=
  0 < (flags.map (flag_priority flag)).sum

abbrev SSet := Lean.Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ","

abbrev STgt := Lean.TSyntax `dcc_target

abbrev SSet.concat (a b : SSet) : SSet :=
  a.getElems ++ b.getElems

abbrev unwrap_locs (stx : Lean.TSyntaxArray `dcc_loc) : Lean.MacroM (Lean.TSyntax `dcc_loc) :=
  match stx.toList with
  | [locs] => pure locs
  | _      => `(dcc_loc| nowhere)

abbrev unwrap_target (stx : Lean.TSyntaxArray `dcc_target) : SSet :=
  match stx with
  | ⟨[tgt]⟩ =>
    match tgt with
    | `(dcc_target| [$lms,*]) => lms
    | _                       => ⟨⟨[]⟩⟩
  | _                         => ⟨⟨[]⟩⟩

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

def dcc_base : Lean.MacroM SSet := do
  return ⟨⟨[← `(Lean.Parser.Tactic.simpLemma| dcc_step),
    ← `(Lean.Parser.Tactic.simpLemma| dcc_reduce),
    ← `(Lean.Parser.Tactic.simpLemma| dcc_size),
    ← `(Lean.Parser.Tactic.simpLemma| dcc_judge),
    ← `(Lean.Parser.Tactic.simpLemma| dcc_rel)]⟩⟩

def dcc_dangerous_force : Lean.MacroM SSet := do
  return ⟨⟨[← `(Lean.Parser.Tactic.simpLemma| dcc_force_reduce),
    ← `(Lean.Parser.Tactic.simpLemma| dcc_force_rel)]⟩⟩

def dcc_infer_force : Lean.MacroM SSet := do
  return ⟨⟨[← `(dcc_force_infer)]⟩⟩

def prioritize_thms (n : ℕ) (thms : SSet) : SSet := thms.getElems.take n

macro_rules
  | `(tactic| $cmd:dcc_cmd $flags:dcc_flag* $tgt:dcc_target* $loc:dcc_loc*) => do
    let loc   := ← unwrap_locs loc
    let flags := flags.toList
    -- Number of ! flags dictates which number of "dangerous" sets to use
    -- ! = just dcc_force_reduce, !! = dcc_force_rel
    let flag_priority (fname : Lean.Name) := ((Option.getD · 0) <| flags.firstM (fun (flag : Lean.TSyntax `dcc_flag) =>
        match priority fname flag with
        | .zero => Option.none
        | n@(.succ _) => .some n))

    -- Up to severity of dangerous thms
    let dangerous_thms := prioritize_thms (flag_priority ``flagb) (thms := ← dcc_dangerous_force)
    -- Activate with : flag
    let infer_thms     := prioritize_thms (flag_priority ``flagc) (thms := ← dcc_infer_force)
    let user_thms      := unwrap_target tgt
    -- Do dangerous theorems first. This is less likely (?) to cause infinite loops
    let thms           := ((infer_thms.concat dangerous_thms).concat (← dcc_base)).concat user_thms

    let cases? (a b : Lean.MacroM (Lean.TSyntax `tactic)) : Lean.MacroM (Lean.TSyntax `tactic) := do
      if flags.contains (← `(dcc_flag| ?)) then a else b

    let discharge (thms : SSet) : Lean.MacroM (Lean.TSyntax `tactic) := do
      match cmd, loc with
      | `(dcc_cmd| dcc_simp), `(dcc_loc| at [$locs,*]) =>
        cases? `(tactic| simp? [$thms,*] at [$locs,*]) `(tactic| simp [$thms,*] at [$locs,*])
      | `(dcc_cmd| dcc_simp), _ =>
        cases? `(tactic| simp? [$thms,*]) `(tactic| simp [$thms,*])
      | `(dcc_cmd| dcc_simp_all), _ =>
        cases? `(tactic| simp_all? [$thms,*]) `(tactic| simp_all [$thms,*])
      | _, _ => Lean.Macro.throwUnsupported
    discharge thms

/-macro_rules
  | `(tactic| dcc_simp [$args,*] at $loc) => do
    `(tactic| (simp [$(← conc dcc_base (pure args)),*] at $loc))
  | `(tactic| dcc_simp [$args,*]) => do
    `(tactic| (simp [$(← conc dcc_base (pure args)),*]))
  | `(tactic| dcc_simp_all [$args,*]) => do
    `(tactic| (simp_all [$(← conc dcc_base (pure args)),*]))
  | `(tactic| dcc_simp at $loc) => `(tactic| dcc_simp [] at $loc)
  | `(tactic| dcc_simp_all) => `(tactic| dcc_simp_all [])
  | `(tactic| dcc_simp) => `(tactic| dcc_simp [])
  | `(tactic| $cmd:dcc_cmd ! [$args,*] at $loc) => `(tactic| $cmd:dcc_cmd [dcc_force_reduce, $args,*] at $loc)
  | `(tactic| $cmd:dcc_cmd ! [$args,*]) => `(tactic| $cmd:dcc_cmd [dcc_force_reduce, $args,*])
  | `(tactic| $cmd:dcc_cmd !) => `(tactic| $cmd:dcc_cmd ! [])-/

/-macro "dcc_simp" : tactic =>
  `(tactic| ((try simp only [dcc_infer]); simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel]))

macro "dcc_simp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| ((try simp only [dcc_infer]); simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, $args,*]))

macro "dcc_simp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" "at" loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic| ((try simp only [dcc_infer] at $loc); simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, $args,*] at $loc))

macro "dcc_simp" "at" loc:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic| ((try simp only [dcc_infer] at $loc); simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel] at $loc))

macro "dcc_simp" "at" loc:Lean.Parser.Tactic.locationWildcard : tactic =>
  `(tactic| ((try simp only [dcc_infer] at $loc); simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel] at $loc))

macro "dcc_simp_all" : tactic =>
  `(tactic| ((try simp only [dcc_infer]); simp_all [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel]))

macro "dcc_simp_all" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| ((try simp only [dcc_infer]); simp_all [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, $args,*]))

macro "dcc_simp_all!" : tactic =>
  `(tactic| dcc_simp_all [dcc_force_reduce, dcc_force_rel])

macro "dcc_simp_all" : tactic =>
  `(tactic| dcc_simp [dcc_force_reduce, dcc_force_rel])-/

syntax "dcc_aesop" (Aesop.tactic_clause)* : tactic
syntax "dcc_aesop?" (Aesop.tactic_clause)* : tactic
syntax "dcc_aesop!" (Aesop.tactic_clause)* : tactic

macro_rules
  | `(tactic| dcc_aesop $clauses:Aesop.tactic_clause*) =>
    `(tactic| aesop (rule_sets := [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]) $clauses*)
  | `(tactic| dcc_aesop? $clauses:Aesop.tactic_clause*) =>
    `(tactic| aesop? (rule_sets := [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]) $clauses*)
  | `(tactic| dcc_aesop! $clauses:Aesop.tactic_clause*) =>
    `(tactic| aesop (config := {terminal := false, warnOnNonterminal := false}) (rule_sets := [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]) $clauses*)
