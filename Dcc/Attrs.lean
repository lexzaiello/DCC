import Lean
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
  Lean.Meta.registerSimpAttr `dcc_force_rel ("Simplifies relation instances eagerly")

declare_aesop_rule_sets [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]

syntax dcc_cmd := ("dcc_simp" <|> "dcc_simp_all")

syntax dcc_cmd "?"? "!"? ("[" Lean.Parser.Tactic.simpLemma,* "]")?
  ("at" (Lean.Parser.Tactic.locationWildcard <|> Lean.Parser.Tactic.locationHyp))? : tactic

/-macro_rules
  | `(tactic| dcc_simp [$args,*] at $loc) =>
    `(tactic| ((try simp only [dcc_infer] at $loc); simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, $args,*] at $loc))
  | `(tactic| dcc_simp [$args,*]) =>
    `(tactic| ((try simp only [dcc_infer]); simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, $args,*]))
  | `(tactic| dcc_simp_all [$args,*]) =>
    `(tactic| ((try simp only [dcc_infer]); simp_all [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, $args,*]))
  | `(tactic| dcc_simp at $loc) => `(tactic| dcc_simp [] at $loc)
  | `(tactic| dcc_simp_all) => `(tactic| dcc_simp_all [])
  | `(tactic| dcc_simp) => `(tactic| dcc_simp [])
  | `(tactic| $cmd:dcc_cmd !) => `(tactic| $cmd:dcc_cmd [dcc_force_reduce, dcc_force_rel])-/

macro "dcc_simp" : tactic =>
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
  `(tactic| dcc_simp [dcc_force_reduce, dcc_force_rel])

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
