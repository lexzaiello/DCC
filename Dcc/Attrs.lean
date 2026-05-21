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
  Lean.Meta.registerSimpAttr `dcc_rel ("Simplifies using theorems about DCC relations")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_reduce ("Simplifies by forcing DCC eta and affine reduction")

declare_aesop_rule_sets [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]

macro "dcc_simp" : tactic =>
  `(tactic| simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, dcc_force_reduce])

macro "dcc_simp?" : tactic =>
  `(tactic| simp? [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, dcc_force_reduce])

macro "dcc_simp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, dcc_force_reduce, $args,*])

macro "dcc_simp?" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp? [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, dcc_force_reduce, $args,*])

macro "dcc_simp_all" : tactic =>
  `(tactic| simp_all [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, dcc_force_reduce])

macro "dcc_simp_all?" : tactic =>
  `(tactic| simp_all? [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, dcc_force_reduce])

macro "dcc_simp_all" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp_all [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, dcc_force_reduce, $args,*])

macro "dcc_simp_all?" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp_all? [dcc_step, dcc_reduce, dcc_size, dcc_judge, dcc_rel, dcc_force_reduce, $args,*])

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
