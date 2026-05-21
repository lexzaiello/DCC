import Lean
import Aesop

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_step ("Simplifies using single-step reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_reduce ("Simplifies using single-step reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_size ("Simplifies using single-step reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_judge ("Simplifies using single-step reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_rel ("Simplifies using single-step reduction theorems")

initialize do pure () <*
  Lean.Meta.registerSimpAttr `dcc_force_reduce ("Simplifies using single-step reduction theorems")

declare_aesop_rule_sets [DccStep, DccReduce, DccSize, DccJudge, DccRel, DccForceReduce]
