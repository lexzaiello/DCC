import Dcc.Ast
import Dcc.Types
import Mathlib.Tactic
import Lean

open Lean.Meta (registerSimpAttr)
open Lean.Meta (SimpExtension)

initialize simp_dcc : SimpExtension ←
  registerSimpAttr `simp_dcc ""
