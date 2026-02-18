/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Dcc

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso. Here, they're used to have the text refer to Verso code used in the text's
-- own source.
open Verso.Genre.Manual.InlineLean

-- This gets access to tools for showing Lean code that's loaded from external modules.
open Verso.Code.External

set_option pp.rawOnError true

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleProject "./"
set_option verso.exampleModule "Dcc.Relations"

#doc (Manual) "DCC: The Dependently-typed Combinator Calculus" =>
%%%
authors := ["Alexandra Aiello"]
shortTitle := "The Dependently-typed Combinator Calculus"
%%%

{index}[DCC]
Reference and explainer of the Dependently-typed Combinator Calculus (DCC).

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
