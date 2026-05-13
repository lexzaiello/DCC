/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoSlides
import DccSlides

open VersoSlides

def main : IO UInt32 :=
  slidesMain
    (config := { theme := "white", slideNumber := true,
                 transition := "fade", center := true, mathPrelude :=
      "\\def\\RR{\\mathbb{R}}\n\\newcommand{\\Hom}[2]{\\mathrm{Hom}(#1, #2)}\n", margin := 0 })
    (doc := %doc DccSlides)
