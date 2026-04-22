/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import VerifiedCompilerNotes.Build

open Verso Doc
open Verso.Genre Manual

def main := manualMain (%doc VerifiedCompilerNotes)
  (extraSteps := [buildExercises])
  (config := htmlConfig)
