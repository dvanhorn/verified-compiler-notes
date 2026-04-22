import VersoManual
import VerifiedCompilerNotes.Build

open Verso Doc
open Verso.Genre Manual

def main := manualMain (%doc VerifiedCompilerNotes)
  (extraSteps := [buildExercises])
  (config := pdfConfig)
