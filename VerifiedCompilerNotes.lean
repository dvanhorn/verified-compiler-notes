/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Van Horn
-/

import VersoManual
import VerifiedCompilerNotes.Meta.Lean
import VerifiedCompilerNotes.Papers

-- This is a chapter that's included
import VerifiedCompilerNotes.Semantics

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that is in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean


open VerifiedCompilerNotes

set_option pp.rawOnError true


#doc (Manual) "Verified Compiler Notes" =>

%%%
authors := ["David Van Horn"]
%%%

{index}[compiler]
This project is a set of Verso notes on expressing programming language syntax,
semantics, and compiler mappings in Lean.

The notes are modeled after the Verso `textbook` template and use the
same inline Lean workflow, so Lean code examples are checked as part of the
book build.

To build the notes, run:

`lake exe verified-compiler-notes`

# Lean in a Notes Setting

Lean code can be written directly in the notes with the `{lean}` block and
role forms. The following command-line example is elaborated in the same Lean
process as the text.

```lean
def introArithmetic : Nat := 2 + 2
```

Use the {lean}`savedLean` block to keep a copy of code in extracted example files.

```savedComment
Example code for extracted file `CompilerExamples.lean`.
```
```savedLean
def compilerExample : Nat := 1 + 3
```

When named, a code block can be rendered back with {lean}`leanOutput`:

```savedLean (name := valOut)
#eval 2 + 2
```
```leanOutput valOut
4
```

{include 1 VerifiedCompilerNotes.Semantics}

# Notes on Modeling Compilation

{index}[semantics]
Formal notes of this style are especially useful when you can keep source
syntax, target instructions, and correctness lemmas close together. The next
chapter gives a compact worked example with an expression compiler.

# References

{index}[index]
The index includes entries for:
{index}[expression]
{index}[compilation]

{theIndex}
