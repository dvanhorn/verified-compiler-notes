# verified-compiler-notes

A Verso-based Lean project for notes on using Lean to model programming language
semantics and compilation.

This project is based on the Verso `textbook` template:
- same manual genre setup
- inline Lean checking
- `savedLean`/`savedImport` support for extracting example code

## Build

```bash
cd verified-compiler-notes
lake exe verified-compiler-notes
```

The manual text lives in `VerifiedCompilerNotes.lean`, with an example chapter in
`VerifiedCompilerNotes/Semantics.lean`.
