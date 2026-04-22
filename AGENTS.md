# AGENTS Instructions for verified-compiler-notes

## Scope
These notes are for agents (including Codex) working in this repository.

## Project
This is a Lean + Verso documentation project built from the Verso `textbook` template.

- Main entry: `VerifiedCompilerNotes.lean`
- Build entry point: `VerifiedCompilerNotesMain.lean`
- Primary chapter: `VerifiedCompilerNotes/Semantics.lean`
- Lean version/tooling: managed through `lake` and `elan`/`lakefile`

## Common Commands
- Build and generate docs:
  - `lake exe verified-compiler-notes`
- Serve locally (if needed): run using `verso-templates/serve.py` against `_out/html-multi`

## Git and Repo Hygiene
- Do not commit generated build output:
  - `.lake/`
  - `_out/`
  - `.lake` build artifacts and caches
- Use `.gitignore` accordingly (already present).
- Keep notes and chapter files as Lean source, not generated `.olean`/IR artifacts.

## CI / Pages
- CI workflow exists at `.github/workflows/build.yml`.
- On push/PR it builds and uploads `_out/html-multi` artifact.
- Pages deployment occurs only from `main`.

## Editing and Review Policy
- Keep changes narrowly scoped to requested files.
- Prefer explicit, minimal changes and explain rationale briefly.
- Update `lakefile.toml`, `lake-manifest.json`, and source files consistently when renaming/restructuring projects.

## Content Conventions
- Follow the existing Manual-style section structure and `Manual`/`lean` block usage.
- Use `savedLean`/`savedImport` where example code extraction is intended.
- Prefer small, self-contained semantic chapters that remain compilation-checkable.
