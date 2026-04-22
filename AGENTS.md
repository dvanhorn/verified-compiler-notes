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
  - On this machine, if architecture/link issues recur, prefer:
    - `arch -arm64 env CFLAGS='-arch arm64' CXXFLAGS='-arch arm64' LDFLAGS='-arch arm64' lake exe verified-compiler-notes`
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
- Use `https://github.com/leanprover/verso-templates` as the primary reference for supported Verso authoring patterns and template examples before adding local extensions.
- Use `savedLean`/`savedImport` where example code extraction is intended.
- Prefer small, self-contained semantic chapters that remain compilation-checkable.
- For rendered mathematics in chapter text, use native Verso math syntax wrapped in backticks: `` `$...$` `` for inline math and `` `$$...$$` `` for display math.
- KaTeX syntax support reference:
  - Supported functions: `https://katex.org/docs/supported`
  - Support table: `https://katex.org/docs/support_table`
- For Lean snippets that must elaborate earlier but be displayed later, prefer the local `sharedLean (snippet := "...")` and `replayLean (snippet := "...")` blocks from `VerifiedCompilerNotes.Meta.Lean`.

## Operational Notes (from current session)
- Chapter source currently in `VerifiedCompilerNotes/Semantics.lean` uses only definitions and no theorem proofs.
- Build from the project root with `lake exe verified-compiler-notes`.
- `VerifiedCompilerNotes.Meta.Lean` now defines reusable local Verso extensions:
  - `sharedLean` / `replayLean` for “define once, display later” Lean snippets
- `VerifiedCompilerNotes/Semantics.lean` imports `VerifiedCompilerNotes.Meta.Lean` directly so these local blocks are available during chapter elaboration.
