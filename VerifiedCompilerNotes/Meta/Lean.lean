/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Lean

namespace VerifiedCompilerNotes

private partial def inlineSortingKey : Verso.Doc.Inline g → String
  | .text str | .code str | .math _ str => str
  | .linebreak _ => " "
  | .emph i | .bold i | .concat i | .link i _ | .other _ i =>
      String.join (i.toList.map inlineSortingKey)
  | .image .. | .footnote .. => ""

private def texIndexEscape (s : String) : String :=
  let s := s.replace "\\" "\\\\"
  let s := s.replace "!" "\\!"
  let s := s.replace "@" "\\@"
  let s := s.replace "|" "\\|"
  s.replace "\"" "\\\""

private def texIndexEntry
    (entry : _root_.Verso.Genre.Manual.Index.Entry) : String :=
  let ⟨termIn, subtermIn, _⟩ := entry
  let term :=
    texIndexEscape <| inlineSortingKey termIn
  match subtermIn with
  | none => term
  | some sub => term ++ "!" ++ texIndexEscape (inlineSortingKey sub)

private def reusableLeanBlocksKey : Name :=
  `VerifiedCompilerNotes.reusableLeanBlocks

private def getReusableLeanTable (state : TraverseState) : Json :=
  ((state.get? reusableLeanBlocksKey : Option (Except String Json))
    >>= Except.toOption) |>.getD (Json.mkObj [])

private def saveReusableLeanBlocks
    (name : String)
    (contents : Array (Verso.Doc.Block Verso.Genre.Manual)) :
    StateT TraverseState IO Unit := do
  modify fun st =>
    st.set reusableLeanBlocksKey <|
      (getReusableLeanTable st).setObjVal! name (toJson contents)

private def loadReusableLeanBlocks?
    (name : String) (state : TraverseState) :
    Option (Except String
      (Array (Verso.Doc.Block Verso.Genre.Manual))) := do
  let table := getReusableLeanTable state
  let json ← table.getObjVal? name |>.toOption
  pure (fromJson? json)

block_extension Block.savedLean (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents =>
    contents.mapM goB
  toHtml := some fun _ goB _ _ contents =>
    contents.mapM goB

block_extension Block.savedImport (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ _ _ _ _ =>
    pure .empty

/--
Lean code that is saved to the examples file.
-/
@[code_block savedLean]
def savedLean : CodeBlockExpanderOf InlineLean.LeanBlockConfig
  | args, code => do
    let underlying ← InlineLean.lean args code
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote (code.getString))) #[$underlying])

/--
An import of some other module, to be located in the saved code. Not rendered.
-/
@[code_block]
def savedImport : CodeBlockExpanderOf Unit
  | (), code => do
    ``(Block.other (Block.savedImport $(quote (← getFileName)) $(quote (code.getString))) #[])

/--
Comments to be added as module docstrings to the examples file.
-/
@[code_block]
def savedComment : CodeBlockExpanderOf Unit
  | (), code => do
    let str := code.getString.trimAsciiEnd.copy
    let comment := s!"/-!\n{str}\n-/"
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote comment)) #[])

@[inline_extension Verso.Genre.Manual.index]
private def texIndexDescr : InlineDescr :=
  { Verso.Genre.Manual.index.descr with
    toTeX := some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        Verso.Doc.TeX.logError err
        pure .empty
      | .ok (entry : _root_.Verso.Genre.Manual.Index.Entry) =>
        pure <| .raw ("\\index{" ++ texIndexEntry entry ++ "}")
  }

@[block_extension Verso.Genre.Manual.theIndex]
private def texTheIndexDescr : BlockDescr :=
  { Verso.Genre.Manual.theIndex.descr with
    toTeX := some <| fun _ _ _ _ _ => do
      pure <| .raw "\\printindex\n"
    usePackages := (["\\usepackage{makeidx}"] : List String)
    preamble := (["\\makeindex"] : List String)
  }

block_extension Block.texSetup where
  traverse _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ _ _ => pure .empty
  usePackages := [
    "\\usepackage{stmaryrd}",
    "\\usepackage{amssymb}"
  ]
  preamble := []

/--
Inject PDF-specific TeX setup such as extra packages and font overrides.
-/
@[code_block]
def texSetup : CodeBlockExpanderOf Unit
  | (), _ => do
    ``(Block.other Block.texSetup #[])

private def sharedLeanStringDesc [Monad m] [MonadError m] :
    ValDesc m String := {
  description := "snippet name"
  signature := .String
  get := fun
    | .str s => pure s.getString
    | other => throwError "Expected string, got {repr other}"
}

structure SharedLeanConfig extends InlineLean.LeanBlockConfig where
  snippet : String

def SharedLeanConfig.parse :
    Verso.ArgParse DocElabM SharedLeanConfig :=
  SharedLeanConfig.mk <$> InlineLean.LeanBlockConfig.parse <*>
    Verso.ArgParse.named `snippet sharedLeanStringDesc false

instance : Verso.ArgParse.FromArgs SharedLeanConfig DocElabM :=
  ⟨SharedLeanConfig.parse⟩

block_extension Block.sharedLean (snippet : String) where
  data := .str snippet

  traverse _ data contents := do
    let .str snippet := data
      | logError s!"Expected snippet name, got {data.compress}" *> pure none
    saveReusableLeanBlocks snippet contents
    pure none

  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ _ _ => pure .empty

/--
Lean code that is elaborated once, hidden at its definition site, and replayable later.
-/
@[code_block sharedLean]
def sharedLean : CodeBlockExpanderOf SharedLeanConfig
  | args, code => do
    let inner : InlineLean.LeanBlockConfig :=
      { args.toLeanBlockConfig with «show» := true }
    let underlying ← InlineLean.lean inner code
    ``(Block.other (Block.sharedLean $(quote args.snippet)) #[$underlying])

structure ReplayLeanConfig where
  snippet : String

def ReplayLeanConfig.parse :
    Verso.ArgParse DocElabM ReplayLeanConfig :=
  ReplayLeanConfig.mk <$>
    Verso.ArgParse.named `snippet sharedLeanStringDesc false

instance : Verso.ArgParse.FromArgs ReplayLeanConfig DocElabM :=
  ⟨ReplayLeanConfig.parse⟩

block_extension Block.replayLean (snippet : String) where
  data := .str snippet

  traverse _ data _ := do
    let .str snippet := data
      | logError s!"Expected snippet name, got {data.compress}" *>
        pure (some (.concat #[]))
    match loadReusableLeanBlocks? snippet (← get) with
    | some (.ok contents) =>
      pure (some (.concat contents))
    | some (.error err) =>
      logError s!"Couldn't decode shared Lean snippet '{snippet}': {err}"
      pure (some (.concat #[]))
    | none =>
      logError s!"Unknown shared Lean snippet '{snippet}'"
      pure (some (.concat #[]))

  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ _ _ => pure .empty

/--
Render a previously shared Lean snippet without repeating its source text.
-/
@[code_block replayLean]
def replayLean : CodeBlockExpanderOf ReplayLeanConfig
  | args, _ => do
    ``(Block.other (Block.replayLean $(quote args.snippet)) #[])
