import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Manual.Meta.Figure
import Manual.Meta.Example
import Manual.Meta.Lean
import Verso.Code

import SubVerso.Highlighting
import SubVerso.Examples

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

def Block.solution (name : Option String) : Block where
  name := `Manual.solution
  data := ToJson.toJson (name, (none : Option Tag))

structure SolutionConfig where
  description : FileMap × Array Syntax
  name : Option String := none

def SolutionConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m SolutionConfig :=
  SolutionConfig.mk <$> .positional `description .inlinesString <*> .named `name .string true

@[directive_expander «solution»]
def «solution» : DirectiveExpander
  | args, contents => do
    let cfg ← SolutionConfig.parse.run args
    let description ← cfg.description.2.mapM elabInline
    -- Elaborate Lean blocks first, so inlines in prior blocks can refer to them
    let blocks ← prioritizedElab (isLeanBlock ·) elabBlock contents
    -- Solutions are represented using the first block to hold the description. Storing it in the JSON
    -- entails repeated (de)serialization.
    pure #[← ``(Block.other (Block.solution $(quote cfg.name)) #[Block.para #[$description,*], $blocks,*])]

@[block_extension «solution»]
def solution.descr : BlockDescr where
  traverse id data contents := do
    match FromJson.fromJson? data (α := Option String × Option Tag) with
    | .error e => logError s!"Error deserializing solution tag: {e}"; pure none
    | .ok (none, _) => pure none
    | .ok (some x, none) =>
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.solution none with id := some id, data := toJson (some x, some tag)} contents
    | .ok (some _, some _) => pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun goI goB id _data blocks => do
      if h : blocks.size < 1 then
        HtmlT.logError "Malformed solution"
        pure .empty
      else
        let .para description := blocks[0]
          | HtmlT.logError "Malformed solution - description not paragraph"; pure .empty
        let xref ← HtmlT.state
        let attrs := xref.htmlId id
        pure {{
          <details class="solution" {{attrs}}>
            <summary class="description">{{← description.mapM goI}}</summary>
            {{← blocks.extract 1 blocks.size |>.mapM goB}}
          </details>
        }}
  extraCss := [
r#".solution {
  padding: 1.5em;
  border: 1px solid #98B2C0;
  border-radius: 0.5em;
  margin-bottom: 0.75em;
  margin-top: 0.75em;
  clear: both; /* Don't overlap margin notes with solutions */
}
.solution p:last-child {margin-bottom:0;}
.solution .description::before {
  content: "";
}
.solution[open] .description {
  margin-bottom: 1em;
}
.solution .description {
  font-style: italic;
  font-family: var(--verso-structure-font-family);
}
.solution .hl.lean.block {
  overflow-x: auto;
}
"#
  ]
