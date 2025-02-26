import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Manual.Meta.Figure
import Manual.Meta.Example
import Manual.Meta.Figure
import Manual.Meta.Lean
import Verso.Code

import SubVerso.Highlighting
import SubVerso.Examples

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual


def Block.foldable (name : Option String) : Block where
  name := `Manual.foldable
  data := ToJson.toJson (name, (none : Option Tag))

structure FoldableConfig where
  description : FileMap × Array Syntax
  /-- Name for refs -/
  name : Option String := none


def FoldableConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m FoldableConfig :=
  FoldableConfig.mk <$> .positional `description .inlinesString <*> .named `name .string true


@[directive_expander «foldable»]
def «foldable» : DirectiveExpander
  | args, contents => do
    let cfg ← FoldableConfig.parse.run args
    let description ← cfg.description.2.mapM elabInline
    -- Elaborate Lean blocks first, so inlines in prior blocks can refer to them
    let blocks ← prioritizedElab (isLeanBlock ·) elabBlock contents
    -- Foldables are represented using the first block to hold the description. Storing it in the JSON
    -- entails repeated (de)serialization.
    pure #[← ``(Block.other (Block.foldable $(quote cfg.name)) #[Block.para #[$description,*], $blocks,*])]

@[block_extension «foldable»]
def foldable.descr : BlockDescr where
  traverse id data contents := do
    match FromJson.fromJson? data (α := Option String × Option Tag) with
    | .error e => logError s!"Error deserializing foldable tag: {e}"; pure none
    | .ok (none, _) => pure none
    | .ok (some x, none) =>
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.foldable none with id := some id, data := toJson (some x, some tag)} contents
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
        HtmlT.logError "Malformed foldable"
        pure .empty
      else
        let .para description := blocks[0]
          | HtmlT.logError "Malformed foldable - description not paragraph"; pure .empty
        let xref ← HtmlT.state
        let attrs := xref.htmlId id
        pure {{
          <details class="foldable" {{attrs}}>
            <summary class="description">{{← description.mapM goI}}</summary>
            {{← blocks.extract 1 blocks.size |>.mapM goB}}
          </details>
        }}
  extraCss := [
r#".foldable {
  padding: 1.5em;
  border: 1px solid #98B2C0;
  border-radius: 0.5em;
  margin-bottom: 0.75em;
  margin-top: 0.75em;
  clear: both; /* Don't overlap margin notes with foldables */
}
.foldable p:last-child {margin-bottom:0;}
.foldable .description::before {
  content: "";
}
.foldable[open] .description {
  margin-bottom: 1em;
}
.foldable .description {
  font-style: italic;
  font-family: var(--verso-structure-font-family);
}
.foldable .hl.lean.block {
  overflow-x: auto;
}
"#
  ]
