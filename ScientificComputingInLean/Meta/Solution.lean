import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Verso.Code

import SubVerso.Highlighting
import SubVerso.Examples

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual


def Block.Solution : Block where
  name := `Manual.Solution

def Inline.Solution : Inline where
  name := `Manual.Solution


@[directive_expander Solution]
def Solution : DirectiveExpander
  | args, blocks => do
    ArgParse.done.run args
    let content ← blocks.mapM elabBlock
    pure #[← `(Doc.Block.other Block.Solution #[$content,*])]

@[role_expander Solution]
def Solutioninline : RoleExpander
  | args, inlines => do
    ArgParse.done.run args
    let content ← inlines.mapM elabInline
    pure #[← `(Doc.Inline.other Inline.Solution #[$content,*])]


@[block_extension Solution]
def Solution.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  extraCss := [r#"
div.collapsible {
  margin: 5px 0;
}

div.collapsible-header {
  padding: 2px;
  font-size: medium;
  cursor: pointer;
  position: relative;
}

div.collapsible-header::after {
  content: "⊢";
  position: absolute;
  left: 60px;
  transition: transform 0.3s ease;
}

div.collapsible-content {
  border: 1px solid white;
  max-height: 0;
  overflow: hidden;
  transition: max-height 0.3s ease;
}

div.collapsible.expanded .collapsible-content {
  max-height: 500px; /* Adjust this value depending on the content's height */
  border: 1px solid lightgrey;
}

div.collapsible.expanded .collapsible-header::after {
  transform: rotate(90deg); /* Rotate to show ">" when expanded */
}
"#]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="collapsible" onclick="this.classList.toggle('expanded');">
               <div class="collapsible-header">"Solution"</div>
               <div class="collapsible-content">{{← content.mapM goB}}</div>
             </div>}}



def Block.Hint : Block where
  name := `Manual.Hint

def Inline.Hint : Inline where
  name := `Manual.Hint


@[directive_expander Hint]
def Hint : DirectiveExpander
  | args, blocks => do
    ArgParse.done.run args
    let content ← blocks.mapM elabBlock
    pure #[← `(Doc.Block.other Block.Hint #[$content,*])]

@[role_expander Hint]
def Hintinline : RoleExpander
  | args, inlines => do
    ArgParse.done.run args
    let content ← inlines.mapM elabInline
    pure #[← `(Doc.Inline.other Inline.Hint #[$content,*])]


@[block_extension Hint]
def Hint.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  extraCss := [r#"
div.collapsible-hint {
  margin: 5px 0;
}

div.collapsible-hint-header {
  padding: 2px;
  font-size: medium;
  cursor: pointer;
  position: relative;
}

div.collapsible-hint-header::after {
  content: "⊢";
  position: absolute;
  left: 50px;
  transition: transform 0.3s ease;
}

div.collapsible-hint-content {
  border: 1px solid white;
  max-height: 0;
  overflow: hidden;
  transition: max-height 0.3s ease;
}

div.collapsible-hint.expanded .collapsible-hint-content {
  max-height: 500px; /* Adjust this value depending on the content's height */
  border: 1px solid lightgrey;
}

div.collapsible-hint.expanded .collapsible-hint-header::after {
  transform: rotate(90deg); /* Rotate to show ">" when expanded */
}
"#]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="collapsible-hint" onclick="this.classList.toggle('expanded');">
               <div class="collapsible-hint-header">"Hint"</div>
               <div class="collapsible-hint-content">{{← content.mapM goB}}</div>
             </div>}}
