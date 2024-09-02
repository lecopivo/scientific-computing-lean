import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Verso.Code

import SubVerso.Highlighting
import SubVerso.Examples

import Manual.Meta.Basic
import Manual.Meta.Lean.Scopes

import Manual.Meta.Lean


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

def Inline.var : Inline where
  name := `Manual.var

open Manual.Meta.Lean.Scopes (getScopes setScopes)

@[role_expander var]
def var : RoleExpander
  | args, inlines => do
    let config ← LeanBlockConfig.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $term:str }) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let altStr ← parserInputString term

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt term e
    | .ok stx =>
      let (newMsgs, tree) ← withInfoTreeContext (mkInfoTree := mkInfoTree `leanInline (← getRef)) do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          discard <| Manual.Meta.Lean.Scopes.runWithVariables  
                       (doSynthesize := false)
                       fun _ => Elab.Term.elabTerm stx none
          Core.getMessageLog
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then
        let msgs ← newMsgs.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

      match config.error with
      | none =>
        for msg in newMsgs.toArray do
          logMessage msg
      | some true =>
        if newMsgs.hasErrors then
          for msg in newMsgs.errorsToWarnings.toArray do
            logMessage msg
        else
          throwErrorAt term "Error expected in code, but none occurred"
      | some false =>
        for msg in newMsgs.toArray do
          logMessage msg
        if newMsgs.hasErrors then
          throwErrorAt term "No error expected in code, one occurred"

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))

      if config.show.getD true then
        pure #[← `(Inline.other {Inline.lean with data := ToJson.toJson $(quote hls)} #[Inline.code $(quote term.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str
  mkInfoTree (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree) : DocElabM InfoTree := do
    let tree := InfoTree.node (Info.ofCommandInfo { elaborator, stx }) trees
    let ctx := PartialContextInfo.commandCtx {
      env := ← getEnv, fileMap := ← getFileMap, mctx := {}, currNamespace := ← getCurrNamespace,
      openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
    }
    return InfoTree.context ctx tree

  modifyInfoTrees {m} [Monad m] [MonadInfoTree m] (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
    modifyInfoState fun s => { s with trees := f s.trees }

  -- TODO - consider how to upstream this
  withInfoTreeContext {m α} [Monad m] [MonadInfoTree m] [MonadFinally m] (x : m α) (mkInfoTree : PersistentArray InfoTree → m InfoTree) : m (α × InfoTree) := do
    let treesSaved ← getResetInfoTrees
    MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let tree  ← mkInfoTree st.trees
      modifyInfoTrees fun _ => treesSaved.push tree
      pure tree


