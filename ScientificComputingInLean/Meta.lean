import Manual.Meta
import ScientificComputingInLean.Meta.Solution


open Verso Doc Elab in
@[code_block_expander latex]
def latex : CodeBlockExpander
  | _args, str => do
    return #[(← `(Doc.Block.para #[Doc.Inline.text s!"$${$str}$$"]))]
