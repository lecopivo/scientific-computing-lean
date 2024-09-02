import Verso

namespace Manual

open Verso Doc Elab in
@[code_block_expander latex]
def latex : CodeBlockExpander
  | _args, str => do
    return #[(← `(Doc.Block.para #[Doc.Inline.text s!"$${$str}$$"]))]
