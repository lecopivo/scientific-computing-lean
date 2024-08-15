import Lake
open Lake DSL

package «ScientificComputingInLean» where
  -- add package configuration options here

lean_lib «ScientificComputingInLean» where
  -- add library configuration options here

lean_lib SCLean where
  roots := #[`Main]

@[default_target]
lean_exe sclean where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true



require verso from git "https://github.com/leanprover/verso.git" @ "main"

require scilean from git "https://github.com/lecopivo/scilean.git" @ "reorganize"
