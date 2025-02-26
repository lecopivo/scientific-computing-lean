import Lake
open Lake DSL

def linkArgs :=
  if System.Platform.isWindows then
    #[]
  else if System.Platform.isOSX then
    #["-L/opt/homebrew/opt/openblas/lib",
      "-L/usr/local/opt/openblas/lib", "-lblas"]
  else -- assuming linux
    #["-L/usr/lib/x86_64-linux-gnu/", "-lblas", "-lm"]

package «ScientificComputingInLean» where
  moreLinkArgs := linkArgs
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


require scilean from git "https://github.com/lecopivo/scilean.git" @ "blas"
require «verso-manual» from git "https://github.com/leanprover/reference-manual.git" @ "release-2025-02-03"
