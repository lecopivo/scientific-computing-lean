import Verso.Genre.Manual
import SciLean


import ScientificComputingInLean.Examples.HarmonicOscillator

open Verso.Genre Manual
open Lean.MessageSeverity

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open SciLean

variable (X : Type)

#doc (Manual) "Examples" =>

{include ScientificComputingInLean.Examples.HarmonicOscillator}
