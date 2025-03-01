import ScientificComputingInLean.Examples.HarmonicOscillator
import ScientificComputingInLean.Examples.HarmonicOscillatorOptimization

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open SciLean

variable (X : Type)

#doc (Manual) "Examples" =>

{include ScientificComputingInLean.Examples.HarmonicOscillator}

{include ScientificComputingInLean.Examples.HarmonicOscillatorOptimization}
