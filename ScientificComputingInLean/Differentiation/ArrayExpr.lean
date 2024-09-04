import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxHeartbeats 1000000000

open Lean.MessageSeverity
open SciLean

#doc (Manual) "Differentiating Array Expressions" =>

Talk about the problem of differentiating w.r.t. an array. Mention sparse update problem and structure sharing.

Talk about {name}`SciLean.revFDerivProj` and {name}`SciLean.revFDerivProjUpdate`.
