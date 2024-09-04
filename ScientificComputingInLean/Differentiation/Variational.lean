import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxHeartbeats 1000000000

open Lean.MessageSeverity
open SciLean


#doc (Manual) "Variational Calculus" =>


Talk about how to compute expressions like these
```latex
\delta_u \integral \| \nabla u(x) \| \, dx
```
or
```latex
\delta_x \integral L(t,x(t),\dot x(t)) \, dt
```


