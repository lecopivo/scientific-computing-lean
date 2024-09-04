import ScientificComputingInLean.Meta
import SciLean
import SciLean.Data.Fintype.Quotient

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxRecDepth   100000000
set_option maxHeartbeats 100000000

open Lean.MessageSeverity
open SciLean

set_default_scalar ℝ

#doc (Manual) "Vectorization" =>



```lean

variable {X Y : Type} [PlainDataType X] [PlainDataType Y]

@[fun_trans]
def vectorize (I : Type) [IndexType I] (f : X → Y) : X^[I] → Y^[I] :=
  fun x => ⊞ i => f (x[i])
```

```lean
variable {R} [RCLike R]
  [NormedAddCommGroup X] [NormedSpace R X]
  [NormedAddCommGroup Y] [NormedSpace R Y]

variable (R)
@[fun_trans]
noncomputable
def fwdFDerivVec (I : Type) [IndexType I] (f : X → Y) (x : X) (dx : X^[I]) : Y × Y^[I] :=
  (f x, vectorize I (fderiv R f x) dx)
variable {R}
```  
