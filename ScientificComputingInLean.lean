-- import ScientificComputingInLean.Intro
-- import ScientificComputingInLean.WorkingWithArrays
-- import ScientificComputingInLean.Differentiation
-- import ScientificComputingInLean.FunctionTransformation
-- import ScientificComputingInLean.Miscellaneous
-- import ScientificComputingInLean.Examples
-- import ScientificComputingInLean.Meta.Solution
import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Scientific Computing in Lean" =>

%%%
authors := ["Tomáš Skřivan"]
%%%

Work in progress book on using Lean 4 as a programming language for scientific computing. Also serves as reference for [SciLean](https://www.github.com/lecopivo/SciLean) library.

This book in its current form is a draft and is subject to change. Code might not work, explanations might be incomplete or incorrect. Procced with caution.


```lean
#check Nat

example (n m : Nat) : n + m = m + n := by
  simp[Nat.add_comm]

```
