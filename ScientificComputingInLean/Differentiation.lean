import ScientificComputingInLean.Meta
import ScientificComputingInLean.Differentiation.Basic
import ScientificComputingInLean.Differentiation.AutomaticDifferentiation
import ScientificComputingInLean.Differentiation.FunctionTransformation
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open Lean.MessageSeverity

open SciLean

#doc (Manual) "Differentiation" =>


We will cover these topics
1. symbolic differentiations
2. automatic differentiations, forward and reverse mode AD
3. function transformations and how AD works in SciLean
  - exersices: define new function transformations:
    - vectorize `(X → Y) → (X^[n] → Y^[n])`
    - vectorized version of fwdFDeriv
      fwdFDerivVec `(X → Y) → (X×X^[n] → Y×Y^[n])`
4. working with user defined functions and structurs
  - polymorphics functions
  - higher order functions
  - recursive functions
5. differentiating tensor expressions
  - explain the problem
  - current solution
  - sparse update and structure sharing problem
6. differentiating imperative and monadic code
7. variational calclus


{include ScientificComputingInLean.Differentiation.Basic}

{include ScientificComputingInLean.Differentiation.AutomaticDifferentiation}

{include ScientificComputingInLean.Differentiation.FunctionTransformation}
