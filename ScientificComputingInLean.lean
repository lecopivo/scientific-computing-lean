import ScientificComputingInLean.Intro
import ScientificComputingInLean.WorkingWithArrays
import ScientificComputingInLean.Differentiation
import ScientificComputingInLean.FunctionTransformation
import ScientificComputingInLean.Examples
import ScientificComputingInLean.Meta.Solution

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Scientific Computing in Lean" =>

%%%
authors := ["Tomáš Skřivan"]
%%%

The Plan 🙂

1. Arrays

2. Differentiations

3. Equations, optimization and their approximation
  - inverse function
  - general approximation
  - nonlinear equations - newton solver    
  - linear equations - todo: add eigen bindings
  - minimization - min function
  - differentiation equations and minimizations
    - differentiating inverse function
    - implicit differentiation
    - differentiating minimization problem
  
4. Differential equations
  - odesolve
  - numerical methods
  - differentiating ode solutions

5. Geometry
  - shapes
  - level sets and SDFs
  - bounding balls and squares

6. probabilistic programming
  - samplers
  - differentiating probabilistic programs
  - differentiating parametric discontinuities
  - random programs with traces

7. Tactic overview
  - fun\_trans
  - fun\_prop
  - infer\_var
  - data\_synth
  - lsimp
  - rsimp
  - optimize_index_access
  

8. Examples


{include ScientificComputingInLean.Intro}

{include ScientificComputingInLean.WorkingWithArrays}

{include ScientificComputingInLean.Differentiation}

{include ScientificComputingInLean.FunctionTransformation}

{include ScientificComputingInLean.Examples}
