import ScientificComputingInLean.Meta
import ScientificComputingInLean.FunctionTransformation.Basic
import ScientificComputingInLean.FunctionTransformation.ExprCompiler

import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open Lean.MessageSeverity

open SciLean

#doc (Manual) "🚧 Function Transformation" =>


In this chapter we will look under the lid of the tactic `fun_trans`, a tactic for general function transformation. Explain the main idea behind it, how to define your own function transformations and how does it work internally.

Note: One of the main inspiration is Google JAX which is descibed as: "Google JAX is a machine learning framework for transforming numerical functions." 

So far we have encoutered couple of function transfomations {lean}`fderiv`, {lean}`fwdFDeriv`, {lean}`revFDeriv`, {lean}`adjoint`. In general, function transformation should be a higher order function `F` taking a function and producing a function that should satisfy
```latex
F(f \circ g) = F(f) \circ F(g)
```
where the composition \\( \\circ \\) should be some kind of generalized composition.


Examples of composition rules for function transformations we have see so far
```
      (∂ (f ∘ g) x dx) = (∂ f (g x) (∂ g x dx))

     (∂> (f ∘ g) x dx) = let (y,dy) := ∂> g x dx
                         (∂> f y dy)

        (<∂ (f ∘ g) x) = let (y,dg) := <∂ g x; 
                         let (z,df) := <∂ f y; 
                         (z, dg ∘ df)

     adjoint ℝ (A ∘ B) = adjoint ℝ B ∘ adjoint ℝ A
```

Also `F` should preserve identity
```latex
F(\text{id}) = \text{id}
```
where \\( \\text\{id\} \\) is some generalized notion of identity function

Examples of identity rules for function transformations we have see so far
```
  (fderiv ℝ (fun x : ℝ => x)) = (fun _ => fun dx =>L[ℝ] dx)

        (∂> (fun x : ℝ => x)) = fun x dx => (x,dx)

        (<∂ (fun x : ℝ => x)) = fun x => (x, fun dx => dx)

 (adjoint ℝ (fun x : ℝ => x)) = fun x => x
```


(Note: If you are familiar with category theorey then `F` is often a functor. For example {lean}`fderiv` is not really a functor yet it still fits into SciLean's function transformation framework. 
This categorical viewpoint on automatic differentiation is inspired by the paper [The simple essence of automatic differentiation](https://arxiv.org/abs/1804.00746))



{include ScientificComputingInLean.FunctionTransformation.Basic}

{include ScientificComputingInLean.FunctionTransformation.ExprCompiler}


