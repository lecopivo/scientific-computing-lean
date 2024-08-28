import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxRecDepth 1000000

open Lean.MessageSeverity
open SciLean

set_default_scalar ℝ

#doc (Manual) "Function Transformation" =>


In this chapter we will look under the lid of the tactic `fun_trans`, a tactic for general function transformation. Explain the main idea behind it, how to define your own function transformations and how does it work internally.

Note: One of the main inspiration is Google JAX which is descibed as: "Google JAX is a machine learning framework for transforming numerical functions." 

So far we have encoutered couple of function transfomations {lean}`fderiv`, {lean}`fwdFDeriv`, {lean}`revFDeriv`, {lean}`adjoint`. In general, function transformation should be a higher order function `F` taking a function and producing a function that should satisfy
```latex
F(f \circ g) = F(f) \circ F(g)
```
where the composition \\( \\circ \\) should be some kind of generalized composition.


```lean
open SciLean 
variable 
  (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : ℝ)
  (A B : ℝ → ℝ) (hf : IsContinuousLinearMap ℝ A) (hg : IsContinuousLinearMap ℝ B) (x : ℝ)

example : (∂ (f ∘ g) x) = (∂ f (g x)) * (∂ g x) := by 
  unfold Function.comp deriv; fun_trans[mul_comm]

example : (↿(∂> (f ∘ g))) = (↿(∂> f)) ∘ (↿(∂> g)) := by 
  fun_trans [Function.HasUncurry.uncurry, Function.comp]

example : (<∂ (f ∘ g) x) 
          = 
          let (y,dg) := <∂ g x; 
          let (z,df) := <∂ f y; 
          (z, dg ∘ df) := by 
 fun_trans [Function.comp]

example : adjoint ℝ (A ∘ B) = adjoint ℝ B ∘ adjoint ℝ A := by 
  fun_trans[Function.comp]
```

Also `F` should preserve identity
```latex
F(\text{id}) = \text{id}
```
where \\( \\text\{id\} \\) is some generalized notion of identity function

```lean
example : (fderiv ℝ (fun x : ℝ => x)) = (fun _ => fun dx =>L[ℝ] dx) := by fun_trans
example : (∂> (fun x : ℝ => x)) = fun x dx => (x,dx) := by fun_trans
example : (<∂ (fun x : ℝ => x)) = fun x => (x, fun dx => dx) := by fun_trans
example : (adjoint ℝ (fun x : ℝ => x)) = fun x => x := by fun_trans
```


(Note: If you are familiar with category theorey then `F` is often a functor. For example {lean}`fderiv` is not really a functor yet it still fits into SciLean's function transformation framework.)


# User Defined Function Transformation

Let's demonstrate `fun_trans` capability by defining a slight variant of forward mode derivative
```lean
open SciLean
variable 
  (R) [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]

@[fun_trans]
noncomputable
def fwdFDeriv' (f : X → Y) : X×X → Y×Y := 
  fun xdx => (f xdx.1, fderiv R f xdx.1 xdx.2)
```
The only difference is that {lean}`fwdFDeriv'` is uncurried version of {lean}`fwdFDeriv`.

My marking the definition with `@[fun_trans]` attribute we let Lean know that it is a function transformation. For `fun_trans` to work properly with this newly defined function transformation we have to state its transformation rules/theorems. There are couple types
1. Lambda theorems.
  Theorems about basic lambda terms like indentity `fun x => x`, constant `fun x => y`, composition `fun x => f (g x)` and few more.
2. Function theorems.
  Theorems about functions like addition, multiplication etc.
3. Free variable theorems.
  These theorems usually state a transformation rule under some special condition. Like derivative of linear function is the function itself.
4. Morphism theorems.
  Theorems about bundled morphisms. These are very special theorems that 
  
# Lambda Theorems

The tactic `fun_trans` transforms a complicated functions by first decomposing them into a sequence of function compositions and then transforms each of those function separetely. For example when we want to transform function {lean}`(fun (x : ℝ) => ((2*x) + x)^2)` then `fun_trans` effectivelly rewrites it as
```lean
example :
  (fun (x : ℝ) => ((2*x) + x)^2)
  =
  (fun x => x^2) ∘ (fun (x,y) => x + y) ∘ (fun x => (2*x,x)) := by rfl
```
Therefore `fun_trans` needs to know how to handle transfoming composition but also to transform `(fun x => (2*x,x))` it ineeds to know how to transform pairing of two functions `fun x => 2*x` and `fun x => x`. 

Lambda theorems are responsible for reducing the problem of transforming function like {lean}`(fun (x : ℝ) => ((2*x) + x)^2)` into transformation of all the elementary functions `(fun x => x^2)`, `(fun (x,y) => x+y)` and `(fun x => 2*x)`. Those are handled by function theorems and we will talk about those a bit later.

There are six basic lambda theorems saying how lambda terms are transformed

1. Identity rule for transforming `fun (x : X) => x`
2. Constant rule for transforming `fun (x : X) => y`
3. Composition rule for transforming `fun (x : X) => f (g x)`
4. Let rule for transforming `fun (x : X) => let y := g x; f x y`
5. Apply rule for transforming `fun (f : X → Y) => f x`
6. Pi rule for transforming `fun (x : X) (y : Y) => f x y`

There are also three theorems about product type which technically speaking fall under the category of "function theorems" but they are so fundamental that we list them here

7. Product rule for transforming `fun (x : X) => (f x, g x)`
8. First projection rule for transforming `fun (xy : X×Y) => xy.1`
9. Second projection rule for transforming `fun (xy : X×Y) => xy.2`

The collection of these theorems allows `fun_trans` to transform any complicated lambda expression if it can transform all the atomic functions in the lambda expression.

Let us give an example of few lambda theorems for {lean}`fwdFDeriv'`
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z]

theorem fwdFDeriv'.id_rule : 
    fwdFDeriv' R (fun x : X => x) = fun xdx => xdx := by
  unfold fwdFDeriv'; fun_trans

theorem fwdFDeriv'.comp_rule 
    (f : Y → Z) (g : X → Y) 
    (hf : Differentiable R f) (hg : Differentiable R g) : 
    fwdFDeriv' R (fun x : X => f (g x)) 
    = 
    fun xdx => 
      let ydy := fwdFDeriv' R g xdx
      fwdFDeriv' R f ydy := by
  unfold fwdFDeriv'; fun_trans

theorem fwdFDeriv'.pi_rule {I} [IndexType I]
    (f : X → I → Y) (hf : ∀ i, Differentiable R (f · i)) : 
    fwdFDeriv' R (fun (x : X) (i : I) => f x i) 
    = 
    fun xdx => 
      let ydy := fun i => fwdFDeriv' R (f · i) xdx
      (fun i => (ydy i).1, fun i => (ydy i).2) := by
  unfold fwdFDeriv'; simp [fderiv.pi_rule f hf]
```

## Exercises

1. Write down the constant lambda theorems of {lean}`fwdFDeriv'`
2. Write down the produce and projection lambda theorems of {lean}`fwdFDeriv'`
3. Write down the apply lambda theorems of {lean}`fwdFDeriv'`. 
  Hint: You want to write it for a function `fun (f : I → X) => f i` where `I` has instance of `[IndexType I]` (probably only `[Fintype I]` is enough)
4. Write down the let lambda theorems of {lean}`fwdFDeriv'`. 
  Pay attention the the use of let bindings on the right hand side. Careful use of let bindings is important for the efficiency of the resulting code. Also you do not want to differentiate `f` w.r.t. to `x` and `y` separetely but rather differentiate it w.r.t. `x` and `y` simultatinously.


# Function Theorems



## Simple vs Compositional Form


## User Defined Functions

# Free Variable Theorems


# Morphism Theorems



# Advanced Function Theorems


## Polymorphic Functions

## High Order Functions

## Recursive Functions
