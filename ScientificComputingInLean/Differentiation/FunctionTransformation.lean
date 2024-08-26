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

Let's demonstrate `fun_trans` capability by defining a new function transformation `vectorize`

```lean

open SciLean
variable 
  {X Y : Type} [PlainDataType X] [PlainDataType Y]

@[fun_trans]
def vectorize (I : Type) [IndexType I] (f : X → Y) : X^[I] → Y^[I] := fun x => ⊞ i => f (x[i])
```
This function takes a function `(f : X → Y)` and creates a function mapping arrays of `X` to arrays of `Y` by calling `f` on every element. To indicete that such high order function should be treated as function transformation we have to add the attribute `@[fun_trans]`

Note: This function is similar to JAX's vmap 

Unlike previous function transformations, {lean}`vectorize` is computable function. Thus we can actually evaluate `vectorize f` for any computable `f`. However, the default implementation might not be ideal as `⊞ i => ...` always allocates new memory but for example `vectorize exp x` should modify the array `x` inplace.


## Lambda Theorems



```lean
open SciLean
variable 
  {X Y Z : Type} [PlainDataType X] [PlainDataType Y] [PlainDataType Z]
  {I : Type} [IndexType I] 

theorem vectorize.id_rule : 
    vectorize I (fun x : X => x) = fun x => x := by
  unfold vectorize; ext i; simp

theorem vectorize.const_rule (y : Y) : 
    vectorize I (fun x : X => y) = fun _ => ⊞ _ => y := by
  unfold vectorize; ext i; simp

theorem vectorize.comp_rule (f : Y → Z) (g : X → Y): 
    vectorize I (fun x : X => f (g x)) = fun x => vectorize I f (vectorize I g x) := by
  unfold vectorize; ext i; simp

theorem vectorize.let_rule (f : X → Y → Z) (g : X → Y): 
    vectorize I (fun x : X => let y := g x; f x y)
    = 
    fun x =>
      let y := vectorize I g x
      let z := vectorize I (fun xy : X×Y => f xy.1 xy.2) (⊞ i => (x[i],y[i]))
      z := by
  unfold vectorize; ext i; simp
```


## Function Theorems


```lean
open SciLean
set_option deprecated.oldSectionVars true
variable 
  {X Y Z : Type} [PlainDataType X] [PlainDataType Y] [PlainDataType Z]
  {I : Type} [IndexType I] 

theorem vectorize.prod_mk_rule (f : X → Y) (g : X → Z) :
  vectorize I (fun x => (f x, g x))
  =
  fun (x : X^[I]) =>
    ⊞ i => (f (x[i]), g (x[i])) := by unfold vectorize; ext x i <;> simp

theorem vectorize.fst_rule (f : X → Y×Z) :
  vectorize I (fun x => (f x).1)
  =
  fun (x : X^[I]) => 
    ⊞ i => (f (x[i])).1 := by unfold vectorize; ext x i <;> simp

theorem vectorize.snd_rule (f : X → Y×Z) :
  vectorize I (fun x => (f x).2)
  =
  fun (x : X^[I]) => 
    ⊞ i => (f x[i]).2 := by unfold vectorize; ext x i <;> simp

theorem vectorize.add_rule [Add Y] (f g : X → Y) :
  vectorize I (fun x => f x + g x)
  =
  fun x =>
    let y := vectorize I f x
    let z := vectorize I g x
    y + z := by unfold vectorize; ext i; simp

theorem vectorize.sub_rule [Sub Y] (f g : X → Y) :
  vectorize I (fun x => f x - g x)
  =
  fun x =>
    let y := vectorize I f x
    let z := vectorize I g x
    y - z := by unfold vectorize; ext i; simp
```




```lean (keep := false)
set_default_scalar Float
variable (y : Float^[5])
def matMul (A : Float^[10,5]) (y : Float^[5]) := 
  vectorize (Fin 10) (⟪·,y⟫) A.curry
```
