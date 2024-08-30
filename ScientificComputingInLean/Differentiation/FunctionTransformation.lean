import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxRecDepth   100000000
set_option maxHeartbeats 100000000

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


1. Write down the constant lambda theorems of {lean}`fwdFDeriv'`
::: Solution
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]

@[fun_trans]
theorem fwdFDeriv'.const_rule (y : Y) :
  fwdFDeriv' R (fun x : X => y) 
  =
  fun _ => (y, 0) := by unfold fwdFDeriv'; fun_trans
```
:::
2. Write down the product and projection lambda theorems of {lean}`fwdFDeriv'`. Hint: The product rule should be formulated for `(fun x : X => (g x, f x))` where `g` and `f` are differentiable functions. The projection rule can be formulated for `(fun (xy : X×Y) => xy.1)`
::: Solution
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z]

@[fun_trans]
theorem Prod.mk.arg_fstsnd.fwdFDeriv'_rule 
   (g : X → Y) (f : X → Z) 
   (hg : Differentiable R g) (hf : Differentiable R f) :
   fwdFDeriv' R (fun x : X => (g x, f x)) 
   =
   fun xdx => 
     let ydy := fwdFDeriv' R g xdx
     let zdz := fwdFDeriv' R f xdx
     ((ydy.1,zdz.1),(ydy.2,zdz.2)) := by unfold fwdFDeriv'; fun_trans

@[fun_trans]
theorem Prod.fst.arg_self.fwdFDeriv'_rule 
    :
  fwdFDeriv' R (fun (xy : X×Y) => xy.1) 
  =
  fun xydxy => (xydxy.1.1,xydxy.2.1) := by unfold fwdFDeriv'; fun_trans

@[fun_trans]
theorem Prod.snd.arg_self.fwdFDeriv'_rule 
    :
  fwdFDeriv' R (fun (xy : X×Y) => xy.2) 
  =
  fun xydxy => (xydxy.1.2,xydxy.2.2) := by unfold fwdFDeriv'; fun_trans
```
:::

3. Write down the apply lambda theorems of {lean}`fwdFDeriv'`. 
  Hint: Writhe the rule for the function `fun (f : I → X) => f i` where `I` has instance of `[IndexType I]`.
::: Solution
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {I} [IndexType I]

@[fun_trans]
theorem fwdFDeriv'.apply_rule (i : I) :
    fwdFDeriv' R (fun (f : I → X) => f i) 
    =
    fun fdf => (fdf.1 i, fdf.2 i) := by 
  unfold fwdFDeriv'; fun_trans
```
:::

4. Write down the let lambda theorems of {lean}`fwdFDeriv'`. 
  Pay attention the the use of let bindings on the right hand side. Careful use of let bindings is important for the efficiency of the resulting code. Also you do not want to differentiate `f` w.r.t. to `x` and `y` separetely but rather differentiate it w.r.t. `x` and `y` simultatinously.
::: Solution
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z]

@[fun_trans]
theorem fwdFDeriv'.let_rule
    (f : X → Y → Z) (hf : Differentiable R (fun (x,y) => f x y))
    (g : X → Y)  (hg : Differentiable R g) : 
    fwdFDeriv' R (fun x => let y := g x; f x y) 
    =
    fun xdx => 
      let ydy := fwdFDeriv' R g xdx
      let xydxy := ((xdx.1,ydy.1),(xdx.2,ydy.2))
      fwdFDeriv' R (fun (x,y) => f x y) xydxy := by 
  unfold fwdFDeriv'; fun_trans
```
:::


# Function Theorems

Once we postulate all the lambda theorems for a new function transformation we have to also postulate theorems for functions like addition, multiplication etc. 

Let's start with a function theorem for negation is it is a function of a single argument
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]

@[fun_trans]
theorem Neg.neg.arg_a0.fwdFDeriv'_rule :
    fwdFDeriv' R (fun x : X => - x)
    =
    fun (x,dx) => 
      (-x, -dx) := by unfold fwdFDeriv'; fun_trans
```

For a function of two or more arguments we just uncurry the function sufficiently and furmulate the theorem as for a function of single argument. For example the transformation rule for addition is
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.fwdFDeriv'_rule :
    (fwdFDeriv' R fun xy : X×X => xy.1 + xy.2)
    =
    fun ((x,y),(dx,dy)) => 
      (x + y, dx + dy) := by unfold fwdFDeriv'; fun_trans
```


Let's define function in three arguments
```lean
open SciLean Scalar
variable {R} [RealScalar R]

def fun1 (x y z : R) := exp x * sin (z + y) + z
```
We do not have to state the transformation rule in all of its arguments at the same time. 
```lean
open SciLean Scalar
variable {R} [RealScalar R]

@[fun_trans]
theorem fun1.arg_xz.fwdFDeriv'_rule (y : R) :
    fwdFDeriv' R (fun (xz : R×R) => fun1 xz.1 y xz.2)
    =
    fun ((x,z),(dx,dz)) => 
      (fun1 x y z, 
       exp x * (dz * cos (z + y)) + dx * exp x * sin (z + y) + dz) := by 
  unfold fwdFDeriv' fun1; fun_trans
```
Writing rules for user defined functions like {lean}`fun1` is tedious and because {lean}`fun1` is defined in terms of known function the right hands side of this rule should be automatically generated anyway. We will discuss this how to do this a bit later. Here we just wanted to demonstrate that you can indeed formulate the transformation rule only for a subset of the input arguments. The important rule is that the order of the arguments should be maintained e.g. the left hand side should *not* be `fwdFDeriv' R (fun (zx : R×R) => fun1 zx.2 y zx.1)`.

In some cases the rule can get a bit tricky and there might be additional requirements on the arguments. The canonical example is division, `x / y`, which can be differentiated only if we divide by non zero `y`. In this case, the theorem can't be stated as a function in `((x,y),(dx,dy))` anymore. We have to fix particular value and require that the `y` is non zero. 
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]

@[fun_trans]
theorem HDiv.hDiv.arg_a0a1.fwdFDeriv'_rule_simple 
    (xydxy : (R×R)×(R×R)) (h : xydxy.1.2 ≠ 0) :
    (fwdFDeriv' R fun xy : R×R => xy.1 / xy.2) xydxy
    =
    let ((x,y),(dx,dy)) := xydxy
    (x/y, (dx*y - x*dy)/ (y^2)) := by 
  unfold fwdFDeriv'
  fun_trans (disch:=apply h)
```
Note that the argument to the theorem is `(xydxy : (R×R)×(R×R))` instead of `(x y dx dy : R)`. Not writing the product pattern explicitely as `((x,y),(dx,dy))` on the left hand side of the rule makes it easier for `fun_trans` to apply this transformation rule.

## User Defined Functions



## Exercises

Define

# Free Variable Theorems

Often we can write down a function transformation rule for a whole class of functions at once. The canonical example of this is that the derivative of liner function is the function itself. For {lean}`fwdFDeriv'` this is whould be
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]

@[fun_trans]
theorem fwdFDeriv'.linear_rule 
    (f : X → Y) (hf : IsContinuousLinearMap R f) :
    fwdFDeriv' R f 
    = 
    fun xdx => (f xdx.1, f xdx.2) := by 
  unfold fwdFDeriv'; fun_trans
```

The characteristic feature of these theorems is that the left hand side of the rule is about a single free variable function `f` and the theorem has some nontrivial conditions on the function `f`.

These theorems are potentially dangerous as the left hand side of the theorem can match an arbitrary function. The tactic `fun_trans` would be incredibly slow if it tried applying these theorems at every step. Therefore "free variable theorems" are applied only in cases when the function that is being transformed can't be written as non-trivial composition of two functions.


## Exercises

1. Write down free variable theorem for differentiating affine function.
::: Solution
```lean
open SciLean
variable 
  {R} [RCLike R]
  {X} [NormedAddCommGroup X] [NormedSpace R X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]

@[fun_trans]
theorem fwdFDeriv'.affine_rule 
    (f : X → Y) (hf : IsAffineMap R f) (hf' : Continuous f) :
    fwdFDeriv' R f 
    = 
    fun xdx => (f xdx.1, f xdx.2 - f 0) := by 
  unfold fwdFDeriv'; funext (x,dx)
  let g := (fun x => f x - f 0)
  have hf'' : IsContinuousLinearMap R g := by 
    simp (config:={zetaDelta:=true}) [g]
    constructor
    · apply hf.1
    · unfold autoParam; fun_prop
  have h : f = fun x => g x + f 0 := by simp (config:={zetaDelta:=true})
  rw[h]
  fun_trans -- this does not seem to work :(
  sorry_proof
```
:::

::: TODO
make the proof trivial i.e. `unfold fwdFDeriv' R f; fun_trans`
:::

# Morphism Theorems



# Advanced Function Theorems

## Compositional form

There is also an alternative way of fomulating function theorems in so called "compositional form". The idea is that we introduce and auxiliary type `W` and parametrize every of the function with this type. The "compositional form" of negation theorem
```lean
open SciLean
variable 
  {R} [RCLike R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [NormedSpace R X]

@[fun_trans]
theorem Neg.neg.arg_a0.fwdFDeriv'_rule_compositional 
    (f : W → X) (hf : Differentiable R f) :
    fwdFDeriv' R (fun w : W => - f w)
    =
    fun wdw => 
      let xdx := fwdFDeriv' R f wdw
      (-xdx.1, -xdx.2) := by unfold fwdFDeriv'; fun_trans
```
The original form of formulating "function theorems" is called "simple form" or "uncurried form" as for function of multiple arguments has to be uncurried.

In simple cases, it does not really matter which form you use but in more complicated scenarios like dealing with higher order functions the "compositional form" is the only way of formulating the function transformation rules. Also certain function transformations seem to support only "compositional form". At the end of this chapter give an example of such function transformation called `vectorize`.


The general idea behing the "compositional form" is that we parametrize every argument of the function with some auxiliary type `W` and then we state the function transformation rule in terms of the argument `(w : W)`.


The theorem for addition in "simple form" 
This form is also called "uncurried form" as the left hand side contains uncurried version for addition `fun (x : X×X) => x.1 + x.2`.

The "compositional form" of this theorem is
```lean
open SciLean
variable 
  {R} [RCLike R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [NormedSpace R X]

@[fun_trans]
theorem HAdd.hAdd.arg_a0a1.fwdFDeriv'_rule_compositional 
    (f g : W → X) (hf : Differentiable R f) (hg : Differentiable R g) :
    (fwdFDeriv' R fun w : W => f w + g w)
    =
    fun xdx => 
      let ydy := fwdFDeriv' R f xdx
      let zdz := fwdFDeriv' R g xdx
      (ydy.1 + zdz.1, ydy.2 + zdz.2) := by unfold fwdFDeriv'; fun_trans
```



## Polymorphic Functions

## High Order Functions

## Recursive Functions
