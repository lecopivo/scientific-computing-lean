import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open Lean.MessageSeverity
open SciLean


#doc (Manual) "Symbolic Differentiation" =>

Differentiation is at the heart of many problems in scientific computing, from optimizing functions to solving differential equations. Computing derivatives is a mechanical process but very error prone when done manually. In this chapter, we will explore how we can compute derivatives of expressions and programs automatically.

Let's recall what derivative is, for a function `f : ℝ → ℝ` we define it derivative as
```latex
f'(x) = \lim_{h → 0} \frac{f(x+h) - f(x)}{h}
```
The mathematical library *Mathlib* defines derivative {lean}`fderiv` for a general function `f : X → Y` from some vector spaces `X` and `Y`. The derivative of `f` at point `x : X` in direction `dx : X` is
```latex
\texttt{fderiv ℝ f x dx} = \lim_{h → 0} \frac{f(x+h\cdot dx) - f(x)}{h}
```

*SciLean* provides tactic `fun_trans` which can compute derivatives. The name `fun_trans` stands for 'function transformation' and differentiations is just one example of function transformation. We will talk about general function transformations later in the book.

One of the simplest examples of a derivative is the derivative of \\(x^n\\) which is equal to \\(n x^\{n-1\}\\). Let's compute it using `fun_trans` tactic
```lean (name:=xnderiv)
variable (n : Nat) (x : ℝ)
#check (fderiv ℝ (fun (x : ℝ) => x^n) x 1) rewrite_by fun_trans
```
```leanOutput xnderiv
↑n * x ^ (n - 1) : ℝ
```

::: TODO
Add a link to an interactive code editor and encourage reader to differentiate more complicated expressions involving sin, cos, exp, ... but warn about log or division.
:::

# Notation

Writing `fderiv ℝ (fun x => f x)` is somewhat tedious so *SciLean* makes our life easier by introducing a nice notation `∂ x, f x` for differentiating `(f x)` w.r.t. `x`.

Before we explore this notation further we have to mention that  {lean}`fderiv` can also compute complex derivatives with {lean}`fderiv ℂ` instead of {lean}`fderiv ℝ`. However, most of the time we work exclusively with real derivative so we can inform Lean that the default choce of the scalar field are real numbers using the following command
```lean
set_default_scalar ℝ
```
Now Lean knows that we want real derivative when we write `∂ x, f x`.


Using this notation we can compute again the above derivative
```lean (name:=nxderiv2)
variable (n : Nat)
#check (∂ (x : ℝ), x^n) rewrite_by fun_trans
```
```leanOutput nxderiv2
fun x => ↑n * x ^ (n - 1) : ℝ → ℝ
```
Because we did not specify the point where we want to compute the derivative we obtained a function in `x`. We can specify the point where we want to compute the derivative with `∂ (x:=x₀), ...`
```lean (name:=nxderiv3)
variable (n : Nat) (x₀ : ℝ)
#check (∂ (x:=x₀), x^n) rewrite_by fun_trans
```
```leanOutput nxderiv3
↑n * x₀ ^ (n - 1) : ℝ
```

Writing `rewrite_by fun_trans` every time we want to diferentiate an expression gets a bit tedious. We can add an exclamation mark after `∂` to indicate that we want to run `fun_trans` tactic to compute the derivative.
```lean (name:=bangderiv)
variable (n : Nat)
#check (∂! (x : ℝ), x^n)
```
```leanOutput bangderiv
fun x => ↑n * x ^ (n - 1) : ℝ → ℝ
```

We can differentiate w.r.t to a vector valued variable `(x : ℝ×ℝ)`
```lean (name:=vecderiv1)
#check ∂! (x : ℝ×ℝ), ‖x‖₂²
```
```leanOutput vecderiv1
fun x => fun dx =>L[ℝ] 2 * ⟪dx, x⟫_ℝ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ
```
For derivatives w.r.t. a vector valued variable we have to also specify the direction in which we differentiate. Therefore in the above we obtained derivative as a function of the position `x` and direction `dx`. Furthermore, the notation `fun dx =>L[ℝ] ...` indicates that the function is linear function in `dx` and similarly `X →L[ℝ] Y` stands for the space of ℝ-linear functions from `X` to `Y`.

If we want to specify the position and the direction in which we want to compute the derivatives we use the notation `∂ (x:=x₀;dx₀), f x`
```lean (name:=vecderiv2)
variable (x₀ dx₀ : ℝ×ℝ)
#check ∂! (x:=x₀;dx₀), ‖x‖₂²
```
```leanOutput vecderiv2
2 * ⟪dx₀, x₀⟫_ℝ : ℝ
```

To summarize all the different variants. For function of a scalar valued argument
```lean
variable (f : ℝ → ℝ) (x₀ : ℝ)

#check ∂ f
#check ∂ x, f x
#check ∂ (x:=x₀), f x
```

For function of a vector valued argument
```lean
variable (f : ℝ×ℝ → ℝ) (x₀ dx₀ : ℝ×ℝ)

#check ∂ f
#check ∂ x, f x
#check ∂ (x:=x₀), f x
#check ∂ (x:=x₀;dx₀), f x
```

There is nothing stopping us from applying derivative multiple times to compute higher order derivatives
```lean (name:=sndderiv)
#check (∂! (∂! (x:ℝ), x^2))
```
```leanOutput sndderiv
fun x => 2 : ℝ → ℝ
```


## Exercises

1. For a function of two arguments `f x y` write a derivative at `x:=x₀` and `y:=y₀` w.r.t 
  - the first argument
  - the second argument
  - both arguments at the same time

```lean
variable (f : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ)
#check ∂ (x:=x₀), (f x y₀)
#check ∂ (f · y₀) x₀
-- both notations are identical
example : (∂ (x:=x₀), (f x y₀)) = (∂ (f · y₀) x₀) := by rfl

#check ∂ (y:=y₀), (f x₀ y)
#check ∂ (f x₀ ·) y₀
example : (∂ (y:=y₀), (f x₀ y)) = (∂ (f x₀ ·) y₀) := by rfl

#check ∂ ((x,y):=(x₀,y₀)), f x y
#check ∂ (fun (x,y) => f x y) (x₀, y₀)
#check ∂ (↿f) (x₀, y₀)
example : (∂ ((x,y):=(x₀,y₀)), f x y) = (∂ (fun (x,y) => f x y) (x₀, y₀)) := by rfl
example : (∂ ((x,y):=(x₀,y₀)), f x y) = (∂ (↿f) (x₀, y₀)) := by rfl
```

2. second derivative of `f x y` 

```lean
variable (f : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ)
#check ∂ (x':= x₀), ∂ (x'':=x'), (f x'' y₀)
#check ∂ (∂ (f · y₀)) x₀
example : (∂ (x':= x₀), ∂ (x'':=x'), (f x'' y₀)) = (∂ (∂ (f · y₀)) x₀) := by rfl

#check ∂ (y':=y₀), ∂ (y'':=y'), (f x₀ y'')
#check ∂ (∂ (f x₀ ·)) y₀

#check ∂ ((x,y):=(x₀,y₀)), f x y
#check ∂ (fun (x,y) => f x y) (x₀, y₀)
#check ∂ (↿f) (x₀, y₀)
```


3. One dimensional Euler-Lagrange equation

```lean
variable (L : ℝ → ℝ → ℝ) (x : ℝ → ℝ) (t : ℝ)

---    d/dt       ∂/∂v          L x v      - ∂/∂x      
#check 
  let v := ∂ x
  ∂ (t':=t), (∂ (v':=v t), L (x t) v') - ∂ (x':=x t), L x' (v t)
```

# Examples

Let's put computing derivatives to some practical use. We will demonstrate how to use *SciLean* symbolic differentiations to solve few common tasks in scientific computing and physics.

## Newton's solver

Solving non-linear equation \\( f(x) = 0 \\) is a very common problem in scientific computing. Often this can be done only approximately and a popular tool to do so is Newton's method. It is an interative process that starts with an initial guess \\(x₀\\) which is incrementally improved by the following rule
```latex
x_{n+1} = x_n - \frac{f(x_n)}{f'(x_n)}
```

We can use Newton's method to compute sqruare root of \\(y\\) by choosing \\( f(x) = x^2 - y\\).
```lean (show := false)
set_default_scalar Float
```
```lean (name := mysqrt)
def mySqrt (steps : Nat) (y : Float) : Float := Id.run do
  let f := fun x => x^2 - y
  let mut x := 1.0
  for _ in [0:steps] do
    x := x - f x / ((deriv f x) rewrite_by fun_trans[deriv])
  return x

#eval mySqrt 10 2.0
```
```leanOutput mysqrt
1.414214
```
::: TODO
In {lean}`mySqrt` we should use `(∂! f x)` notation but unfortunatelly it is currently broken for some reason.
:::

You might feel a bit unconfortable here are we are differentiating a function defined on floating point numbers. If you think that can't be formally correct then you are right. We will discuss this issue in a later chapter "Working with Real Numbers".


### Exercises
1. try to solve different equations, for example `exp x = y` to obtain `log`, `x*exp x = y` to obtain Lambert W function or some polynomial.

2. measure relative,\\(\\left| \\frac\{f(x\_n)\}\{x\_n\} \\right| \\), and absolute error \\( \\left| f(x\_n) \\right| \\) and use them for stopping criteria.

3. A difficult exercise is to define a general `newtonSolve` function that takes an arbitrary function `f : Float → Float` and uring elaboration synthesizes its derivative. Add multiple hints, 1. use `infer_var` trick, 2. state explicitly how the arguments should look like

```lean
set_default_scalar Float
def newtonSolve (steps : Nat) (x₀ : Float)
    (f : Float → Float) {f' : Float → Float}
    (hf : f' = (∂ f) := by unfold deriv; fun_trans; infer_var) : Float := Id.run do
  let mut x := x₀
  for _ in [0:steps] do
    x := x - f x / f' x
  return x

#eval newtonSolve 10 1.0 (fun x => x^2 - 2.0)
```


## Kinematics

```lean (show:=false)
set_default_scalar ℝ
```

We can also use *SciLean*'s symbolic differentiation to prove some basic theorems from physics. For example we can state the second Newton's law
```lean

def NewtonSecondLaw (m : ℝ) (x : ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ t, m * deriv (∂ x) t = F t
```
saying that for a particle with mass `m` under the influence of force `F` has trajectory `x` if the mass times the acceleration `deriv (∂ x) t`, i.e. the second derivative of trajectory, is equal to the force `F t`.


We can show that under constant force `f` a particle with mass `m` has trajectory `(fun t => 1/2 * f/m * t^2)`
```lean
example (m f : ℝ) (hm : m ≠ 0) :
    NewtonSecondLaw m (fun t => 1/2 * f/m * t^2) (fun _ => f) := by

  unfold NewtonSecondLaw
  -- compute derivatives
  fun_trans [deriv]
  -- finish algebraic simplifications
  field_simp; ring
```

::: TODO

*Warning*: currently the tactic `fun_trans` uses theorems that are not fully proven therefore the above proof is not completely formal proof. If you do not like this you are welcome to improve SciLean by helping out proving its theorems. Lots of theorems should be just matter of finding the right mathlib theorem.

:::




### Exercises

1. show that trajectory `x := fun t => (cos t, sin t)` satisfies differential equation `∂ x t = (- (x t).2, (x t).1)`

```lean
open SciLean Scalar
def ode (x : ℝ → ℝ×ℝ) := ∀ t, deriv x t = (- (x t).2, (x t).1)

example : ode (fun t => (cos t, sin t)) := by unfold ode deriv; fun_trans
```

2. show that trajectory `x := fun t => sin (ω*t)` correspond to the force `f := fun t => - k * x t` with `ω = sqrt (k/m)`

Hint: After differentiation you will have to show that \\(m \\sqrt\{\\frac\{k\}\{m\}\}^2 = k\\). Unfortunatelly Lean is not yet very powerful computer algebra system. So you can finish the proof with
```
  ring_nf --  m * (sqrt (k / m) * (sqrt (k / m) ==> m * sqrt (k * m⁻¹) ^ 2
  have h : m * sqrt (k * m⁻¹) ^ 2 = k := sorry_proof
  simp[h]
```
where we call `ring_nf` to clean up the expression, then we just assume that ` m * sqrt (k * m⁻¹) ^ 2` is equal to `k` and finally we can finish the proof by running simp
```lean
open SciLean Scalar

example (m k : ℝ) :
    let ω := sqrt (k/m)
    let x := fun t => sin (ω*t)
    NewtonSecondLaw m x (fun t => - k*x t) := by

  unfold NewtonSecondLaw deriv
  fun_trans
  ring_nf
  have h : m * sqrt (k * m⁻¹) ^ 2 = k := sorry_proof
  simp[h]
```

Warning: Right now `fun_trans` uses theorems that use sorry thus the theorem is not fully proven.

3. show that `u = fun t x => sin (x - t)` is solution to wave equation, 1D and n-D

```latex
\frac{\partial^2 u}{\partial t^2} = \frac{\partial^2 u}{\partial x^2}
```

```lean
open SciLean Scalar
def WaveEquation (u : ℝ → ℝ → ℝ) := ∀ x t, (∂ (∂ (u · x)) t) = (∂ (∂ (u t ·)) x)

example : 
    WaveEquation (fun t x => sin (x - t)) := by
  unfold WaveEquation deriv
  fun_trans

```

4. solution to heat equation


# Gradient

In many practical applications, we need to compute gradient instead of directional derivative. For a function \\(f : \\mathbb\{R\}^n \\rightarrow \\mathbb\{R\} \\) the gradient of \\(f\\) is a vector of all its partial derivatives
```latex
\nabla f = \left(\frac{\partial f}{\partial x_1}, \dots, \frac{\partial f}{\partial x_n} \right)
```

A more general way of defining gradient is through linear map transposition/adjoint. The derivative of a function `(f : X → ℝ)` at point `x` is a linear map from `X` to `ℝ`
```lean (name := linmapderiv)
open SciLean
variable {X} [NormedAddCommGroup X] [AdjointSpace ℝ X] [CompleteSpace X]
variable (f : X → ℝ) (x : X)
#check (∂ f x)
```
```leanOutput linmapderiv
∂ f x : X →L[ℝ] ℝ
```

To obtain gradient we take an adjoint and evaluate it at one. This is exactly how gradient is defined.
```lean
open SciLean
variable {X} [NormedAddCommGroup X] [AdjointSpace ℝ X] [CompleteSpace X]
variable (f : X → ℝ) (x : X)
example : (∇ f x) = adjoint ℝ (∂ f x) 1 := by rfl
```

This coincides with the standard notion of gradient that it is a vector of all its partial derivatives. For example for `n=2` we have
```lean
open SciLean
variable {n : Nat} (f : ℝ×ℝ → ℝ) (hf : Differentiable ℝ f) (x y : ℝ)
example : (∇ f (x,y)) = (∂ (x':=x), f (x',y), ∂ (y':=y), f (x,y')) := sorry_proof
```

::: TODO

*Warning for mathlib users*: SciLean defines its own version of `adjoint` and `gradient`. The reason is that the product type `ℝ×ℝ` and function type `Fin n → ℝ` are not `InnerProductSpace` and therefore it is impossible do use mathlibs `gradient` on functions of type `ℝ×ℝ → ℝ` or `(Fin n → ℝ) → ℝ`. Mathlib's advice is to use `WithLp 2 (ℝ×ℝ)` or `EuclidianSpace n` however this is seriously inconvenient for people that just want to write some code.

SciLean solution to this is to introduce new typeclass `AdjointSpace ℝ X` that is almost the same as `InnerProductSpace ℝ X` but requires that the norm induced by inner product, `‖x‖₂ = ⟪x,x⟫`, is topologically equivalent to the norm `‖x‖`. This way we can provide instance of `AdjointSpace ℝ (X×Y)` and `AdjointSpace ℝ (ι → X)` without causing issues.

:::


Few examples of of computing gradients
```lean (name:=gradfst)
variable (x₀ : ℝ×ℝ)
#check ∇! (x:=x₀), x.1
```
```leanOutput gradfst
(1, 0) : ℝ × ℝ
```

```lean (name:=gradnorm2)
variable (x₀ : ℝ×ℝ)
#check ∇! (x:=x₀), ‖x‖₂²
```
```leanOutput gradnorm2
2 • x₀ : ℝ × ℝ
```

```lean (name:=gradinner)
variable (x₀ y : ℝ×ℝ)
#check ∇! (x:=x₀), ⟪x,y⟫
```
```leanOutput gradinner
y : ℝ × ℝ
```

## Exercises

1. Previously we computed \\(\\sqrt\{y\}\\) using Newton's method. Similarly we can {lean}`mySqrt` Compute `sqrt y` using gradient descent by minimizing objective function `f := fun x => (x^2 - y)^2`

2. Linear regression via gradient descent
   `x : Float^[2]^[n]` `y : Float^[2]^[n]`
   `fun := fun (A : Float^[2,2]) => ∑ i, ‖ ⊞ i' => ∑ j, A[i',j] * x[i][j] - y[i]‖₂²`

```lean
set_default_scalar Float

variable (n : Nat) (x y : Float^[2]^[n])

#check (∇ (A : Float^[2,2]), ∑ i, ‖(⊞ i' => ∑ j, A[i',j] * x[i][j]) - y[i]‖₂²) rewrite_by unfold SciLean.fgradient; fun_trans; unfold SciLean.revFDerivProj; fun_trans
```

3. Evalute gradient of `x[0]`, `‖x‖₂²`, `⟪x,y⟫` for `x y : Float^[3]` or for `A : Float^[3,3]`

4. Euler-Lagrange equation in arbitrary dimension and show that for lagrangian `L x v := 1/2 * m * ‖v‖₂² - φ x` the Euler-Langran equation is `m * ∂ (∂ x) t = - ∇ φ x`

```lean
set_default_scalar ℝ
variable {X} [NormedAddCommGroup X] [AdjointSpace ℝ X] [CompleteSpace X]

variable (L : X → X → ℝ) (x : ℝ → X) (t : ℝ)

#check 
  let v := ∂ x
  ∂ (t':=t), (∇ (v':=v t), L (x t) v') - ∇ (x':=x t), L x' (v t)
```



# Derivative Rules

```lean (show:=false)
set_default_scalar ℝ
```

A commong issue when `fun_trans` is not doing what we expect is that there is a missing differentiation theorem.

For example, if we define a function
```lean
def foo (x : ℝ) := x^2 + x
```
then nothing happens when we try to differentiate it
```lean (name:=fooderivnothing)
#check ∂! x, foo x
```
```leanOutput fooderivnothing
fun x => (∂ (x:=x), foo x) 1 : ℝ → ℝ
```
Turning on the `fun_trans` trace reveals useful information
```lean
set_option trace.Meta.Tactic.fun_trans true in
#check ∂! x, foo x
```
```
[Meta.Tactic.fun_trans] [❌] ∂ (x:=x), foo x
  [Meta.Tactic.fun_trans] candidate theorems for foo: []
  [Meta.Tactic.fun_trans] candidate local theorems for foo: []
  [Meta.Tactic.fun_trans] candidate fvar theorems: [isContinuousLinearMap_fderiv]
  [Meta.Tactic.fun_trans] [❌] applying: isContinuousLinearMap_fderiv
    [Meta.Tactic.fun_trans] isContinuousLinearMap_fderiv, failed to discharge hypotheses
          SciLean.IsContinuousLinearMap ℝ fun x => foo x
```

The `❌` on the first line signifies that `fun_trans` failed to make prograss on `∂ (x:=x), foo x`. The next two lines
```
  [Meta.Tactic.fun_trans] candidate theorems for foo: []
  [Meta.Tactic.fun_trans] candidate local theorems for foo: []
```
states that there are no derivative theorems for {lean}`foo`. The next line
```
  [Meta.Tactic.fun_trans] candidate fvar theorems: [isContinuousLinearMap_fderiv]
```
states that there is a potentially applicable theorem {lean}`isContinuousLinearMap_fderiv` which can differentiate linear functions. However the next few lines report that applying this theorem failed as `fun_trans` can't prove that `foo` is (continuous) linear map.


To remedy this problem we can define derivative of {lean}`foo`
```lean
def foo_deriv (x : ℝ) := 2*x + 1
```
and add a theorem that the derivative of {lean}`foo` is equal to {lean}`foo_deriv`
```lean
open SciLean
@[fun_trans]
theorem foo_deriv_rule : fderiv ℝ foo = fun x => fun dx =>L[ℝ] dx • foo_deriv x := by unfold foo foo_deriv; ext x; fun_trans
```

Because {lean}`foo_deriv_rule` is marked with `fun_trans` attribute it will be used when we try to differentiate `foo` now
```lean (name:=fooderiv)
#check ∂! x, foo x
```
```leanOutput fooderiv
fun x => foo_deriv x : ℝ → ℝ
```


Unfortuantelly there is one more issue, `fun_trans` will do nothing when we try to compose `foo` together
```lean (name:=foofooderiv)
#check ∂! x, foo (foo x)
```
```leanOutput foofooderiv
fun x => (∂ (x:=x), foo (foo x)) 1 : ℝ → ℝ
```
```lean
set_option trace.Meta.Tactic.fun_trans true in
#check ∂! x, foo (foo x)
```
```
...
  [Meta.Tactic.fun_trans] trying comp theorem SciLean.fderiv.comp_rule
  [Meta.Tactic.fun_trans] [❌] applying: SciLean.fderiv.comp_rule
    [Meta.Tactic.fun_trans] SciLean.fderiv.comp_rule, failed to discharge hypotheses
          Differentiable ℝ fun x0 => foo x0
...
```
The trace will reveal that `fun_trans` tries to apply composition(chain) rule {lean}`SciLean.fderiv.comp_rule` but it fails as it can't prove {lean}`Differentiable ℝ fun x0 => foo x0`. We need another theorem stating that {lean}`foo` is differentiable function. Mathlib has a tactic `fun_prop` that can prove differentiability and many other function properties like linearity, continuity, measurability etc. and `fun_trans` uses this tactic to ensure it can apply chain rule.

Therefore we need to add `fun_prop` theorem for {lean}`foo`
```lean
@[fun_prop]
theorem foo_differentiable : Differentiable ℝ foo := by unfold foo; fun_prop
```
Now `fun_trans` knows that {lean}`foo` is differentiable function and can safely apply chain rule
```lean (name:=foofooderivsuccess)
#check (∂! x, foo (foo x)) rewrite_by simp
```
```leanOutput foofooderivsuccess
fun x => foo_deriv x * foo_deriv (foo x) : ℝ → ℝ
```

Writing these theorems by hand is quite tedious so there is a macro `def_fun_prop` and `def_fun_trans` to help you with writing these theorems
```lean
def_fun_prop : Differentiable ℝ foo by unfold foo; fun_prop
def_fun_trans : fderiv ℝ foo by unfold foo; fun_trans
```
It generates these theorems and definition
```lean (name:=foodiffrule)
#check foo.arg_x.Differentiable_rule
#print foo.arg_x.fderiv
#check foo.arg_x.fderiv_rule
```
The problem of writing appropriate theorems for `fun_trans` and `fun_prop` is quite involve problem and will be discussed in future chapter.



# Differentiating Division, Log, Sqrt, ...

```lean (show:=false)
set_default_scalar ℝ
```

So far we have worked with functions that are smooth. However, functions like division, `log`, `sqrt`, `‖·‖₂` are not differentiable everywhere. We have to be a bit careful with those functions because *SciLean* tries to perform computations that are, at least in principle, fully formalizable. Let's try to differentiate division
```lean (name:=divderiv)
#check ∂! (x:ℝ), 1/x
```
```leanOutput divderiv
fun x => (∂ (x:=x), x⁻¹) 1 : ℝ → ℝ
```
We did not get expected `-x⁻²`. When differentiation, or any tactic, is not doing what we expect we can turn on tracing. Let's try again with tracing on
```lean
set_option trace.Meta.Tactic.fun_trans true in
#check ∂! (x:ℝ), 1/x
```
and the beggining of the trace is saying that `fun_trans` tried to apply theorem {lean}`HDiv.hDiv.arg_a0a1.fderiv_rule_at` however it failed to discharge `x ≠ 0`
```
[Meta.Tactic.fun_trans] [❌] ∂ (x:=x), 1 / x
  [Meta.Tactic.fun_trans] candidate theorems for HDiv.hDiv: [HDiv.hDiv.arg_a0a1.fderiv_rule_at]
  [Meta.Tactic.fun_trans] [❌] applying: HDiv.hDiv.arg_a0a1.fderiv_rule_at
    [Meta.Tactic.fun_trans] [❌] discharging: x ≠ 0
    [Meta.Tactic.fun_trans] HDiv.hDiv.arg_a0a1.fderiv_rule_at, failed to discharge hypotheses
          x ≠ 0
```
This makes sense as division `1/x` is well defined and differentiable only away from zero. Therefore we have to differentiate it at a concrete point that is not equal to zero.
```lean (name:=divderivsucc)
variable (x₀ : ℝ) (hx₀ : x₀ ≠ 0)
#check (∂ (x:=x₀), 1/x) rewrite_by fun_trans (disch:=assumption)
```
```leanOutput divderivsucc
-(x₀ ^ 2)⁻¹ : ℝ
```
We introduced a point `x₀` and assumption `hx₀` that it is not equal to zero. By default `fun_trans` does not see this assumption and we have to provide discharger. A discharger is any tactic that tries to satisfy(discharge) any assumption of the theorems `fun_trans` is using. In this simple case `assumption` tactic is enough as it just looks through the local context and tries to directly apply any existing assumptions.

Using `assumption` is not enough for a more complicated expression
```lean (name:=divsqderiv)
variable (x₀ : ℝ) (hx₀ : x₀ ≠ 0)
#check (∂ (x:=x₀), 1/x^2) rewrite_by fun_trans (disch:=assumption)
```
```leanOutput divsqderiv
∂ (x:=x₀), (x ^ 2)⁻¹ : ℝ
```
tracing shows
```
[Meta.Tactic.fun_trans] HDiv.hDiv.arg_a0a1.fderiv_rule_at,
  failed to discharge hypotheses x₀ ^ 2 ≠ 0
```
We need a tactic that is capable of infering `(x₀^2 ≠ 0)` from `(x₀ ≠ 0)`. A very general and powerful tactic is `aesop`
```lean (name:=divsqderivsucc)
variable (x₀ : ℝ) (hx₀ : x₀ ≠ 0)
#check (∂ (x:=x₀), 1/x^2) rewrite_by fun_trans (disch:=aesop)
```
```leanOutput divsqderivsucc
-(2 * x₀) / (x₀ ^ 2) ^ 2 : ℝ
```


In multiple dimensions we often want to differentiate the norm
```lean
open SciLean Scalar

variable (x₀ : ℝ×ℝ) (hx₀ : x₀ ≠ 0)

#check (∇ (x:=x₀), ‖x‖₂) rewrite_by unfold fgradient; fun_trans (disch:=assumption)
```
The fact that norm is not differentiable can cause issues. The common practice when writing numerical algorithms is to regularize norm using a small positive `ε`.
```lean (name:=smoothnormgrad)
open SciLean Scalar
variable (ε : ℝ) (hε : 0 < ε)

#check (∂ (x:ℝ×ℝ), sqrt (ε + ‖x‖₂²)) rewrite_by
  unfold deriv
  fun_trans (disch:=intro x; nlinarith [norm2_nonneg ℝ x])
```
```leanOutput smoothnormgrad
fun w => fun x =>L[ℝ] 2 * ⟪x, w⟫_ℝ / (2 * sqrt (ε + ‖w‖₂²)) : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ
```

::: TODO

Figuring out the right tactic like `intro x; nlinarith [norm2_nonneg ℝ x]` can be difficult. Therefore introduce tactic/discharger `unsafe_ad_disch` that assumes commong AD assumptions and reports them back to user.

Create unsafe mode differentiation which assumes that everything works out. Effectivelly this requires discharger that recognize commong goals that should be sorries or postponed.

:::

## Exercises

1. gradient of energy for n-body system, newton's potential, lenard jones potential
  - do it for two particles 
  - do it for n-particles

2. signed distance function 
  - compute gradient of sphere sdf
  - compute mean and gaussian curvature of sphere

  - pick SDF from https://iquilezles.org/articles/distfunctions/
    - most of them involve functions that are not differentiable everywhere
    - compute derivative in unsafe mode
    - figure out the minimal condition under which it is differentiable
      

