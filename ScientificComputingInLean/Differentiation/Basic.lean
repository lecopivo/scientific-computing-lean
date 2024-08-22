import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open Lean.MessageSeverity
open SciLean

#doc (Manual) "Introduction" =>

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

# Notation for Derivative

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


We can differentiate w.r.t to a vector valued variable `(x : ℝ×ℝ)`
```lean (name:=vecderiv1)
#check (∂ (x : ℝ×ℝ), ‖x‖₂²) rewrite_by fun_trans
```
```leanOutput vecderiv1
fun x => fun dx =>L[ℝ] 2 * ⟪dx, x⟫_ℝ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ
```
For derivatives w.r.t. a vector valued variable we have to also specify the direction in which we differentiate. Therefore in the above we obtained derivative as a function of the position `x` and direction `dx`. Furthermore, the notation `fun dx =>L[ℝ] ...` indicates that the function is linear function in `dx` and similarly `X →L[ℝ] Y` stands for the space of ℝ-linear functions from `X` to `Y`.

If we want to specify the position and the direction in which we want to compute the derivatives we use the notation `∂ (x:=x₀;dx₀), f x`
```lean (name:=vecderiv2)
variable (x₀ dx₀ : ℝ×ℝ)
#check (∂ (x:=x₀;dx₀), ‖x‖₂²) rewrite_by fun_trans
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


The last convenience is to get rid of the tedious `rewrite_by fun_trans`. We can add exclamation mark after `∂` to indicate that we want to run `fun_trans` tactic to compute the derivative.
```lean (name:=bangderiv)
variable (n : Nat)
#check (∂! (x : ℝ), x^n)
```
```leanOutput bangderiv
fun x => ↑n * x ^ (n - 1) : ℝ → ℝ
```
Note that `∂!` is actually runnning `autodiff` tactic instead of `fun_trans`. The tactic `autodiff` is just specially configured `fun_trans` such that it yields better results for programs and it will be discussed later.


# Derivative Examples

## Newton's solver

Let's put computing derivatives to some practical use. In scientific computing a common task is to solve non-linear equation \\( f(x) = 0 \\) for some complicated function \\( f \\). Very often this can be done only approximately and a common tool is Newton's method which starts with an initial guess \\(x₀\\) which is incrementally improved by the following rule
```latex
x_{n+1} = x_n - \frac{f(x_n)}{f'(x_n)}
```

We can use Newton's method to compute sqruare root of \\(y\\) by choosing \\( f(x) = x^2 - y\\).
```lean (name := mysqrt)
set_default_scalar Float

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

::: TODO

Exercise
1. try to solve different equations, for example `exp x = y` to obtain `log`, `x*exp x = y` to obtain Lambert W function or some polynomial.

2. A difficult exercise is to define a general `newtonSolve` function that takes an arbitrary function `f : Float → Float` and uring elaboration synthesizes its derivative. Add multiple hints, 1. use `infer_var` trick, 2. state explicitly how the arguments should look like

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
:::



## Simple Kinematics


We can also use *SciLean*'s symbolic differentiation to prove some basic theorems from physics. For example we can state the second Newton's law
```lean
set_default_scalar ℝ

def NewtonSecondLaw (m : ℝ) (x : ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ t, m * deriv (∂ x) t = F t
```
saying that for a particle with mass `m` under the influence of force `F` has trajectory `x` if the mass times the acceleration `deriv (∂ x) t`, i.e. the second derivative of trajectory, is equal to the force `F t`.


We can show that under constant force `f` a particle with mass `m` has trajectory `(fun t => 1/2 * f/m * t^2)`
```lean
example (m f : ℝ) (hm : m ≠ 0) :
    NewtonSecondLaw m (fun t => 1/2 * f/m * t^2) (fun _ => f) := by

  unfold NewtonSecondLaw
  fun_trans [deriv] -- compute derivatives
  field_simp; ring  -- finish algebraic simplifications
```

::: TODO

Warning: Right now `fun_trans` uses theorems that use sorry thus the theorem is not fully proven.

:::
