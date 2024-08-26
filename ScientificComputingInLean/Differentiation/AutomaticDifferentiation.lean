import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open Lean.MessageSeverity
open SciLean

set_default_scalar ℝ

#doc (Manual) "Automatic Differentiation" =>


In scientific computing a common requirement is to compute derivatives of a program. The important requirement is that the resulting program computing the derivative should be efficient. The problem with symbolic differentiation is that it can produce expressions which are really inefficient. So called *automatic differentiation* addresses this issue an computes derivatives that are also efficient to compute. 

Let's have a look how symbolic differentiation can produce large expressions.
```lean
open SciLean Scalar
#check (∂! (x : ℝ), x * x * x * x * x * x * x * x)
```

The last example, symbolic differentiation takes and expression with 9 mulplications and produces an expression with 27 multiplications and 7 additions.

If we instead use forward mode derivative(one type of automatic differentiation which we will explain in a moment)
```lean
#check (∂>! (x : ℝ), x * x * x * x * x * x * x * x) 
```
we obtain 21 multiplications and 7 additions. 

The difference might not seems to big but if you look at the shape of the result you can see that the the expression reulting from `∂` contains a big triangular block of multiplications whose size(in terms of multiplications) grows quadratically in the number of multiplications in the original expression. On the other hand when we use `∂>`, for every multiplication in the original expression we obtain one line with `ydy * x` and one line with `dx * ydy_i + ydy * dx`.

::: TODO

Add table with number of multplications and additions with growing `n`
::: 


# Forward Mode

The issue with symbolic differentiation is that the chain rule
```latex
(f\circ g)'(x) = f'(g(x)) g'(x)
```
repeats \\(g\\) on the right hand side twice which can lead to doubling of computation everytime we apply chainrule. 

The remedy to this problem is to introduce forward mode derivative \\( \\overrightarrow\{\\partial\} \\)
```latex
\overrightarrow{\partial} f (x,dx) = (f(x), f'(x) dx)
```
The motivation is that the forward mode derivative computes the value \\( f(x) \\) and the derivative \\( f'(x) dx \\) once and at the same time. Both values then can be comnsumed by subsequent computation without ever evaluating \\(f\\) again. The chain rule for forward mode derivative is
```latex
\overrightarrow{\partial} \left( f \circ g \right) =  \overrightarrow{\partial} f  \circ  \overrightarrow{\partial} g  
```
which does not suffer from the problem of repeating \\( g \\) twice and thus not potentially double the computation. 

In SciLean, the forward mode derivative is {lean}`fwdFDeriv` which has notaion `∂>`. It is defined as
```lean
open SciLean
variable (f : ℝ → ℝ) (x dx : ℝ)
example : (∂> f x dx) = (f x, ∂ f x dx) := by rfl
```
In Lean notation the chain rule can be writen as
```lean
open SciLean
variable (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x dx : ℝ)
example : (∂> (f ∘ g) x dx) = (let (y,dy) := (∂> g x dx); (∂> f y dy)) := by fun_trans[Function.comp]
```
Alternativelly, when we use the notation `↿f` that uncurries any function we can write the chain rule
```lean
open SciLean
variable (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
example : ↿(∂> (f ∘ g)) = ↿(∂> f) ∘ ↿(∂> g) := by fun_trans[Function.comp,Function.HasUncurry.uncurry]
```

In SciLean it is the theorem {lean}`SciLean.FwdFDeriv.comp_rule`.


## autodiff vs fun\_trans

So far we have been using the tactic `fun_trans` to compute derivatives. You might have notices that `fun_trans` removes all let bindings from the expression. For example
```lean (name:=derivwithfuntrans)
#check (∂ (x : ℝ), let y := x*x; y*x) rewrite_by unfold deriv; fun_trans
```
we can alternativelly use `autodiff` tactic
```lean (name:=derivwithautodiff)
#check (∂ (x : ℝ), let y := x*x; y*x) rewrite_by autodiff
```

The tactic `autodiff` behaves very similarly to `fun_trans` but it carefully handled let bindings which is important for generating efficient code. Internally it uses a slightly modified version of Lean's simplifier and carefully configured `fun_trans` such that it handles let bindings more carefully and efficiently.

From now one, the rule of thumb it to use `fun_trans` if you do not care about generating efficient code and want to just prove something using derivatives and to use `autodiff` when you care about the efficiency of the resulting code.

You might have noticed that let bindings are preserved when using `∂!` notation. This is because `∂!` is using the tactic `autodiff` instead of `fun_trans`. 

Note that when you want to compute efficient derivatives you have to use `autodiff` *and* forward mode derivative `∂>`. Using only one of them will not yield the most efficient code. 


## Relation to Dual Numbers 

One common explanation of forward mode derivative is through dual numbers \\(a + \\epsilon b \\). Similarly to complex numbers \\( \\mathbb\{C\}\\), which extend reals numbers with complex unit \\(i\\) that squares to negative one, \\(i^2 = -1\\), the dual numbers \\( \\overline\{\\mathbb\{R\}\}\\) extend real numbers with \\(\\epsilon\\) that squares to zero, \\(\\epsilon^2 = 0\\).

We can add and multiply two dual numbers
```latex
\begin{align}
(a + \epsilon b) + (c + \epsilon d) &= ((a + c) + \epsilon (b + d)) \\
(a + \epsilon b) (c + \epsilon d) &= ((a c) + \epsilon (b c + a d))
\end{align}
```
Through power series we can also calculate functions like sin, cos or exp
```latex
\begin{align}
\sin(a + \epsilon b) &= \sin(a) + \epsilon b \cos(a) \\
\cos(a + \epsilon b) &= \cos(a) - \epsilon b \sin(a) \\
\exp(a + \epsilon b) &= \exp(a) + \epsilon b \exp(a)
\end{align}
```
In general, for an analytical function `(f : ℝ → ℝ)` we can show that 
```latex
f(a + \epsilon b) = f(a) + \epsilon b f'(a)
```
Every dual number is just a pair of two real numbers i.e. \\( \\overline\{\\mathbb\{R\}\} \\cong \\mathbb\{R\} \\times \\mathbb\{R\} \\) therefore we can think about the forward mode derivative \\(\\overrightarrow\{\\partial\} f\\) as extension of \\(f\\) to dual numbers
```latex
\overrightarrow{\partial} f (x + \epsilon dx) = f(x) + \epsilon f'(x)dx
```

::: TODO

Explain this for general function `f : X → Y` and relate it to complexification of a vector space.

:::

## Exercises

1. In section (??) we defined a function `foo` 
```lean (keep:=false)
def foo (x : ℝ) := x^2 + x
```
In order to compute derivatives with `foo` you need to derivative generate theorems using `def_fun_trans` and `def_fun_prop` macros. Use `def_fun_trans` macro to generate forward mode derivative rule for `foo`.

2. Newton's method with forward mode AD. In previous chapter (??) we talked about Newton's method. At each iteration we need to compute the function value \\( f(x\_n)\\) and its derivative  \\( f'(x\_n)\\). Instead of evaluating `f x` and `∂! f x` use fowrward mode `∂>! f x 1` to compute the function value and its derivative at the same time.

3. Redo the exercises on Newton's method from chapter (??) using forward mode derivative `∂>` instead of normal derivative `∂`.

4. Prove on paper that the chain rule for forward mode derivative is equivalent to the standard chain rule.


# Reverse Mode


Forward mode derivative `∂> f` is designed to efficiently compute the derivative `∂ f`. To efficiently compute the gradient `∇ f` we have to introduce reverse mode derivative `<∂ f`. 


Recall the that definition of the gradient `∇ f` is adjoint of the derivative
```lean
variable (f : ℝ×ℝ → ℝ) (x : ℝ×ℝ)
example : (∇ f x) = adjoint ℝ (∂ f x) 1 := by rfl
```
One might naively do the same trick as with forward mode derivative and define reverse mode by putting together the function value and the derivative together i.e. `<∂ f x dy = (f x, adjoint ℝ (∂ f x) dy)`. However, it is not possible to write down a good chain rule for this operation. The only way to do this is to postpone the argument `dy` and define the reverse mode derivative as
```
variable (f : ℝ → ℝ) (x : ℝ)
example : (<∂ f x) = (f x, fun dy => adjoint ℝ (∂ f x) dy) := by rfl
```
The reverse mode derivative at point `x` computes the value `f x` and a function that can compute the adjoint of the derivative.

With this definition we can write down the chain rule for reverse mode derivative
```lean
variable (f g : ℝ → ℝ) (x : ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)

example : 
  (<∂ (fun x => f (g x)) x)
  =
  let (y,dg') := <∂ g x
  let (z,df') := <∂ f y
  (z, fun dz => dg' (df' dz)) := by fun_trans
```

The crucial observation is that the derivative part of `<∂ (f∘g)` composes the derivatives of `f` and `g` in the reverse order hence the name *reverse mode*.


::: TODO

Talk about 
1. what is forward pass and reverse pass
2. memory requirements of reverse mode
3. forward mode vs reverse mode 
4. relation to vjp jvp convention
::: 


## Exercises

1. reimplement gradient descent using `revFDeriv` and use `f x` for computing the improvement

2. Generate `revFDeriv` rules for `foo`.

3. SDF projection
  - sphere
  - pick something from
    https://iquilezles.org/articles/distfunctions/


# Derivatives of Neural Network Layers

In the chapter 'Working with Arrays' we have constructured a simple neural network. To train it we have to comput its derivative

::: TODO

Differentiate neural network layers from the chapter 'Working with Arrays'

:::
