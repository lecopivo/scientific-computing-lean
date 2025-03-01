import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxHeartbeats 1000000000
set_option maxRecDepth 5000

open Lean.MessageSeverity
open SciLean

set_default_scalar Float

theorem revFDeriv_eq_fwdFDeriv
    {R : Type*} [RealScalar R]
    {f : R → R} :
    (revFDeriv R f)
    =
    fun x =>
      let' (y,dy) := fwdFDeriv R f x 1
      (y, fun dy' => dy*dy') := by sorry_proof

open Optimjl

#doc (Manual) "🚧 Harmonic Oscillator Optimization" =>

```lean (show := false)
namespace HarOscOpt
```

# Problem Statement

In this example, we will demonstrate how to find a parameter of differential equation such that the solution satisfies particular property. Consider this practical problem. We are designing a new musical instrument, we have already decided on its particular shape. We want to hit a particular note and we will do that by finding the right material. To do this we model the musical instrument with harmonic oscillator and we will find the right stifness value that gives us solution with desired frequency.

Of course that in reality we would optimize for the shape rather than for the material but this would yield much harder mathematical problem. Therefore we do it the other way around which is much easier, serves as demonstration on how to use SciLean and we can easily check the numrical answer to the analytical solution.


The harmonic oscillator is governed by the following differential equation
```latex
m \ddot x = - k x
```
because we will try to find the appropricate `k` we will denote \\(x(k,t)\\) the solution of this equation as a function of time \\(t\\) and stiffness \\(k\\).

How can we express the requirement that the solution should hit a particular frequencty \\(\omega\\)? One way to state this requirement is that the solution should return to the same position after time \\(T\\). We want to find stiffness \\(k\\) such that
```latex
x(k,T) = x(k,0)
```
where the time \\(T\\) is related to the given frequency by
```latex
T = \frac{2 \pi}{\omega}
```

(You might have noticed that this argument contains a flaw which we kindly ask you to ignore for the moment as we will discuss it at the end.)


# Lean Specification

Lets formulate this in Lean now. In the previous example 'Harmonic Oscillator' we have shows how to specify harmonic oscillator using its energy
```lean
def H (m k x p : Float) := (1/(2*m)) * p^2 + k/2 * x^2
```
The solution of the corresponding differential equation is symbolically represented using the function {name}`odeSolve`
```lean
noncomputable
def solution (m k x₀ p₀ t : Float) : Float×Float :=
  odeSolve (t₀ := 0) (x₀ := (x₀,p₀)) (t := t)
    (fun (t : Float) (x,p) =>
        ( ∇ (p':=p), H m k x  p',
         -∇ (x':=x), H m k x' p))
```
The expression `solution m k x₀ p₀ t` is the position and momentum at time `t` of harmonic oscillator with mass `m`, stiffness `k` starting at time `0` at position `x₀` and momentum `p₀`.

Notice that we had to mark the function {name}`solution` with `noncomputable` as it is purely symbolic as it can't be executed because it uses the function {name}`odeSolve`.

To express that we are looking for the stiffness satisfying a particular property we can use the notation `solve x, f x = 0` which will symbolically return the solution `x` of the equation `f x = 0`.
```lean
noncomputable
def optimalStiffness (m x₀ ω : Float) : Float :=
  let x := fun k t =>
    let (x,p) := solution m k x₀ 0 t
    x
  let T := 2*π/ω
  solve k, x k T = x k 0
```
The notation `solve x, f x = 0` uses the noncomputable function {name}`solveFun` which returns a term that satisfies a particular property. This is why we have to mark {name}`optimalStiffness` as noncomputable.

Our goal is to have an executable function that can approximatelly compute the symbolic function {name}`optimalStiffness`.

We can therefore define function `findStiffness` that is an approximation to the specification. In the next section we will show how replace `skip` with a sequence of tactics that will turn the specification into executable approximation and allows us to remove the `noncomputable` annotation from this fuction.
```lean (keep:=false)
noncomputable
approx findStiffness (m x₀ ω : Float) :=
  let T := 2*π/ω
  let y := fun (k : Float) =>
    odeSolve (t₀ := 0) (t:=T) (x₀:=(x₀,0))
      (fun (t : Float) (x,p) =>
        ( ∇ (p':=p), H m k x  p',
         -∇ (x':=x), H m k x' p))
  solve k, (y k).1 = x₀
by
  skip
```

# Turning Specification into Implementation


Unfortunatelly the current documentation tool we are using does not allow mixing a proof with text so we have to write down everything with only brief comments and only then we will go over each tactic and explain what it does.

The are two little differences in the initial specification that are mainly of technical nature. First, we had to add the function {name}`holdLet` which is just an identity function and should be ignored. Its purpose is to prevent inlining of `y` by the tactic `autodiff`. The se

Please go ahead and have a brief look at every step. The short comments should give you rought idea what each tactic is doing and by clicking on each command will display the current state.

```lean
approx findStiffness (m x₀ ω k₀ : Float) :=
  let T := 2*π/ω
  let y := holdLet <| fun (k : Float) =>
    odeSolve (t₀ := 0) (t:=T) (x₀:=(x₀,0))
      (fun (t : Float) (x,p) =>
        ( ∇ (p':=p), H m k x  p',
         -∇ (x':=x), H m k x' p))
  solve k, (y k).1 = x₀
by
  conv =>
    -- focus on the specification
    enter[2]

    -- Unfold Hamiltonian and compute gradients
    unfold H; autodiff

    conv =>
      -- focus on solve k, (y k).1 = x₀
      enter[T,y]

      -- reformulate as minimization problem
      rw[solve_eq_argmin_norm2 Float (by sorry_proof)]

      -- approximate by gradient descrent
      rw[argmin_eq_limit_optimize (R:=Float)
          (x₀ := k₀)
          (method := (default : LBFGS Float 1))]

  -- consume limit by `Approx`
  approx_limit opts sorry_proof

  conv =>
    -- focus on the specification again
    enter[2]

    -- rewrite reverse mode AD (<∂) as forward mode AD (∂>)
    -- this is possible because we are differentiating scalar function `Float → Float`
    simp -zeta only [revFDeriv_eq_fwdFDeriv]

    -- run forward mode AD
    -- this will formulate a new ODE that solves for `x`, `p`, `dx/dk` and `dp/dk`
    autodiff

  -- approximate both ODEs with RK4
  simp -zeta only [odeSolve_fixed_dt rungeKutta4 sorry_proof]

  -- choose the same number of steps for both ODE solvers
  -- and consume the corresponding limin in `Approx`
  approx_limit steps sorry_proof
```

```lean
#eval (2*π)^2
```

```lean
#eval findStiffness (m:=1) (ω:=2*π) (x₀:=1) (k₀:=10)
        ({x_abstol := 1e-16, g_abstol := 0, show_trace := true, result_trace := true},200,())
```

```lean
#eval 4*π^2
```
