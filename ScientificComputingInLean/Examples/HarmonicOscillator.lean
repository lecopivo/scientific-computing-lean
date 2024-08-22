import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open Lean.MessageSeverity
open SciLean

set_default_scalar Float

#doc (Manual) "Harmonic Oscillator" =>

Let's demonstrate basic capabilities of SciLean on a simple program simulating harmonic oscillator. The energy/Hamiltonian of harmonic oscillator is
```lean
def H (m k : Float) (x p : Float) := (1/(2*m)) * p^2 + k/2 * x^2
```

Once we have an energy of a physical system we can derive its dynamics using Hamilton's equations
```latex
\begin{align}
\dot x &= \frac{\partial H}{\partial p} \\
\dot p &= -\frac{\partial H}{\partial x}
\end{align}
```

In SciLean, we define function `solver` that approximatelly solves these equations with the following command
```
approx solver (m k : Float)
  := odeSolve (fun (t : Float) (x,p) => ( ∇ (p':=p), H m k x  p',
                                         -∇ (x':=x), H m k x' p))
by
  ...
```
The expression after `:=` is just a specification of what the function `solver` is supposed to approximate and the actual definition is given where the dots `...` are.

The general idea behind SciLean is that we first specify what we want to compute and only then we describe how we do it. In this case, the function {lean}`odeSolve` is non-computable function that can't be executed but has well defined meaning of returning the solution of given differential equation. In the place of the dots `...` we will manipulate this function symbolically and transform the whole specification into an expression that can be evaluated approximatelly.


Let's have a look how we can turn the specification into implementation
```lean
open SciLean
approx solver (m k : Float)
  := odeSolve (fun (t : Float) (x,p) => ( ∇ (p':=p), H m k x  p',
                                         -∇ (x':=x), H m k x' p))
by
  unfold H  -- unfold definition of H
  autodiff  -- run automatic differentiation

  -- apply RK4 method
  simp_rw (config:={zeta:=false}) [odeSolve_fixed_dt rungeKutta4 sorry_proof]

  -- approximate the limit with a fixed `n`
  approx_limit n sorry_proof
```
There are two main steps in turning the specification into implementation. We need to compute the derivatives `∇ (p':=p), H m k x  p'` and `∇ (x':=x), H m k x' p` and we need to approximate the function {lean}`odeSolve` using some time stepping scheme.

To compute the derivatives, we unfold the definition of the Hamiltonian {lean}`H` and call `autodiff` tactic.

To approximate {lean}`odeSolve` we rewrite the specification using the theorem {lean}`odeSolve_fixed_dt` saying that {lean}`odeSolve` can be approximated by a time stepping scheme, we choose Runge-Kutta 4 {lean}`rungeKutta4`.

The theorem {lean}`odeSolve_fixed_dt` produces a specification of the form `limit n → ∞, ...`. We can decide to approximate this limit by taking a concrete value `n` and hope it is sufficiently large such that the approximation is good enough. To do this we call the tactic `approx_limit` and we end up with a goal that fully computable expression.

Now we have a function {lean}`solver` that takes mass `m`, stiffness `k`, number of substeps `substep`, initial time `t₀`, final time `t`, initial position `x` and momentum `p` and produces new position and momentum at time `t`.
```lean
#check fun m k substep t₀ t (x,p) => solver m k substep t₀ t (x,p)
```
If we check {lean}`solver` directly
```lean
#check solver
```
we see that its type contains {lean}`Approx ?l ?spec` where `?l` specifies what are the parameters controling the approximation and `?spec` is the specification of what is {lean}`solver` approximating.

Here is an example how to run {lean}`solver`
```lean
def sim : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 10.0

  let Δt := 0.1
  let x₀ := 1.0
  let p₀ := 0.0
  let mut t := 0
  let mut (x,p) := (x₀, p₀)

  for _ in [0:50] do

    (x, p) := solver m k substeps t (t+Δt) (x, p)
    t += Δt

    -- poor man's visualization
    for (j : Nat) in [0:20] do
      if j.toFloat < 10*(x+1.0) then
        IO.print "o"
    IO.println ""
```

When we execute it we obtain expected sinusoidal wave
```lean
#eval sim
```
