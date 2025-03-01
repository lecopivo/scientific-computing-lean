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


open Lean Parser Term in
macro "argmin" xs:funBinder* ", " b:term : term => do
  `(Function.argmin ↿fun $xs* => $b)

theorem solve_eq_argmin_norm2
    (R : Type*) [RealScalar R]
    {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
    {f : X → Y} {y : Y} (hf : HasUniqueSolution (fun x => f x = y)) :
    (solve x, f x = y) = argmin x, ‖f x - y‖₂²[R] := sorry_proof

theorem revFDeriv_eq_fwdFDeriv
    {R : Type*} [RealScalar R]
    {f : R → R} :
    (revFDeriv R f)
    =
    fun x =>
      let' (y,dy) := fwdFDeriv R f x 1
      (y, fun dy' => dy*dy') := by sorry_proof

open Optimjl

-- not sure how to define this yet
opaque Options.filter {R : Type} [RealScalar R] : Filter (Options R) := default

theorem argmin_eq_limit_optimize
    {R : Type} [RealScalar R] [ToString R]
    {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [ToString X]
    {Method : Type*} {State : outParam Type} [AbstractOptimizer Method State R X]
    (method : Method) (x₀ : X)
    {f : X → R} :
    (argmin x, f x)
    =
    limit opts ∈ Options.filter (R:=R),
      let f' := holdLet <| revFDeriv R f
      let r := optimize' {f:=f,f':=f',hf:=sorry_proof} (AbstractOptimizer.setOptions X method opts) x₀
      r.minimizer := sorry_proof


@[fun_prop]
theorem holdLet.arg_a.Differentiable_rule
  {𝕜} [RCLike 𝕜] {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
  IsContinuousLinearMap 𝕜 fun x : X => holdLet x := by simp[holdLet]; fun_prop

@[fun_prop]
theorem holdLet.arg_a1.Differentiable_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (f : X → Y) (hf : Differentiable 𝕜 f):
  Differentiable 𝕜 (holdLet f) := by simp[holdLet,hf]

@[fun_prop]
theorem holdLet.arg_a1.IsContinusousLinearMap_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (f : X → Y) (hf : IsContinuousLinearMap 𝕜 f):
  IsContinuousLinearMap 𝕜 (holdLet f) := by simp[holdLet,hf]

@[fun_trans]
theorem holdLet.arg_a1.fwdFDeriv_rule
  {𝕜} [RCLike 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (f : X → Y) :
  fwdFDeriv 𝕜 (holdLet f) = holdLet (fwdFDeriv 𝕜 f) := by rfl

@[simp, simp_core]
theorem holdLet_apply {α β : Type*} (f : α → β) (x : α) : holdLet f x = f x := rfl


#doc (Manual) "🚧 Harmonic Oscillator Optimization" =>

```lean (show := false)
namespace HarOscOpt
```

```lean
def H (m k : Float) (x p : Float) := (1/(2*m)) * p^2 + k/2 * x^2

approx solver (m T X k₀ : Float) :=
  let y := holdLet <| fun (k : Float) =>
    odeSolve (t₀ := 0) (t:=T) (x₀:=(X,0))
      (fun (t : Float) (x,p) =>
        ( ∇ (p':=p), H m k x  p',
         -∇ (x':=x), H m k x' p))
  solve k, (y k).1 = X
by
  conv =>
    -- focus on the specification
    enter[2]

    -- Unfold Hamiltonian and compute gradients
    unfold H; autodiff

    conv =>
      -- focus on solve k, (y k).1 = X
      enter[y]

      -- reformulate as minimization problem
      rw[solve_eq_argmin_norm2 Float (by sorry_proof)]

      -- approximate by gradient descrent
      rw[argmin_eq_limit_optimize (R:=Float)
          (x₀ := k₀)
          (method := (default : LBFGS Float 1))]

  -- consume limit by `Approx`
  -- approx limit is not respecting leading let binding!
  -- I thing this is because of the final apply `Approx.limit _ _`
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
#eval solver (m:=1) (T:=1) (X:=1) (k₀:=60)
        ({show_trace := true, result_trace := true},200,())
```

```lean
#eval solver (m:=1) (T:=1) (X:=1) (k₀:=60)
        ({x_abstol := 1e-16, g_abstol := 0, init_alpha := 10,
          show_trace := true, result_trace := true},200,())
```

```lean
#eval 4*π^2
```
