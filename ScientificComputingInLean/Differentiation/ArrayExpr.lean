import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxHeartbeats 1000000000

open Lean.MessageSeverity
open SciLean

#doc (Manual) "Differentiating Array Expressions" =>


```lean (show:=false)
set_default_scalar Float
namespace DiffArrayExpr
variable (n m : Nat) (A : Float^[n,m])

variable
  {K : Type} [RCLike K]
  {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
  [ArrayType Cont Idx Elem] [IndexType Idx]
  [NormedAddCommGroup Elem] [AdjointSpace K Elem]
  {I : Type} [IndexType I] [DecidableEq I]
  {E : I → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace K (E i)]
  [∀ i, CompleteSpace (E i)] [StructType Elem I E] [VecStruct K Elem I E]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace K W] [CompleteSpace W]

@[fun_trans]
theorem ArrayType.ofFn.arg_f.revFDerivProj_rule_unit_simple :
    revFDerivProj K Unit (fun f : Idx → Elem => ArrayType.ofFn f)
    =
    fun f =>
      (ArrayType.ofFn (Cont:=Cont) f, fun _ (dx : Cont) i => ArrayType.get dx i) := by
  unfold revFDerivProj; fun_trans[oneHot]
```

In this chapter we will talk about differentiating array expressions like matrix multiplication
```lean
#check ∇! x : Float^[m], ⊞ i => ∑ j, A[i,j] * x[j]
```
In general, differentiationg w.r.t. an array of expression containing index access and loops.

First, we identify three main issues and then we explain SciLean's approach in dealing with them.


```lean (show:=false)
end DiffArrayExpr
```

# The Difficulty of Differentiating Array Expressions

## Sparse Update Problem

```lean (show:=false)
set_default_scalar Float
```

The main difficulty in differerentiating array expressions is to efficiently differentiate index access and update. The naive implementation of reverse mode differentiation turns every index access into one hot vector, i.e. a vector with all zeros except for the index `i` which is one.

```lean (name:=oneHotExample)
variable (x : Float^[3])
#check ∇! (x':=x), x'[0]
```
```leanOutput oneHotExample
oneHot (0, ()) 1 : Float^[3]
```
Where `oneHot (i,()) a` is a vector of zeros with `a` at index `i`.

This is a problem because creating these one hot vectors is wasteful. Ideally we would like that reverse mode differentiation turns every index access into an update operation at that index. To demonstrate the above problem consider the following example where we turn off SciLean's optimization that deals with the problem we are discussing.

```lean (keep:=false) (name:=revFDeriv_on_DataArrayN)
-- turn off optimizations
attribute [-simp_core] revFDeriv_on_DataArrayN

#check ∇! (x':=x), (x'[0] + x'[1] + x'[2])
```
```leanOutput revFDeriv_on_DataArrayN
oneHot (0, ()) 1 + oneHot (1, ()) 1 + oneHot (2, ()) 1 : Float^[3]
```

The gradient of the sum of all elements is just a vector of ones. However, the naive implementation of reverse mode differentiation creates three one hot vectors and adds them up. This is lots of wasteful computation. A better implementation is to create an arrays of zeroes and update its elements one by one. If we turn on the optimization we exactly that:

```lean (name:=revFDeriv_on_DataArrayN2)
-- turn on optimizations
attribute [simp_core ↓ high] revFDeriv_on_DataArrayN

#check ∇! (x':=x), (x'[0] + x'[1] + x'[2])
```
```leanOutput revFDeriv_on_DataArrayN2
let dx := oneHot (0, ()) 1;
let dx := ArrayType.modify dx 1 fun xi => xi + 1;
ArrayType.modify dx 2 fun xi => xi + 1 : Float^[3]
```
With optimizations we get a much more efficient implementation which initially creates a single one-hot vector and then modifies it twice with {name}`SciLean.ArrayType.modify`.

In this chapter we will explain how is this optimization done using two function transformations {name}`SciLean.revFDerivProj` and {name}`SciLean.revFDerivProjUpdate`. We will demonstrate what problems it solves and which ones are still unresolved.



## Loops and let bindings


```lean
#check ∇! x : Float^[5], IndexType.foldl (fun s (i : Fin 5) => let y := x[i]^2; s + y) 0
```

## Sparse Update Problem


```lean
variable (f g : Float^[5] → Float) (hf : Differentiable Float f)
  (hg : Differentiable Float g)
#check (revFDerivProjUpdate Float Unit (fun  (x : Float^[5]^[2]) => (f x[0] + g x[1])))
  rewrite_by
    autodiff
```


# Problematic Rewrite Rules

```lean (show:=false)
namespace ProblematicRewriteRules
variable
  {R : Type} [RCLike R]
  {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
  [ArrayType Cont Idx Elem] [IndexType Idx] [DecidableEq Idx]
  [NormedAddCommGroup Elem] [AdjointSpace R Elem] [CompleteSpace Elem]
  {I : Type} [IndexType I] [DecidableEq I]
  {E : I → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, AdjointSpace R (E i)]
  [∀ i, CompleteSpace (E i)] [StructType Elem I E] [VecStruct R Elem I E]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]
```

Let's have a look at rewrite rules for the default reverse mode automatic differentiation and point out the problems that arrise when they are applied to differentiating array expressions.


As a simple example we will try to compute `∇ (x':=x), (x[i] + x[j])` and produce `Array.modify (oneHot (i,()) 1) j (·+1)`. The first rule we have to apply is the rule for addition:
```lean (keep:=false)
theorem HAdd.hAdd.arg_a0a1.revFDeriv_rule_bad
    (f g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDeriv R fun x => f x + g x)
    =
    fun x =>
      let (y,df') := revFDeriv R f x
      let (z,dg') := revFDeriv R g x
      (y + z, fun dy => df' dy + dg' dy) := by fun_trans
```
The issue with this rule is the addition of `df' dy` and `dg' dy`. We would like to modify this rule such that for example we turn `dy` into `dx := df' dy` and then modify `dx` by reverse pass `dg'`.

To deal with this we can apply copiler optimization that replaces `X` with `X→X`. An element `x` is replaced with `fun x' => x' + x`, this has the great advantage such that zero `0 : X` is just identity function thus adding zero is zero cost. Similarly, `oneHot i 1` is replaced with `fun x' => Array.modify x' i (·+1)`.

To do this we introduce a new function transformation `revFDerivUpdate` which returns `X→X` instead of `X` in the reverse pass:
```lean(show:=false)
variable (R)
```
```lean
@[fun_trans]
noncomputable
def revFDerivUpdate (f : X → Y) (x : X) : Y × (Y→X→X) :=
  let (y,df') := revFDeriv R f x
  (y, fun dy dx => dx + df' dy)
```
```lean(show:=false)
variable {R}
```
The revised version for the addition rule is then:
```lean (keep:=false)
theorem HAdd.hAdd.arg_a0a1.revFDeriv_rule
    (f g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDeriv R fun x => f x + g x)
    =
    fun x =>
      let (y,df') := revFDeriv R f x
      let (z,dg') := revFDerivUpdate R g x
      (y + z, fun dy => dg' dy (df' dy)) := by fun_trans[revFDerivUpdate]
```
As you can see we have replaced `dg' dy + df' dy` with `dg' dy (df' dy)`. The difference is that the original rule has to create two arrays and add them up, while the new rule only creates one array and then updates it.

You can see that this rule is not symmetric in `f` and `g`. This is somewhat unfortunate and will be listed as one of the unresolved problems later on as in certain scenarios it would be beneficial to apply `revFDerivUpdate` to `f` instead of `g`.

Because we have introduced a new function transformation `revFDerviUpdate` we also need to introduce new function transformations rules for it. The addition rule is then:
```lean
theorem HAdd.hAdd.arg_a0a1.revFDerivUpdate_rule
    (f g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g) :
    (revFDerivUpdate R fun x => f x + g x)
    =
    fun x =>
      let (y,df') := revFDerivUpdate R f x
      let (z,dg') := revFDerivUpdate R g x
      (y + z, fun dy dx => dg' dy (df' dy dx)) := by
  unfold revFDerivUpdate; fun_trans[add_assoc]
```


Together with a simple rule for index excess we can now compute `∇ (x':=x), (x[i] + x[j])` and produce `Array.modify (oneHot (i,()) 1) j (·+1)`:
```lean
@[fun_trans]
theorem ArrayType.get.arg_cont.revFDeriv_rule_simple (i : Idx) :
    revFDerivUpdate R (fun x : Cont => ArrayType.get x i)
    =
    fun x =>
      (ArrayType.get x i, fun dx dx' => ArrayType.modify dx' i (·+dx)) := by
  unfold revFDerivUpdate; funext; simp; ext dx dx' i'; fun_trans
  by_cases h : i=i' <;> simp [h,oneHot]
```

```lean
@[fun_trans]
theorem ArrayType.get.arg_cont.revFDeriv_rule (i : Idx)
    (cont : W → Cont) (hf : Differentiable R cont) :
    revFDeriv R (fun w => (cont w)[i])
    =
    fun w : W =>
      let (c,dc') := revFDeriv R cont w
      (c[i], fun de => dc' (oneHot (i,()) de)) := by fun_trans
```




```lean (show:=false)
end ProblematicRewriteRules
```
