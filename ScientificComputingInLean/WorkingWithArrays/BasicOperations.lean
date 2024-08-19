import Verso.Genre.Manual
import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open Lean.MessageSeverity

open SciLean

#doc (Manual) "Basic Operations" =>

What distinguishes Lean from many other programming languages is that Lean is so called dependently typed programming language. This allows us to work with arrays that have their dimensions specified in their type. For example, vector dot product can be defined as
```lean
def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]
```
This function accepts the size of the array as an argument `n : Nat` and then two arrays of the same size `n`. The meaning of *dependently typed* is that the type of function argument can depend on the value of another argument. Here the type of `x` and `y` is `Float^[n]` which depends on the first argument `n`. This is really not possible in ordinary programming languages, some of them allow you to provide the dimension at compile time. In Lean this is not the case, the dimension `n` can be determined completly at runtime.

As you can see, one of the nice advantages is that we didn't have to specify the range over which we want to sum at it is automatically infered it should sum over the numbers `0..(n-1)`.

We can test the function with
```lean (name:=doteval)
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0]
```
```leanOutput doteval (severity := information)
2.000000
```
When calling a function, you have to provide only the arguments with normal braces, such as `(x y : Float^[n])`. Arguments with the curly braces `{n : Nat}` are implicit and will be infered automatically from the other arguments, from `x` and `y` in this case. Lean prevents us from providing arrays of different lenghts
```lean (name:=dotfail) (error:=true)
#eval dot ⊞[1.0,1.0] ⊞[(1.0:Float),1.0,1.0]
```
```leanOutput dotfail (severity := error)
application type mismatch
  dot ⊞[1.0, 1.0] ⊞[1.0, 1.0, 1.0]
argument
  ⊞[1.0, 1.0, 1.0]
has type
  Float^[3] : Type
but is expected to have type
  Float^[2] : Type
```

Let's back up and talk about the notation `Float^[n]` and how it connects to {lean}`DataArray` we talked about previously. An array `x : Float^[n]` has length `n` and thus can be indexed with number `0..(n-1)`. The type expressing all natural numbers smaller then `n` is denoted with `Fin n`. It is defined as a structure:
```lean (keep:=false)
namespace BasicOperations
structure Fin (n : Nat) where
  val  : Nat
  isLt : val < n
```
which holds the value `val` and a proof `isLt` that the value is infact smaller then `n`.

`Float^[n]` is just a syntactic sugar for `DataArrayN Float (Fin n)` which is {lean}`DataArray Float` together with a proof that the size of the array is `n`. In general, `Fin n` can be replaced with an arbitrary index type `I`. The definition of {lean}`DataArrayN` is:
```lean (keep:=false)
open SciLean
namespace BasicOperations
structure DataArrayN (X : Type) (I : Type) [PlainDataType X] [IndexType I] where
  data : DataArray X
  h_size : size I = data.size
```
which is an array `data` with a proof that the array size it equal to the size of the index set `I`. In the case of `I = Fin n` we have `size (Fin n) = n.`

Having the flexibility using an arbitrary type `I` as index is already sufficient to support arbitrary n-dimensional array. To get matrices we pick `I = Fin n × Fin m`. In other words matrix is just an array indexed by pair of indices `(i,j)` where `0≤i<n` and `0≤j<m`. Thus `DataArrayN Float (Fin n × Fin m)` is just a `n×m` matrix and the syntactic sugar for it is `Float^[n,m]`. We can generalize this and pick `I = Fin n₁ × ... × Fin nᵣ` which yields `r`-dimensional array with dimensions `n₁, ..., nᵣ`. The syntactic sugar for `DataArrayN Float (Fin n₁ × ... × Fin nᵣ)` is `Float^[n₁, ..., nᵣ]`.

Have a look at chapter 1.4. Structures in Functional Programming in Lean to learn more about structures


Let's go over the basic operations on arrays in **SciLean**. As we mentioned previously you can create {lean}`List` with {lean}`[1.0,2.0,3.0]` or {lean}`Array` with `#[1.0,2.0,3.0]`. Here we will mainly focus on {lean}`DataArray` that uses {lean}`⊞[1.0,2.0,3.0]` so let's create one
```lean
def u := ⊞[1.0, 2.0, 3.0]
```
we can access its elements with bracket notation `u[i]`
```lean (name:=arrayelem0)
#eval u[0]
```
```leanOutput arrayelem0
1.000000
```
```lean (name:=arrayelem1)
#eval u[1]
```
```leanOutput arrayelem1
2.000000
```
```lean (name:=arrayelem2)
#eval u[2]
```
```leanOutput arrayelem2
3.000000
```
Lean can leverage the index information in the type of `u` so we can easily sum all the elements of {lean}`u`
```lean (name:=arraysum)
#eval ∑ i, u[i]
```
```leanOutput arraysum
6.000000
```
or convert an array to a function from the index type to array values
```lean (name:=arrayfun)
#check fun i => u[i]
```
```leanOutput arrayfun
fun i => u[i] : Fin 3 → Float
```
Lean automatically infers the type of `i`

Similarly we can create a matrix
```lean
def A := ⊞[1.0, 2.0; 3.0, 4.0]
```
and we can access its elements
```lean (name:=matrixelem)
#eval A[0,1]
```
```leanOutput matrixelem
2.000000
```
Because matrix `A` is just an array indexed by `Fin 2 × Fin 2` we can also write it as
```lean (name:=matrixelem2)
#eval A[(1,0)]
```
```leanOutput matrixelem2
3.000000
```
which might look like an odd quirk of our definition of matrix but hopeful later on you will see that this generality allows us to work with indices that have a proper meaning rather being a meaningless number.



Popular method for creating arrays in Python is list comprehension. To some capacity this can be viewed as process turning a function, `f : Idx → Elem`, into an array `DataArraN Elem Idx`. The notation is very similar to lambda notation `fun x => f x`
```lean (name:=arrayoffn)
variable (f : Fin 10 → Float)
#check ⊞ i => f i
```
```leanOutput arrayoffn
⊞ i => f i : Float^[10]
```
Unlike lambda notation, array notation uncurries all of its arguments. This means that `⊞ i j => f i j` creates and matrix indexed by `(i,j)`. For example outer product of two arrays can be defines as
```lean (keep:=false)
def outerProduct {n m : Nat} (x : Float^[n]) (y : Float^[m]) : Float^[n,m] :=
  ⊞ i j => x[i]*y[j]
```
If you want an array of arrays instead of matrix you would write `⊞ i => (⊞ j => x[i]*y[j])` or `⊞ j => (⊞ i => x[i]*y[j])` depending whether you want the matrix stored as an array of rows or columns.


Another way to set up a matrix is to set its elements one by one
```lean (keep:=false)
open SciLean
def outerProduct {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for i in fullRange (Fin n) do
    for j in fullRange (Fin m) do
      A[i,j] := x[i]*y[j]
  return A
```
We first create mutable zero matrix and then set every. The function {lean}`fullRange` creates a range that runs over all the elements of `I`. When working with matrices, one has to be careful if they are in column major or row major ordering and accordingly iterate over `i` first and then over `j`. We will explain later how this is done in *SciLean* so for now it is safe to just iterate over both indices simultaneously and we get the optimal order
```lean
open SciLean
def outerProduct'' {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for (i,j) in (fullRange (Fin n × Fin m)) do
    A[i,j] := x[i]*y[j]
  return A
```

Of course the above implementation of has the drawback that it first initialized the whole matrix to zero and then go over the matrix again and set it up to the correct value. Sometimes it is much more natural to create the matrix element by element. We can create an array with dynamic size and push element one by one. Once we are done we can fix the dimensions of the matrix.
```lean (keep:=false)
open SciLean
def outerProduct {n m : Nat}
    (x : Float^[n]) (y : Float^[m]) : Float^[n,m] := Id.run do
  let mut A : DataArray Float := default
  A := A.reserve (n*m)
  for (i,j) in (fullRange (Fin n × Fin m)) do
    A := A.push (x[i]*y[j])
  return { data:= A, h_size:= sorry_proof }
```
Recall that `Float^[n,m]` is just syntax for `DataArrayN Float (Fin n × Fin m)` and `DataArrayN X I` is just a structure holding `data : DataArray X` and a proof `h_size : data.size = size I`. In this case, we provide the matrix `A` and in the second element we should provide a proof that `A.size = size (Fin n × Fin m) = n*m`. Right now, we do not want to focus on proofs to we just omit it. Deciding when to provide proofs and when to omit them is a crucial skill when writing programs in Lean. Often it is very useful to just state what your program is supposed to do. It is a an amazing tool to clarify in your head what program are you actually writing. On the other hand, providing all the proofs can be really tedious and often a waste of time if you have to reorganize your program and all your proofs are suddently invalid.


# Reshaping Arrays

Reshaping arrays is a common operation, where you may need to transform an array of one shape into another while preserving its total size. *SciLean* provides several functions for reshaping arrays, allowing you to convert arrays of arbitrary shapes into vectors, matrices, or arrays of higher rank.

```
def reshape1 (x : Float^[I]) (n : Nat)    (h : size I = n)     : Float^[n] := ...
def reshape2 (x : Float^[I]) (n m : Nat)  (h : size I = n*m)   : Float^[n,m] := ...
def reshape3 (x : Float^[I]) (n m k: Nat) (h : size I = n*m*k) : Float^[n,m,k] := ...
...
```

For example, to create a matrix, you can first create an array and then convert it to a matrix:

```lean
#check ⊞[1.0, 2.0, 3.0, 4.0].reshape (Fin 2 × Fin 2) (by decide)
```

Here, we also prove that reshaping an array of size four to a two-by-two matrix is valid by calling the tactic `decide`. This tactic works well with concrete numbers, when variables are involved, feel free to omit the proof with `sorry`.

These reshape functions are concrete instances of a general `reshape` function:
```lean
open SciLean
/--
info: SciLean.DataArrayN.reshape {α : Type} [pd : PlainDataType α] {ι : Type} [IndexType ι] (x : α^[ι]) (κ : Type)
  [IndexType κ] (hs : size κ = size ι) : α^[κ]
-/
#guard_msgs in
#check DataArrayN.reshape
```
which reshapes an array of shape `I` to an array of shape `J`. Using this function for vectors or matrices is cumbersome, as `x.reshape2 n m sorry` is just a shorthand for `x.reshape (Fin n × Fin m) sorry`.


# Exercises

1. write function that computes mean and variance
  - for data array of floats `Float^[n]` - mean should have type `Float` and variance `Float`
  - for arbitrarily shaped data `Float^[I]^[n]` - mean should have type `Float^[I]` and covariance `Float^[I,I]`
```lean
open SciLean
variable {n : Nat} {I : Type} [IndexType I] [DecidableEq I]

def mean (x : Float^[n]) : Float := (1/n.toFloat) • ∑ i, x[i]

def variance (x : Float^[n]) : Float :=
  let m := mean x
  (1/(n-1).toFloat) • ∑ i, (x[i] - m)^2

def mean' (x : Float^[I]^[n]) : Float^[I] := (1/n.toFloat) • ∑ i, x[i]
```

```lean
open SciLean
variable {n : Nat} {I : Type} [IndexType I] [DecidableEq I]

def covariance (x : Float^[I]^[n]) : Float^[I,I] :=
  let m := mean' x
  ⊞ i j => ∑ k, (x[k][i] - m[i])*(x[k][j] - m[j])

def covariance' (x : Float^[I]^[n]) : Float^[I,I] :=
  let m := mean' x
  let x := x.uncurry
  ⊞ i j => ∑ k, (x[k,i] - m[i])*(x[k,j] - m[j])

```
