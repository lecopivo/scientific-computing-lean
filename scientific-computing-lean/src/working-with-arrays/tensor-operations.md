# Tensor Operations

*doing arithmetics on indices is a bit painful and commond practices and usefull tricks should be explained here*
*usage of `Fin n`, `ZMod n`, `Icc a b`*
*show implementation of convolution and many of its variants*

In this chapter we will demonstrate more advanced oprations with arrays like transofmations and reductions. To give a concrete example we will build simple neural network. Note that Lean/*SciLean* is not yet fit for running and training neural networks as it only runs on CPU and the current compiler does not produce the most efficient code. Neverthereless, I belive writing a simple neural network will nicely demonstrate Lean's expresivity. My secrate hope is that this text will motivate someone to write a specialized compiler that will translate subset of Lean to GPUs.


## Transformations and Reductions

Common operation is to transform every element of an array. To do that we can write a simple for loop. Let us remind that anytime you want to write an imperative style code you have to start it with `Id.run do` and to modify input `x` mutably we have to introduce a new mutable variable `x'` and assign `x` to it
```lean
def map {I : Type} [IndexType I] (x : Float^I) (f : Float → Float) := Id.run do
  let mut x' := x
  for i in IndexType.univ I do
    x'[i] := f x'[i]
  return x'
```
A new thing here is that we wrote this function polymorphic in the index type `I`. `{I : Type}` introduces a new type and `[IndexType I]` adds a requirement that `I` behave as index. `IndexType` is so called type class and it allows us to do bunch of things with `I`. We have already seen `IndexType.card I` which tells you the number of elements in `I`. There is also `IndexType.toFin` and `IndexType.fromFin` which convert `i : I` into `toFin i : Fin (card I)` and `idx : Fin (card I)` to `fromFin idx : I`. So the function `toFin` allows you to linearize any index `I` and it is the core function used to implement `DataArrayN` as all elements of an array have to be stored linearly in the memory.


In fact *SciLean* already provides this function under the name `mapMono`. The mono stands for the fact that the function `f` does not change the type, in our case it accepts and returns `Float`. Also this function is defined in the `DataArrayN` namespace and because of that we can use familiar dot notation `x.mapMono`. As `mapMono` is polymorphic in the shape of the array we can call it on vectors
```lean
#eval ⊞[1.0,2.0,3.0].mapMono (fun x => sqrt x)
```
or matrices
```lean
#eval ⊞[1.0,2.0;3.0,4.0].mapMono (fun x => sqrt x)
```
or higher rank arrays
```lean
#eval (⊞ (i j k : Fin 2) => (IndexType.toFin (i,j,k)).toFloat).mapMono (fun x => sqrt x)
```
where `IndexType.toFin (i,j,k)` turns structured index of type `Fin 2 × Fin 2 × Fin 2` to linear index of type `Fin 8`, `.toFloat` converts it to `Float` and finally `.map (fun x => sqrt x)` computes square root of every element.
Float

Alternative to `mapMono` is `mapIdxMono` which accepts function `f : I → X → X` so you can in addition use the index value to transform the array values. 
```lean
#eval (0 : Float^[3]) |>.mapIdxMono (fun i _ => i.toFloat) |>.map (fun x => sqrt x)
```
where `0 : Float^[3]` creates zero array of size 3 then `mapIdxMono (fun i _ => i.toFloat)` initializes every element to the value of its index and finally `map (fun x => sqrt x)` computes square root of every element.


Next important opeartion with tensor is reduction which runs over elements and reducess them using provided binary operation. There are two main reductions `x.fold op init` and `x.reduceD op default`. The difference is that `fold` used `init` as the initial value that is updated with elements of the array `x`. `reduceD` uses only the element of `x` and returns `default` if `x` happends to be empty
```lean
x.fold op init = (op ... (op (op init x[0]) x[1]) ...n)
x.reduceD op default = (op ... (op (op x[0] x[1]) x[2]) ...)
```
There is also versions `x.reduce` where you do not have to provide the default element but it is required that the element type `X` of the array `x : X^I` has instance `Inhabited X` which allows you to call `default : X` returning a default element of `X`. For example `default : Float` returns `0.0`.

To sum all element of an array
```lean
#eval ⊞[1.0,2.0,3.0].fold (·+·) 0
```
or to find minimal element
```lean
#eval ⊞[(1.0 :Float),2.0,3.0].reduce (min · ·)
```
notice that computing the minimal element with `fold` and `init:=0` would give you an incorrect answer.


Putting it all together we can implement soft-max
```lean
def softMax {I} [IndexType I]
  (r : Float) (x : Float^I) : Float^I := Id.run do
  let m := x.reduce (max · ·)
  let x := x.map fun x => x-m
  let x := x.map fun x => exp r*x
  let w := x.reduce (·+·)
  let x := x.map fun x => x/w
  return x
```
where for numerical stablity we first find the maximal element `m` and subtract it from all the element. After that we procees with the standard definition of soft max. Of course, this is not the most efficient implementation of softmax. In later chapter, we will show how to transform it to a more efficient version.


Very common reduction is to sum element or to multiply them. *SciLean* provides familiar notation for these
```
def x := ⊞[1.0,2.0,3.0,4.0]
def A := ⊞[1.0,2.0;3.0,4.0]

#eval ∑ i, x[i]
#eval ∏ i, x[i]
#eval ∑ i j, A[i,j]
#eval ∏ i j, A[i,j]
```

Therefore we can define commong matrix operations like matrix-vector multiplication
```lean
def matMul {n m : Nat} (A : Float^[n,m]) (x : Float^[m]) :=
  ⊞ i => ∑ j, A[i,j] * x[j]
```
or trace
```lean
def trace {n : Nat} (A : Float^[n,n]) :=
  ∑ i, A[i,i]
```

## Convolution and Operations on Indices

The fundamental operation in machine learning is convolution. The first attempt at writing convolution might look like this
```lean
def conv1d {n k : Nat} (x : Float^[n]) (w : Float^[k]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] * x[i-j]
```
However this produces error
```lean
typeclass instance problem is stuck, it is often due to metavariables
  HSub (Fin n) (Fin k) ?m.48171
```
that is saying Lean can't infer subtraction operation between the type `Fin n` and `Fin k` producing some unknown type `?m.48171`. This makes sense, what does it mean to subtracting `j : Fin k` from `i : Fin n`? Because we are accesing an elements of `x` we probably want the result to be `Fin n` but what do we do if `i -j` is smaller then zero? We need to do something more involved when doing operations on indices that have their range specified in their type.


Let's step back a bit and look at the type of the kernel `w : Float^[k]` we index it with number `0,...,k-1` but that is not how we usually think of kernels. We would rather index them by `-k,...,-1,0,1,...,k`. *SciLean* provides uselfull notation for this `Float^[[-k:k]]` which stands for `DataArrayN Float (Set.Icc (-k) k)` and `Set.Icc (-k) k` is closed interval with endpoints `-k` and `k`. Because here we consider `k` to be integer then `Set.Icc (-k) k` is exactly the set of `-k,...,-1,0,1,...,k`. Recall that `i : Fin n` is a pair of the value `i.1 : ℕ` and proof `i.2 : i.1 < n` similarly `i : Set.Icc (-k) k` is a pair `i.1 : ℤ` and proof `i.2 : -k ≤ i.1 ∧ i.1 ≤ k`. The type for two dimensinal kernel would be `Float^[[-k:k],[-k:k]]` which stands for `DataArrayN Float (Set.Icc (-k) k × Set.Icc (-k) k)`.


Now instead of writing `i-j` we want to shift the index `i : Fin n` by the index `j` and obtain another index of type `Fin n`. Let's define general function `shift` that shift `Fin n` by arbitrary integer
```lean
def Fin.shift {n} (i : Fin n) (j : ℤ) : Fin n :=
    { val := ((i.1 + j) % n ).toNat, isLt := sorry }
```
where `%` is already doing positive modulo on integers and we again omitted proof that the result is infact smaller then `n`. It is not a hard proof but the purpose of this text is not to teach you how to prove theorems in Lean rather then how to use Lean as programming language omitting proofs is perfectly valid approac.


Now we can write one dimensional convolution as
```lean
def conv1d {n k : Nat} (w : Float^[[-k:k]]) (x : Float^[n]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] * x[i.shift j.1]
```

This immediatelly generalizes to two dimensions
```lean
def conv2d {n m k : Nat} (w : Float^[[-k:k],[-k:k]]) (x : Float^[n,m]) :=
    ⊞ (i : Fin n) (j : Fin m) => ∑ a b, w[a,b] * x[i.shift a, j.shift b]
```

In practice, convolution layer takes as input a stack of images `x`, a stack of kernels `w` and bias `b`. Let's index images by an arbitrary type `I` and kernels by `J×I`.
```lean
def conv2d {n m k : Nat} (J : Type) {I : Type} [IndexType I] [IndexType J] [DecidableEq J]
    (w : Float^[J,I,[-k:k],[-k:k]]) (b : Float^[J,n,m]) (x : Float^[I,n,m]) : Float^[J,n,m] :=
    ⊞ κ (i : Fin n) (j : Fin m) => b[κ,i,j] + ∑ ii a b, w[κ,ι,a,b] * x[ι, i.shift a, j.shift b]
```
TODO: investigate why we need to provide [DecidableEq J] and why we have to give explicit types for `i` and `j`
As you can see the notation `Float^[I,n,m]` accepts arbitrary types for dimensions. Therefore `Float^[I,n,m]` is identical to `Float^[I,Fin n,Fin m]`. This is very useful when the dimensions have some meaning or structure that is used in the computation.



## Physics Example

### Ricci decomposition
```lean
variable {n : Nat}
  (R : Float^[n,n,n,n])
  (g20 : Float^[n,n])
  (g02 : Float^[n,n])

def Ricci := ⊞ (j,k) => ∑ i l, (g20[i,l] : Float) * (R[i,j,k,l] : Float)
def Curvature := ∑ j k, (g20[j,k] : Float) * (Ricci R g20)[j,k]
def RicciTraceLess := (Ricci R g20) - (Curvature R g20/n) • g02
def S := ⊞ (i,j,k,l) => (Curvature R g20/(n*(n-1))) * ((g02[i,l] : Float) * (g02[j,k] : Float) - (g02[i,k] : Float) * (g02[j,l] : Float))
def E := ⊞ (i,j,k,l) =>
  let Z := RicciTraceLess R g20 g02
  (1.0/(n-2)) *  ((Z[i,l] : Float) * (g02[j,k] : Float)
                - (Z[j,l] : Float) * (g02[i,k] : Float)
                - (Z[i,k] : Float) * (g02[j,l] : Float)
                + (Z[j,k] : Float) * (g02[i,l] : Float))
def W := R + S R g20 g02 - E R g20 g02
```
