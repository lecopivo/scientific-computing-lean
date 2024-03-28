# Tensor Operations

In this chapter, we will demonstrate more advanced operations with arrays, such as transformations and reductions. To provide a concrete example, we will build a simple neural network. It's important to note that Lean/SciLean is not yet suitable for running and training neural networks, as it only runs on CPU and the current compiler does not produce the most efficient code. Nevertheless, I believe that writing a simple neural network will nicely demonstrate Lean's expressivity. My secret hope is that this text will motivate someone to write a specialized compiler that will translate a subset of Lean to GPUs.

## Transformations and Reductions

One common operation is to transform every element of an array. To do that, we can write a simple for loop. Recall that anytime you want to write imperative-style code, you have to start it with `Id.run do`, and to modify input `x` mutably, we have to introduce a new mutable variable `x'` and assign `x` to it:

```lean
def map {I : Type} [IndexType I] (x : Float^I) (f : Float → Float) := Id.run do
  let mut x' := x
  for i in IndexType.univ I do
    x'[i] := f x'[i]
  return x'
```

A new thing here is that we wrote this function polymorphically in the index type `I`. `{I : Type}` introduces a new type, and `[IndexType I]` adds a requirement that `I` behave as an index. `IndexType` is a type class that allows us to do a bunch of things with `I`. We have already seen `IndexType.card I`, which tells you the number of elements in `I`. There is also `IndexType.toFin` and `IndexType.fromFin`, which convert `i : I` into `toFin i : Fin (card I)` and `idx : Fin (card I)` to `fromFin idx : I`. So the function `toFin` allows you to linearize any index `I`, and it is the core function used to implement `DataArrayN`, as all elements of an array have to be stored linearly in memory.

In fact, SciLean already provides this function under the name `mapMono`. The "mono" stands for the fact that the function `f` does not change the type; in our case, it accepts and returns `Float`. Also, this function is defined in the `DataArrayN` namespace, and because of that, we can use the familiar dot notation `x.mapMono`. As `mapMono` is polymorphic in the shape of the array, we can call it on vectors:

```lean
#eval ⊞[1.0,2.0,3.0].mapMono (fun x => sqrt x)
```

or matrices:

```lean
#eval ⊞[1.0,2.0;3.0,4.0].mapMono (fun x => sqrt x)
```

or higher-rank arrays:

```lean
#eval (⊞ (i j k : Fin 2) => (IndexType.toFin (i,j,k)).toFloat).mapMono (fun x => sqrt x)
```

where `IndexType.toFin (i,j,k)` turns a structured index of type `Fin 2 × Fin 2 × Fin 2` to a linear index of type `Fin 8`, `.toFloat` converts it to `Float`, and finally `.map (fun x => sqrt x)` computes the square root of every element.

An alternative to `mapMono` is `mapIdxMono`, which accepts a function `f : I → X → X`, so you can additionally use the index value to transform the array values:

```lean
#eval (0 : Float^[3]) |>.mapIdxMono (fun i _ => i.toFloat) |>.map (fun x => sqrt x)
```

where `0 : Float^[3]` creates a zero array of size 3, then `mapIdxMono (fun i _ => i.toFloat)` initializes every element to the value of its index, and finally `map (fun x => sqrt x)` computes the square root of every element.

The next important operation with arrays is reduction, which runs over elements and reduces them using a provided binary operation. There are two main reductions, `x.fold op init` and `x.reduceD op default`. The difference is that `fold` uses `init` as the initial value that is updated with elements of the array `x`, while `reduceD` uses only the elements of `x` and returns `default` if `x` happens to be empty:

```lean
x.fold op init = (op ... (op (op init x[0]) x[1]) ...n)
x.reduceD op default = (op ... (op (op x[0] x[1]) x[2]) ...)
```

There are also versions `x.reduce` where you do not have to provide the default element, but it is required that the element type `X` of the array `x : X^I` has an instance `Inhabited X`, which allows you to call `default : X`, returning a default element of `X`. For example, `default : Float` returns `0.0`.

To sum all elements of an array:

```lean
#eval ⊞[1.0,2.0,3.0].fold (·+·) 0
```

or to find the minimal element:

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
*Note for Mathlib users: For performance reasons SciLean defines sums and products with `IndexType` instead of `Finset`. Therefore this notation is different from the one defined in `BigOperators` namespace.*

We can define commong matrix operations like matrix-vector multiplication
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


The fundamental operation in machine learning is convolution. The first attempt at writing convolution might look like this:

```lean
def conv1d {n k : Nat} (x : Float^[n]) (w : Float^[k]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] * x[i-j]
```

However, this produces an error:

```lean
typeclass instance problem is stuck, it is often due to metavariables
  HSub (Fin n) (Fin k) ?m.48171
```

This error arises because Lean can't infer the subtraction operation between the types `Fin n` and `Fin k`, which would produce some unknown type `?m.48171`. This makes sense, what does it mean to subtract `j : Fin k` from `i : Fin n`? Because we are accessing elements of `x`, we probably want the result to be `Fin n`, but what do we do if `i - j` is smaller than zero? We need to do something more involved when performing operations on indices that have their range specified in their type.

Let's step back a bit and look at the type of the kernel `w : Float^[k]`. We index it with numbers `0,...,k-1`, but that is not how we usually think of kernels. We would rather index them by `-k,...,-1,0,1,...,k`. SciLean provides useful notation for this: `Float^[[-k:k]]`, which stands for `DataArrayN Float (Set.Icc (-k) k)` and `Set.Icc (-k) k` is a closed interval with endpoints `-k` and `k`. Because here we consider `k` to be an integer, then `Set.Icc (-k) k` is exactly the set of `-k,...,-1,0,1,...,k`. Recall that `i : Fin n` is a pair of the value `i.1 : ℕ` and proof `i.2 : i.1 < n`. Similarly, `i : Set.Icc (-k) k` is a pair `i.1 : ℤ` and proof `i.2 : -k ≤ i.1 ∧ i.1 ≤ k`. The type for a two-dimensional kernel would be `Float^[[-k:k],[-k:k]]`, which stands for `DataArrayN Float (Set.Icc (-k) k × Set.Icc (-k) k)`.

Now, instead of writing `i-j`, we want to shift the index `i : Fin n` by the index `j` and obtain another index of type `Fin n`. Let's define a general function `shift` that shifts `Fin n` by an arbitrary integer:

```lean
def Fin.shift {n} (i : Fin n) (j : ℤ) : Fin n :=
    { val := ((i.1 + j) % n ).toNat, isLt := sorry }
```

Here, `%` is already performing positive modulo on integers, and we again omitted the proof that the result is indeed smaller than `n`. It is not a hard proof, but the purpose of this text is not to teach you how to prove theorems in Lean but rather how to use Lean as a programming language, and omitting proofs is a perfectly valid approach.

Now we can write one-dimensional convolution as:

```lean
def conv1d {n k : Nat} (w : Float^[[-k:k]]) (x : Float^[n]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] * x[i.shift j.1]
```

This immediately generalizes to two dimensions:

```lean
def conv2d {n m k : Nat} (w : Float^[[-k:k],[-k:k]]) (x : Float^[n,m]) :=
    ⊞ (i : Fin n) (j : Fin m) => ∑ a b, w[a,b] * x[i.shift a, j.shift b]
```

In practice, a convolutional layer takes as input a stack of images `x`, a stack of kernels `w`, and a bias `b`. Let's index images by an arbitrary type `I` and kernels by `J×I`:

```lean
def conv2d {n m k : Nat} (J : Type) {I : Type} [IndexType I] [IndexType J] [DecidableEq J]
    (w : Float^[J,I,[-k:k],[-k:k]]) (b : Float^[J,n,m]) (x : Float^[I,n,m]) : Float^[J,n,m] :=
    ⊞ κ (i : Fin n) (j : Fin m) => b[κ,i,j] + ∑ ι a b, w[κ,ι,a,b] * x[ι, i.shift a, j.shift b]
```

## Pooling and Difficulties with Dependent Types

The next piece of neural networks is the pooling layer, a layer that reduces image resolution. Giving a good type to the pooling layer is quite challenging, as we have to divide the image resolution by two. Doing any kinds of operations in types brings out all the complexities of dependent type theory. Yes, dependent types can be really hard, but please do not get discouraged by this section. One has to be careful and not put dependent types everywhere, but when used with care, they can provide lots of benefits without causing too many troubles.

The canonical example is if you have an index `i : Fin (n + m)` and you have a function `f : Fin (m + n) → Float`, you can't simply call `f i` as `Fin (n + m)` is not *obviously* equal to `Fin (m + n)` because we need to invoke commutativity of addition on natural numbers. We will explain how to deal with this later; for now, let's have a look at the pooling layer.

Let's start with one dimension. A function that reduces the array size by two by taking the average of `x[2*i]` and `x[2*i+1]` is:

```lean
def avgPool (x : Float^[n]) : Float^[n/2] := 
  ⊞ (i : Fin (n/2)) =>
    let i₁ : Fin n := ⟨2*i.1, by omega⟩
    let i₂ : Fin n := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i₁] + x[i₂])
```

Given the index of the new array `i : Fin (n/2)`, we need to produce indices `2*i.1` and `2*i.1+1` of the old vector, which have type `Fin n`. Recall that `Fin n` is just a pair of natural numbers and a proof that it is smaller than `n`. So far, we always omitted the proof with `sorry`, but we do not have to. Here, the proof can be easily done by calling the tactic `omega`, which is very good at proving index bounds. However, remember when you are writing a program, it is usually a good strategy to inspect all proofs, see if they are plausible, and omit them with `sorry`. Only once your program is capable of running, you can go back and start filling out the proofs. You can see this as an alternative way of debugging your program.

Beware! `Fin n` is endowed with modular arithmetic. Naively calling `2*i` would multiply `i` by two and perform modulo by `n/2`. We do not want that; we have to get the underlying natural number `i.1` and multiply then by two. For example:

```lean
def i : Fin 10 := 6

#eval 2*i
#eval 2*i.1
```

One downside of the `avgPool` as written above is that if we call it multiple times, we get an array with an ugly type. For example, `avgPool (avgPool x)` has type `Float^[n/2/2]`. If we have a size that we already know is divisible by four, the `n/2/2` does not reduce. For `x : Float^[4*n]`, the term `avgPool (avgPool x)` has type `Float^[4*n/2/2]` and not `Float^[n]`.

You might attempt to solve this by writing the type of `avgPool` as:

```lean
def avgPool (x : Float^[2*n]) : Float^[n] :=
  ⊞ (i : Fin n) =>
    let i₁ : Fin (2*n) := ⟨2*i.1, by omega⟩
    let i₂ : Fin (2*n) := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i₁] + x[i₂])
```

Unfortunately, this does not work. Lean's type checking is not smart enough to allow us to call `avgPool x` for `x : Float^[4*m]`. It can't figure out that `4*m = 2*(2*m)` and infer that `n = 2*m` when calling `avgPool`. We have to do something else.


The most flexible way of writing the `avgPool` function is as follows:

```lean
def avgPool (x : Float^[n]) {m} (h : m = n/2 := by deduce_by norm_num) : Float^[m] :=
  ⊞ (i : Fin m) =>
    let i1 : Fin n := ⟨2*i.1, by omega⟩
    let i2 : Fin n := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i1] + x[i2])
```

Here, the output dimension `m` is implicitly inferred from the proof `h : m = n/2`. Let's go step by step on what is going on.

When you call `avgPool x` for `x : Float^[4*k]`, the first argument is expected to have type `Float^[n]`. From this, Lean infers that `n = 4*k`. The next argument `{m}` is implicit, so Lean skips it for now as it is supposed to be inferred from the following arguments. Lastly, we have the argument `h : m = n/2`, which has the default value `by deduce_by norm_num`. This means, please run the tactic `deduce_by norm_num` to infer this argument. The tactic `deduce_by` expects an expression with an undetermined variable, in our case `m`, and runs `norm_num` on `n/2` and assigns the result to `m`. In this case, `4*k/2` gets simplified to `2*k`, and that is the final value of `m`.

You might be wondering what happens when `n` is odd. Because `n/2` performs natural division, for `x : Float^[2*n+1]`, calling `avgPool x` produces an array of type `Float^[n]`. If you want to prevent calling `avgPool` on arrays of odd length, you can simply modify the proof obligation to `(h : 2*m = n)`. This way, you require that `n` is even, and calling `avgPool x` with an odd-sized array `x` will produce an error.

To build a simple neural network, we need a two-dimensional version of the pooling layer:

```lean
def avgPool2d
    (x : Float^[I,n₁,n₂]) {m₁ m₂}
    (h₁ : m₁ = n₁/2 := by deduce_by norm_num)
    (h₂ : m₂ = n₂/2 := by deduce_by norm_num) : Float^[I,m₁,m₂] :=
  ⊞ (ι : I) (i : Fin m₁) (j : Fin m₂) =>
    let i₁ : Fin n₁ := ⟨2*i.1, by omega⟩
    let i₂ : Fin n₁ := ⟨2*i.1+1, by omega⟩
    let j₁ : Fin n₂ := ⟨2*j.1, by omega⟩
    let j₂ : Fin n₂ := ⟨2*j.1+1, by omega⟩
    0.5 * (x[ι,i₁,j₁] + x[ι,i₁,j₂] + x[ι,i₂,j₁] + x[ι,i₂,j₂])
```

## Simple Neural Network

We are almost ready to write a simple neural network. The only missing piece is the dense layer, which is just matrix multiplication followed by addition. We have already shown matrix multiplication previously, but it was only for multiplying by a normal matrix with `n` rows and `m` columns. A general dense layer takes a tensor `x` of any shape, treats it as a flat array of `m` elements, and multiplies that by an `n×m` matrix. Because our arrays allow indexing by an arbitrary type `I`, we do not need to perform this flattening explicitly and can just multiply by the matrix `Float^[n,I]`.

```lean
def dense (n : Nat) (A : Float^[n,I]) (b : Float^[n]) (x : Float^[I]) : Float^[n] :=
  ⊞ (i : Fin n) => b[i] + ∑ j, A[i,j] * x[j]
```

Finally, we have all the necessary pieces, and we can implement a simple neural network.

```lean
def nnet := fun (w₁,b₁,w₂,b₂,w₃,b₃) (x : Float^[28,28]) =>
  x |> resize3 1 28 28 (by decide)
    |> conv2d 1 (Fin 8) w₁ b₁ 
    |>.mapMono (fun x => max x 0)
    |> avgPool2d
    |> dense 30 w₂ b₂ -- deduce_by does not play well :(
    |>.mapMono (fun x => max x 0)
    |> dense 10 w₃ b₃
    |> softMax 0.1
```

When we check the type of `nnet`, we get:

```lean
Float^[8,1,[-1:1],[-1:1]] × Float^[8,28,28] × Float^[30,8,14,14] × Float^[30] × Float^[10,30] × Float^[10] → Float^[28,28] → Float^[10]
```

You can see that the type of weights is automatically inferred to be:

```lean
Float^[8,1,[-1:1],[-1:1]] × Float^[8,28,28] × Float^[30,8,14,14] × Float^[30] × Float^[10,30] × Float^[10]
```

The input image has type `Float^[28,28]`, and the output is an array of ten elements `Float^[10]`. As you might have guessed from the dimensions, later in the book, we will train this network to classify handwritten digits from the MNIST database.
