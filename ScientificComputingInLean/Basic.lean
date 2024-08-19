/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Genre.Manual
import DemoTextbook.Exts.Exercises

import Std.Data.HashMap

import SciLean

open Verso.Genre Manual
open DemoTextbook.Exts (lean)

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open Verso ArgParse Doc Elab Genre.Manual Html Code
open SubVerso.Examples.Slice
open SubVerso.Highlighting Highlighted

@[code_block_expander latex]
def latex : CodeBlockExpander
  | _args, str => do
    return #[(← `(Doc.Block.para #[Doc.Inline.text s!"$${$str}$$"]))]

open SciLean

set_default_scalar Float


#doc (Manual) "Scientific Computing in Lean" =>

%%%
authors := ["Tomáš Skřivan"]
%%%

# About

Work in progress book on using Lean 4 as a programming language for scientific computing. Also serves as reference for [SciLean](www.github.com/lecopivo/SciLean) library.

This book in its current form is a draft and is subject to change. Code might not work, explanations might be incomplete or incorrect. Procced with caution.


# Introduction


## Why Lean for Scientific Computing?

If your job involves writing scientific computing software and you're a satisfied user of Python, Julia, R, Matlab, or C/C++, the idea of using Lean, an interactive theorem prover and dependently typed programming language, might seem completely bizarre. Lean is often advertised as a tool that allows you to write programs and prove their correctness, thus completely eliminating bugs. However, the sad truth is that proving the correctness of programs is still very challenging and can feel like an unnecessary hassle. This is especially true in scientific computing, where your primary concern is often whether you've chosen the right model to describe the real world, rather than worrying about minor bugs in your program.


If you write scientific computing software, you mainly require two things from your programming language: ease of use and performance. High-level programming languages like Python, Julia, R, or Matlab are popular for their ease of use, while languages like C/C++ or Fortran are used when you need maximum performance. Julia is somewhat unique among these languages, as it addresses both of these goals. It is often referred to as "solving the two-language problem," in contrast to languages like Python, which are essentially glue code between highly optimized C libraries.


Similar to Julia, the goal of SciLean is to provide a high-level programming language that is also performant for scientific computing. Because Lean is dependently types language and interactive theorem prover it offers completely new opportunities in terms of ease of use and has the potential to reimagine how we write scientific computing software.


### The Role of Dependent Types?

The main feature of Lean is that it is dependently type language, which allows you to prove mathematical statements or the correctness of programs. While this may not seem very relevant for scientific computing but the ability to formally state what a program is supposed to do is extremely useful. As a library author, you can formally state what your library does, and as a user, you know exactly what to expect. This guarantees that different libraries can be used together without issues and makes refactoring large codebases less painful.

  In a way, this is taking typed programming languages to the next level and the difficulties shares some similarities with the types vs untyped language debate. Typed programming languages gained a bad reputation early on for being bureaucratic, requiring types to be written everywhere and this led to the popularity of untyped programming languages. However, in modern typed programming languages, this bureaucracy is mostly gone and for building and maintaining large-scale libraries, the benefits of types outweigh the downsides.

  Dependently typed languages are currently stuck in this bureaucratic stage, similar to where typed languages were in the past. The key point is that while writing proofs can be very tedious, stating properties of programs is not. The goal of *SciLean* is to provide a useful library for scientific computing with precisely defined specifications. Only once the library gains popularity and reaches a certain level of stability can we go back and truly prove its full correctness.

  The decision to use Lean over any other dependently typed language is largely due to the existence of a vast library of formalized mathematics *Mathlib*, supported by a large and enthusiastic community. Scientific software is typically math-heavy, and it can leverage *Mathlib* to precisely specify the programs we write. A notable example of this is automatic differentiation in *SciLean*, which utilizes *Mathlib*'s theorems about differentiation to provide automatic/symbolic differentiation that is guaranteed to be correct.

### Benefits of Interactivity

Lean is primarily known as an interactive theorem prover, allowing you to state mathematical statements and iteratively prove them. In your code editor, you can view the goal statement you want to prove and a list of statements you already know to be true. Lean provides a set of tactics that combine known facts to simplify the goal statement until you reach a statement that is trivially true. While this interactive proving may not be directly relevant to scientific computing, the infrastructure enabling it is quite interesting. We will demonstrate how this infrastructure allows us to build an interactive computer algebra system and an interactive compiler/optimizer, which are highly relevant to scientific computing.

Traditionally, there has been a clear divide between languages focusing on symbolic computations (like Mathematica, Maple, etc.) and numerical computation (like Python, Julia, etc.). The latter often provide libraries for symbolic computations, but there is still a clear division between symbolic code and normal code. In Lean, any piece of code can be treated symbolically, and Lean's interactivity allows you to effectively open an interactive notebook at any point where you can perform symbolic manipulations on your code and paste it back to your source code. Later, we will demonstrate how this approach can be taken to an extreme where you write programs that are purely symbolic and then turn them into executable programs through a series of symbolic manipulations.


One of the challenges with high-level programming languages is that they heavily rely on compiler optimizations to achieve performant code. However, when these automatic optimizations fail, understanding what went wrong can be quite difficult. An interesting approach to this problem is called "program scheduling", where you initially write your programs in a straightforward manner and then transform them using a series of commands to a more efficient form. A notable example of this is the domain-specific programming language *Halide*, which allows you to write high-performance image processing code in this manner.

By leveraging Lean's interactivity, we can build a similar system where you write your program in a simple way and then interactively rewrite it to a more efficient form. An additional benefit of using Lean is that you can also obtain a proof that you haven't changed the meaning of the program.


# Working with Arrays

Scientific computing involves working with large amounts of data. To efficiently handle this data, we need efficient data structures. Programming languages provide a variety of data structures for this purpose. One core data structure is an array, which comes in various forms, including tuples, linked lists, C-like arrays, and multi-dimensional arrays (sometimes called tensors), which are especially important for scientific computing.

In Lean, the `Array X` type can store an array of elements of any type `X`. Arrays are advantageous for their fast element access, with accessing an element `a[i]` having a complexity of `O(1)`. You can create an array in Lean using `#[1.0,2.0,3.0]` or by sequentially adding elements using `(((Array.mkEmpty 3).push 1.0 ).push 2.0).push 3.0`, where `Array.mkEmpty` allows you to specify the initial capacity of the array, and `Array.push` adds elements one by one.

Lean also supports imperative-style programming, as shown in the example below, which creates an array of Fibonacci numbers:

```lean
def fibonacci (n : Nat) : Array Nat := Id.run do
    let mut fib : Array Nat := Array.mkEmpty n
    fib := fib.push 0
    fib := fib.push 1
    for i in [2:n] do
        fib := fib.push (fib[i-1]! + fib[i-2]!)
    return fib
```

You can start imperative-style code blocks with `Id.run do` and it allows you to define mutable variables using `let mut a := ...`. To access previous elements of `fib`, we use the `a[i]!` variant, which allows access to the `i`-th element of `a : Array X` using a natural number `i : Nat`. It's important to ensure that `i` is within the range of `a`, as Lean will crash if it's out of bounds. For safe access, you can use `a[i]`, but in this case, `i` must be of type `Fin a.size`, which is a natural number with a proof that it's smaller than the size of `a`. There are also variants `a[i]?` and `a[i]'proof`, which we will discuss later in this chapter.


The great thing about Lean is that the above code actually mutates the array `fib`. Each call of `fib.push` in the Fibonacci function modifies the array directly. This is unlike many purely functional programming languages, where data structures are immutable, and every call to `fib.push` would create a new copy of `fib` with one extra element.


While `Array X` offers the versatility of storing elements of any data type X, this flexibility comes at a performance cost at it is implemented as array of pointers. This is especially bad for scientific computing, where we often need arrays that store elements in a contiguous block of memory. *SciLean* provides `DataArray X` which is an array capable of storing any type `X` with a fixed byte size. We can replace `Array` with `DataArray` in the Fibonacci function if we use `UInt64` instead of `Nat`, as `Nat` arbitrary size number and does not have a fixed byte size.
```lean
open SciLean
def fibonacci' (n : Nat) : DataArray UInt64 := Id.run do
    let mut fib : DataArray UInt64 := DataArray.mkEmpty n
    fib := fib.push 0
    fib := fib.push 1
    for i in [2:n] do
        fib := fib.push (fib[i-1]! + fib[i-2]!)
    return fib
```
`DataArray X` and its variant `DataArrayN X I` are the core array types for scientific computing, and this chapter will explain how to use them effectively.

In Lean, there are other array-like data structures mainly useful for general-purpose programming. One of these is the linked list, `List X`. While it does not offer fast element access, it allows for easy pushing and popping of elements. It is suitable for defining recursive functions. For example, an implementation of Fibonacci numbers using `List` would look like this:

```lean
def fibonacci'' (n : Nat) : List Nat :=
  (go n []).reverse
  where
    go (n : Nat) (l : List Nat) : List Nat :=
      match n, l with
      |   0,       l  => l
      | n+1,       [] => go n [0]
      | n+1,    x::[] => go n [1, x]
      | n+1, x::y::l  => go n ((x+y)::x::y::l)
```


```lean

#eval fibonacci 10
#eval fibonacci' 10
#eval fibonacci'' 10

```

The last data structure we will mention here is product type `Prod X Y` usually written as `X×Y`. It allows you to store elements of different types. If you have an element of a product `p : X×Y`, you can access its elements by `p.1` and `p.2`. You can chain pairs to build tuples of arbitrary size. For example, `(3.14, ("hello", 42))` has the type `Float × (String × Nat)`. Lean considers products to be right-associative, so you can omit the brackets and write `(3.14, "hello", 42)` or `Float × String × Nat`. This affects how you actually access elements of `p := (3.14, "hello", 42)`. To get the first element, you write `p.1`, but to access the second element, you have to write `p.2.1`, because `p.2` returns the second element `("hello", 42)` of the pair, and to get the second element of the original tuple `p`, you need to then get the first element of `p.2`.


## Basic Operations

What distinguishes Lean from many other programming languages is that Lean is so called dependently typed programming language. This allows us to work with arrays that have their dimensions specified in their type. For example, vector dot product can be defined as
```lean
def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]
```
This function accepts the size of the array as an argument `n : Nat` and then two arrays of the same size `n`. The meaning of *dependently typed* is that the type of function argument can depend on the value of another argument. Here the type of `x` and `y` is `Float^[n]` which depends on the first argument `n`. This is really not possible in ordinary programming languages, some of them allow you to provide the dimension at compile time. In Lean this is not the case, the dimension `n` can be determined completly at runtime.

As you can see, one of the nice advantages is that we didn't have to specify the range over which we want to sum at it is automatically infered it should sum over the numbers `0..(n-1)`.

We can test the function with
```lean
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0]
```
When calling a function, you have to provide only the arguments with normal braces, such as `(x y : Float^[n])`. Arguments with the curly braces `{n : Nat}` are implicit and will be infered automatically from the other arguments, from `x` and `y` in this case. Lean prevents us from providing arrays of different lenghts
```lean
#check_failure dot ⊞[1.0,1.0] ⊞[(1.0:Float),1.0,1.0]
```

Let's back up and talk about the notation `Float^[n]` and how it connects to `DataArray X` we talked about previously. An array `x : Float^[n]` has length `n` and thus can be indexed with number `0..(n-1)`. The type expressing all natural numbers smaller then `n` is denoted with `Fin n`. It is defined as a structure:
```lean
structure Fin' (n : Nat) where
  val  : Nat
  isLt : val < n
```
which holds the value `val` and a proof `isLt` that the value is infact smaller then `n`.

`Float^[n]` is just a syntactic sugar for `DataArrayN Float (Fin n)` which is  `DataArray Float` together with a proof that the size of the array is `n`. In general, `Fin n` can be replaced with an arbitrary index type `I`. The definition of `DataArrayN` is:
```lean
open SciLean
structure DataArrayN (X : Type) (I : Type) [PlainDataType X] [IndexType I] where
  data : DataArray X
  h_size : size I = data.size
```
which is an array `data` with a proof that the array size it equal to the cardinality of the index set `I`. In the case of `I = Fin n` we have `card (Fin n) = n.`

Having the flexibility using an arbitrary type `I` as index is already sufficient to support arbitrary n-dimensional array. To get matrices we pick `I = Fin n × Fin m`. In other words matrix is just an array indexed by pair of indices `(i,j)` where `0≤i<n` and `0≤j<m`. Thus `DataArrayN Float (Fin n × Fin m)` is just a `n×m` matrix and the syntactic sugar for it is `Float^[n,m]`. We can generalize this and pick `I = Fin n₁ × ... × Fin nᵣ` which yields `r`-dimensional array with dimensions `n₁, ..., nᵣ`. The syntactic sugar for `DataArrayN Float (Fin n₁ × ... × Fin nᵣ)` is `Float^[n₁, ..., nᵣ]`.

Have a look at chapter 1.4. Structures in Functional Programming in LeanTo learn more about structures


Let's go over the basic operations on arrays in *SciLean*. As we mentioned previously you can create `List` with `[a,b,...]` or `Array` with `#[a,b,...]`. Here we will mainly focus on `DataArray` that uses `⊞[a,b,...]` so let's create one
```lean
def u := ⊞[1.0, 2.0, 3.0]
```
we can access its elements with bracket notation `u[i]`
```
#eval u[0]
#eval u[1]
#eval u[2]
```
Lean can leverage the index information in the type of `u` so we can easily sum all the elements of `u`
```
#eval ∑ i, u[i]
```
or convert an array to a function from the index type to array values
```
#check fun i => u[i]
```
Lean automatically infers the type of `i`

Similarly we can create a matrix
```lean
def A := ⊞[1.0, 2.0; 3.0, 4.0]
```
and we can access its elements
```lean
#eval A[0,1]
```
Because matrix `A` is just an array indexed by `Fin 2 × Fin 2` we can also write it as
```lean
#eval A[(0,1)]
```
which might look like an odd quirk of our definition of matrix but hopeful later on you will see that this generality allows us to work with indices that have a proper meaning rather being a meaningless number.



Popular method for creating arrays in Python is list comprehension. To some capacity this can be viewed as process turning a function, `f : Idx → Elem`, into an array `DataArraN Elem Idx`. The notation is very similar to lambda notation `fun x => f x`
```lean
variable (f : Fin 10 → Float)
#check ⊞ i => f i
```
Unlike lambda notation, array notation uncurries all of its arguments. This means that `⊞ i j => f i j` creates and matrix indexed by `(i,j)`. For example outer product of two arrays can be defines as
```lean
def outerProduct {n m : Nat} (x : Float^[n]) (y : Float^[m]) : Float^[n,m] :=
  ⊞ i j => x[i]*y[j]
```
If you want an array of arrays instead of matrix you would write `⊞ i => (⊞ j => x[i]*y[j])` or `⊞ j => (⊞ i => x[i]*y[j])` depending whether you want the matrix stored as an array of rows or columns.

Currently this notation does not allow you to do any advanced features like filtering the elements based on some property. If you have a good idea how this should work please submit a proposal.


Another way to set up a matrix is to set its elements one by one
```lean
open SciLean
def outerProduct' {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for i in fullRange (Fin n) do
    for j in fullRange (Fin m) do
      A[i,j] := x[i]*y[j]
  return A
```
We first create mutable zero matrix and then set every. The function `IndexType.univ I` creates a range that runs over all the elements of `I`. When working with matrices, one has to be careful if they are in column major or row major ordering and accordingly iterate over `i` first and then over `j`. We will explain later how this is done in *SciLean* so for now it is safe to just iterate over both indices simultaneously and we get the optimal order
```lean
open SciLean
def outerProduct'' {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for (i,j) in (fullRange (Fin n × Fin m)) do
    A[i,j] := x[i]*y[j]
  return A
```

Of course the above implementation of has the drawback that it first initialized the whole matrix to zero and then go over the matrix again and set it up to the correct value. Sometimes it is much more natural to create the matrix element by element. We can create an array with dynamic size and push element one by one. Once we are done we can fix the dimensions of the matrix.
```lean
open SciLean
def outerProduct''' {n m : Nat} (x : Float^[n]) (y : Float^[m]) : Float^[n,m] := Id.run do
  let mut A : DataArray Float := default
  A := A.reserve (n*m)
  for (i,j) in (fullRange (Fin n × Fin m)) do
    A := A.push (x[i]*y[j])
  return { data:= A, h_size:= sorry_proof }
```
Recall that `Float^[n,m]` is just syntax for `DataArrayN Float (Fin n × Fin m)` and `DataArrayN X I` is just a structure holding `data : DataArray X` and a proof `h_size : data.size = card I`. In this case, we provide the matrix `A` and in the second element we should provide a proof that `A.size = card (Fin n × Fin m) = n*m`. Right now, we do not want to focus on proofs to we just omit it. Deciding when to provide proofs and when to omit them is a crucial skill when writing programs in Lean. Often it is very useful to just state what your program is supposed to do. It is a an amazing tool to clarify in your head what program are you actually writing. On the other hand, providing all the proofs can be really tedious and often a waste of time if you have to reorganize you program and all your proofs are suddently invalid.


### Exercises

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

### Reshaping Arrays

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


## Tensor Operations

In this chapter, we will demonstrate more advanced operations with arrays, such as transformations and reductions. To provide a concrete example, we will build a simple neural network. It's important to note that Lean/SciLean is not yet suitable for running and training neural networks, as it only runs on CPU and the current compiler does not produce the most efficient code. Nevertheless, I believe that writing a simple neural network will nicely demonstrate Lean's expressivity. My secret hope is that this text will motivate someone to write a specialized compiler that will translate a subset of Lean to GPUs.

### Transformations and Reductions

One common operation is to transform every element of an array. To do that, we can write a simple for loop. Recall that anytime you want to write imperative-style code, you have to start it with `Id.run do`, and to modify input `x` mutably, we have to introduce a new mutable variable `x'` and assign `x` to it:

```lean
open SciLean
def map {I : Type} [IndexType I] (x : Float^[I]) (f : Float → Float) := Id.run do
  let mut x' := x
  for i in fullRange I do
    x'[i] := f x'[i]
  return x'
```

A new thing here is that we wrote this function polymorphically in the index type `I`. `{I : Type}` introduces a new type, and `[IndexType I]` adds a requirement that `I` behave as an index. `IndexType` is a type class that allows us to do a bunch of things with `I`. We have already seen `IndexType.card I`, which tells you the number of elements in `I`. There is also `IndexType.toFin` and `IndexType.fromFin`, which convert `i : I` into `toFin i : Fin (card I)` and `idx : Fin (card I)` to `fromFin idx : I`. So the function `toFin` allows you to linearize any index `I`, and it is the core function used to implement `DataArrayN`, as all elements of an array have to be stored linearly in memory.

In fact, SciLean already provides this function under the name `mapMono`. The "mono" stands for the fact that the function `f` does not change the type; in our case, it accepts and returns `Float`. Also, this function is defined in the `DataArrayN` namespace, and because of that, we can use the familiar dot notation `x.mapMono`. As `mapMono` is polymorphic in the shape of the array, we can call it on vectors:

```lean
open SciLean Scalar
#eval ⊞[1.0,2.0,3.0].mapMono (fun x => sqrt x)
```

or matrices:

```lean
open SciLean Scalar
#eval ⊞[1.0,2.0;3.0,4.0].mapMono (fun x => sqrt x)
```

or higher-rank arrays:

```lean
open SciLean Scalar
#eval (⊞ (i j : Fin 2) => (IndexType.toFin (i,j)).1.toFloat).mapMono (fun x => sqrt x)
```

where `IndexType.toFin (i,j,k)` turns a structured index of type `Fin 2 × Fin 2 × Fin 2` to a linear index of type `Fin 8`, `.toFloat` converts it to `Float`, and finally `.map (fun x => sqrt x)` computes the square root of every element.

An alternative to `mapMono` is `mapIdxMono`, which accepts a function `f : I → X → X`, so you can additionally use the index value to transform the array values:

```lean
open SciLean Scalar
#eval (0 : Float^[3]) |>.mapIdxMono (fun i _ => i.1.toFloat) |>.mapMono (fun x => sqrt x)
```

where `0 : Float^[3]` creates a zero array of size 3, then `mapIdxMono (fun i _ => i.toFloat)` initializes every element to the value of its index, and finally `map (fun x => sqrt x)` computes the square root of every element.

The next important operation with arrays is reduction, which runs over elements and reduces them using a provided binary operation. There are two main reductions, `x.fold op init` and `x.reduceD op default`. The difference is that `fold` uses `init` as the initial value that is updated with elements of the array `x`, while `reduceD` uses only the elements of `x` and returns `default` if `x` happens to be empty:

```
x.fold op init = (op ... (op (op init x[0]) x[1]) ...n)
x.reduceD op default = (op ... (op (op x[0] x[1]) x[2]) ...)
```

There are also versions `x.reduce` where you do not have to provide the default element, but it is required that the element type `X` of the array `x : X^I` has an instance `Inhabited X`, which allows you to call `default : X`, returning a default element of `X`. For example, `default : Float` returns `0.0`.

To sum all elements of an array:

```lean
#eval ⊞[1.0,2.0,3.0].foldl (·+·) 0
```

or to find the minimal element:

```lean
#eval ⊞[1.0,2.0,3.0].reduce (min · ·)
```
notice that computing the minimal element with `fold` and `init:=0` would give you an incorrect answer.


Putting it all together we can implement soft-max
```lean
open SciLean Scalar
def softMax {I : Type} [IndexType I]
  (r : Float) (x : Float^[I]) : Float^[I] := Id.run do
  let m := x.reduce (max · ·)
  let x := x.mapMono fun x => x-m
  let x := x.mapMono fun x => exp r*x
  let w := x.reduce (·+·)
  let x := x.mapMono fun x => x/w
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

```
def conv1d {n k : Nat} (x : Float^[n]) (w : Float^[k]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] * x[i-j]
```

However, this produces an error:

```
typeclass instance problem is stuck, it is often due to metavariables
  HSub (Fin n) (Fin k) ?m.48171
```

This error arises because Lean can't infer the subtraction operation between the types `Fin n` and `Fin k`, which would produce some unknown type `?m.48171`. This makes sense, what does it mean to subtract `j : Fin k` from `i : Fin n`? Because we are accessing elements of `x`, we probably want the result to be `Fin n`, but what do we do if `i - j` is smaller than zero? We need to do something more involved when performing operations on indices that have their range specified in their type.

Let's step back a bit and look at the type of the kernel `w : Float^[k]`. We index it with numbers `0,...,k-1`, but that is not how we usually think of kernels. We would rather index them by `-k,...,-1,0,1,...,k`. SciLean provides useful notation for this: `Float^[[-k:k]]`, which stands for `DataArrayN Float (Set.Icc (-k) k)` and `Set.Icc (-k) k` is a closed interval with endpoints `-k` and `k`. Because here we consider `k` to be an integer, then `Set.Icc (-k) k` is exactly the set of `-k,...,-1,0,1,...,k`. Recall that `i : Fin n` is a pair of the value `i.1 : ℕ` and proof `i.2 : i.1 < n`. Similarly, `i : Set.Icc (-k) k` is a pair `i.1 : ℤ` and proof `i.2 : -k ≤ i.1 ∧ i.1 ≤ k`. The type for a two-dimensional kernel would be `Float^[[-k:k],[-k:k]]`, which stands for `DataArrayN Float (Set.Icc (-k) k × Set.Icc (-k) k)`.

Now, instead of writing `i-j`, we want to shift the index `i : Fin n` by the index `j` and obtain another index of type `Fin n`. Let's define a general function `shift` that shifts `Fin n` by an arbitrary integer:

```lean
def Fin.shift {n} (i : Fin n) (j : ℤ) : Fin n :=
    { val := ((Int.ofNat i.1 + j) % n ).toNat, isLt := sorry_proof }
```

Here, `%` is already performing positive modulo on integers, and we again omitted the proof that the result is indeed smaller than `n`. It is not a hard proof, but the purpose of this text is not to teach you how to prove theorems in Lean but rather how to use Lean as a programming language, and omitting proofs is a perfectly valid approach.

Now we can write one-dimensional convolution as:

```lean
def conv1d {n k : Nat} (w : Float^[[-k:k]]) (x : Float^[n]) :=
    ⊞ (i : Fin n) => ∑ j, w[j] * x[i.shift j]
```

This immediately generalizes to two dimensions:

```lean
def conv2d {n m k : Nat} (w : Float^[[-k:k],[-k:k]]) (x : Float^[n,m]) :=
    ⊞ (i : Fin n) (j : Fin m) => ∑ a b, w[a,b] * x[i.shift a, j.shift b]
```

In practice, a convolutional layer takes as input a stack of images `x`, a stack of kernels `w`, and a bias `b`. Let's index images by an arbitrary type `I` and kernels by `J×I`:

```lean
open SciLean
def conv2d' {n m : Nat} (k : Nat) (J : Type) {I : Type} [IndexType I] [IndexType J] [DecidableEq J]
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
def avgPool' (x : Float^[2*n]) : Float^[n] :=
  ⊞ (i : Fin n) =>
    let i₁ : Fin (2*n) := ⟨2*i.1, by omega⟩
    let i₂ : Fin (2*n) := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i₁] + x[i₂])
```

Unfortunately, this does not work. Lean's type checking is not smart enough to allow us to call `avgPool x` for `x : Float^[4*m]`. It can't figure out that `4*m = 2*(2*m)` and infer that `n = 2*m` when calling `avgPool`. We have to do something else.


The most flexible way of writing the `avgPool` function is as follows:

```lean
def avgPool'' (x : Float^[n]) {m} (h : m = n/2 := by infer_var) : Float^[m] :=
  ⊞ (i : Fin m) =>
    let i1 : Fin n := ⟨2*i.1, by omega⟩
    let i2 : Fin n := ⟨2*i.1+1, by omega⟩
    0.5 * (x[i1] + x[i2])
```

Here, the output dimension `m` is implicitly inferred from the proof `h : m = n/2`. Let's go step by step on what is going on.

When you call `avgPool x` for `x : Float^[4*k]`, the first argument is expected to have type `Float^[n]`. From this, Lean infers that `n = 4*k`. The next argument `{m}` is implicit, so Lean skips it for now as it is supposed to be inferred from the following arguments. Lastly, we have the argument `h : m = n/2`, which has the default value `by infer_var`. The tactic `infer_var` expects an expression with an undetermined variable, in our case `m`, and runs normalization on `n/2` and assigns the result to `m`. In this case, `4*k/2` gets simplified to `2*k`, and that is the final value of `m`.

You might be wondering what happens when `n` is odd. Because `n/2` performs natural division, for `x : Float^[2*n+1]`, calling `avgPool x` produces an array of type `Float^[n]`. If you want to prevent calling `avgPool` on arrays of odd length, you can simply modify the proof obligation to `(h : 2*m = n)`. This way, you require that `n` is even, and calling `avgPool x` with an odd-sized array `x` will produce an error.

To build a simple neural network, we need a two-dimensional version of the pooling layer:

```lean
open SciLean
variable {n₁ n₂ : Nat} {I : Type} [IndexType I] [DecidableEq I]
def avgPool2d
    (x : Float^[I,n₁,n₂]) {m₁ m₂ : Nat}
    (h₁ : m₁ = n₁/2 := by infer_var)
    (h₂ : m₂ = n₂/2 := by infer_var) : Float^[I,m₁,m₂] := sorry
  -- ⊞ (ι : I) (i : Fin m₁) (j : Fin m₂) =>
  --   let i₁ : Fin n₁ := ⟨2*i.1, by omega⟩
  --   let i₂ : Fin n₁ := ⟨2*i.1+1, by omega⟩
  --   let j₁ : Fin n₂ := ⟨2*j.1, by omega⟩
  --   let j₂ : Fin n₂ := ⟨2*j.1+1, by omega⟩
  --   0.5 * (x[ι,i₁,j₁] + x[ι,i₁,j₂] + x[ι,i₂,j₁] + x[ι,i₂,j₂])
```

### Simple Neural Network

We are almost ready to write a simple neural network. The only missing piece is the dense layer, which is just matrix multiplication followed by addition. We have already shown matrix multiplication previously, but it was only for multiplying by a normal matrix with `n` rows and `m` columns. A general dense layer takes a tensor `x` of any shape, treats it as a flat array of `m` elements, and multiplies that by an `n×m` matrix. Because our arrays allow indexing by an arbitrary type `I`, we do not need to perform this flattening explicitly and can just multiply by the matrix `Float^[n,I]`.

```lean
open SciLean
variable {I : Type} [IndexType I]
def dense (n : Nat) (A : Float^[n,I]) (b : Float^[n]) (x : Float^[I]) : Float^[n] :=
  ⊞ (i : Fin n) => b[i] + ∑ j, A[i,j] * x[j]
```

Finally, we have all the necessary pieces, and we can implement a simple neural network.

```lean
def nnet := fun (w₁,b₁,w₂,b₂,w₃,b₃) (x : Float^[28,28]) =>
  x |>.reshape (Fin 1 × Fin 28 × Fin 28) (by decide)
    |> conv2d' 1 (Fin 8) w₁ b₁
    |>.mapMono (fun x => max x 0)
    |> avgPool2d (m₁ := 14) (m₂ := 14)
    |> dense 30 w₂ b₂
    |>.mapMono (fun x => max x 0)
    |> dense 10 w₃ b₃
    -- |> softMax 0.1
```

When we check the type of `nnet`, we get:

```lean
#check nnet
```

You can see that the type of weights is automatically inferred to be:

```
Float^[8,1,[-1:1],[-1:1]] × Float^[8,28,28] × Float^[30,8,14,14] × Float^[30] × Float^[10,30] × Float^[10]
```

The input image has type `Float^[28,28]`, and the output is an array of ten elements `Float^[10]`. As you might have guessed from the dimensions, later in the book, we will train this network to classify handwritten digits from the MNIST database.


# SciLean examples

## Differentiation

```lean
open SciLean
#check (∇ (x : Float×Float), ‖x‖₂²) rewrite_by unfold fgradient; autodiff
#check (∇ (x : Float×Float), x.2) rewrite_by unfold fgradient; autodiff
```

# Exercises

This book format supports Lean examples {index subterm:="embedded Lean"}[example] and exercises.



```lean
def a : Nat := 5
def b : Nat := a + 10
```

Example theorem:

```lean
theorem five_eq_5' : a = 5 := by
  -- !! begin solution
  skip; skip
  skip
  have := True.intro
  skip; sorry
  -- !! end solution
  -- !! begin exercise
  have : "a" = "a" := by rfl
  rfl
  -- !! end exercise
```

# Using LaTeX

Inline LaTeX \\(\\int e^x \\, dx\\)

Free standing equation
$$\\int  e^x \\, dx$$

Align mode equation
\\begin\{align\}
  \\int  e^x \\, dx  \\label\{eq1\}\\tag\{1\}
\\end\{align\}
Referencing above equation Equation (\\ref\{eq1\})


LaTeX code block
```latex
\int  e^x \, dx \label{eq2}\tag{2}
```
Referencing above equation Equation (\\ref\{eq2\})
