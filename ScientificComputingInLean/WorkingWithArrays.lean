import ScientificComputingInLean.WorkingWithArrays.BasicOperations
-- import ScientificComputingInLean.WorkingWithArrays.TensorOperations
-- import ScientificComputingInLean.WorkingWithArrays.OptimizingArrays

open Verso.Genre Manual
open Lean.MessageSeverity

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

open SciLean

variable (X : Type)

#doc (Manual) "Working with Arrays" =>

Scientific computing involves working with large amounts of data. To efficiently handle this data, we need efficient data structures. Programming languages provide a variety of data structures for this purpose. One core data structure is an array, which comes in various forms, including tuples, linked lists, C-like arrays, and multi-dimensional arrays (sometimes called tensors), which are especially important for scientific computing.

In Lean, the {lean}`Array` type can store an array of elements of any type `X`. Arrays are advantageous for their fast element access, with accessing an element `a[i]` having a complexity of `O(1)`. You can create an array in Lean using `#[1.0,2.0,3.0]` or by sequentially adding elements using {lean}`(((Array.mkEmpty 3).push 1.0 ).push 2.0).push 3.0`, where {lean}`Array.mkEmpty` allows you to specify the initial capacity of the array, and {lean}`Array.push` adds elements one by one.

Lean also supports imperative-style programming, as shown in the example below, which creates an array of Fibonacci numbers:

```lean (name:=fib1) (keep:=false)
def fibonacci (n : Nat) : Array Nat := Id.run do
    let mut fib : Array Nat := Array.mkEmpty n
    fib := fib.push 0
    fib := fib.push 1
    for i in [2:n] do
        fib := fib.push (fib[i-1]! + fib[i-2]!)
    return fib

#eval fibonacci 10
```
```leanOutput fib1 (severity := information)
#[0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
```

You can start imperative-style code blocks with `Id.run do` and it allows you to define mutable variables using `let mut a := ...`. To access previous elements of `fib`, we use the `a[i]!` variant, which allows access to the `i`-th element of `a : Array X` using a natural number `i : Nat`. It's important to ensure that `i` is within the range of `a`, as Lean will crash if it's out of bounds. For safe access, you can use `a[i]`, but in this case, `i` must be of type `Fin a.size`, which is a natural number with a proof that it's smaller than the size of `a`. There are also variants `a[i]?` and `a[i]'proof`, which we will discuss later in this chapter.


The great thing about Lean is that the above code actually mutates the array `fib`. Each call of `fib.push` in the Fibonacci function modifies the array directly. This is unlike many purely functional programming languages, where data structures are immutable, and every call to `fib.push` would create a new copy of `fib` with one extra element.


While {lean}`Array` offers the versatility of storing elements of any data type X, this flexibility comes at a performance cost at it is implemented as array of pointers. This is especially bad for scientific computing, where we often need arrays that store elements in a contiguous block of memory. *SciLean* provides {lean}`DataArray` which is an array capable of storing any type `X` with a fixed byte size. We can replace {lean}`Array` with {lean}`DataArray` in the Fibonacci function if we use {lean}`UInt64` instead of {lean}`Nat`, as {lean}`Nat` arbitrary size number and does not have a fixed byte size.
```lean (name:=fib2) (keep:=false)
def fibonacci (n : Nat) : DataArray UInt64 := Id.run do
    let mut fib : DataArray UInt64 := DataArray.mkEmpty n
    fib := fib.push 0
    fib := fib.push 1
    for i in [2:n] do
        fib := fib.push (fib[i-1]! + fib[i-2]!)
    return fib

#eval fibonacci 10
```
```leanOutput fib2 (severity := information)
⊞[0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
```

{lean}`DataArray` and its variant {lean}`DataArrayN` are the core array types for scientific computing, and this chapter will explain how to use them effectively.

In Lean, there are other array-like data structures mainly useful for general-purpose programming. One of these is the linked list, {lean}`List`. While it does not offer fast element access, it allows for easy pushing and popping of elements. It is suitable for defining recursive functions. For example, an implementation of Fibonacci numbers using `List` would look like this:

```lean (name:=fib3) (keep:=false)
def fibonacci (n : Nat) : List Nat :=
  (go n []).reverse
  where
    go (n : Nat) (l : List Nat) : List Nat :=
      match n, l with
      |   0,       l  => l
      | n+1,       [] => go n [0]
      | n+1,    x::[] => go n [1, x]
      | n+1, x::y::l  => go n ((x+y)::x::y::l)

#eval fibonacci 10
```
```leanOutput fib3 (severity := information)
[0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
```

The last data structure we will mention here is product type `Prod X Y` usually written as `X×Y`. It allows you to store elements of different types. If you have an element of a product `p : X×Y`, you can access its elements by `p.1` and `p.2`. You can chain pairs to build tuples of arbitrary size. For example, `(3.14, ("hello", 42))` has the type {lean}`Float × (String × Nat)`. Lean considers products to be right-associative, so you can omit the brackets and write {lean}`(3.14, "hello", 42)` or {lean}`Float × String × Nat`. This affects how you actually access elements of `p := (3.14, "hello", 42)`. To get the first element, you write `p.1`, but to access the second element, you have to write `p.2.1`, because `p.2` returns the second element {lean}`("hello", 42)` of the pair, and to get the second element of the original tuple `p`, you need to then get the first element of `p.2`.


{include ScientificComputingInLean.WorkingWithArrays.BasicOperations}
