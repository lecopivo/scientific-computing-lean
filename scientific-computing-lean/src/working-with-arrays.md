# Working with Arrays

*Give and overview of different data structures in Lean like `Prod`, `List`, `Array`, `DataArray` say that in this chapter we will focus on `DataArray` and alike. Also fixed size vs non-fixed size.*

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

In Lean, `Array X` can hold elements of any type `X`, but it is implemented as an array of pointers. This can be inefficient for performance, especially in scientific computing, where we often need arrays that store elements in a contiguous block of memory. To address this, Lean provides `ByteArray` and `FloatArray`, which allow efficient storage of bytes or floats. However, these are limited in their flexibility. To address the need for arrays of any type `X` with a fixed byte size, *SciLean* introduces `DataArray X`. For example, we can replace `Array` with `DataArray` in the Fibonacci function if we use `UInt64` instead of `Nat`, as `Nat` arbitrary size number and does not have a fixed byte size.

```lean
def fibonacci (n : Nat) : DataArray UInt64 := Id.run do
    let mut fib : DataArray UInt64 := Array.mkEmpty n
    fib := fib.push 0
    fib := fib.push 1
    for i in [2:n] do
        fib := fib.push (fib[i-1]! + fib[i-2]!)
    return fib
```

`DataArray X` and its variant `DataArrayN X I` are the core array types for scientific computing, and this chapter will explain how to use them effectively.

In Lean, there are other array-like data structures mainly useful for general-purpose programming. One of these is the linked list, `List X`. While it does not offer fast element access, it allows for easy pushing and popping of elements. It is suitable for defining recursive functions. For example, an implementation of Fibonacci numbers using `List` would look like this:

```lean
def fibonacci (n : Nat) (l : List Nat) : List Nat :=
  match n, l with
  |   0,       l  => l
  | n+1,       [] => fibonacci n [0]
  | n+1,    x::[] => fibonacci n [1, x]
  | n+1, x::y::l  => fibonacci n ((x+y)::x::y::l)
```

Unlike the previous data structures, a pair or product, `Prod X Y` usually written as `X×Y`, allows you to store elements of different types. If you have an element of a product `p : X×Y`, you can access its elements by `p.1` and `p.2`. You can chain pairs to build tuples of arbitrary size. For example, `(3.14, ("hello", 42))` has the type `Float × (String × Nat)`. Lean considers products to be right-associative, so you can omit the brackets and write `(3.14, "hello", 42)` or `Float × String × Nat`. This affects how you actually access elements of `p := (3.14, "hello", 42)`. To get the first element, you write `p.1`, but to access the second element, you have to write `p.2.1`, because `p.2` returns the second element `("hello", 42)` of the pair, and to get the second element of the original tuple `p`, you need to then get the first element of `p.2`.

