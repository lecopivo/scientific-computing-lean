# Basic Operations

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
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0,1.0]
```
TODO: FIX ERROR MESSGE FOR THIS - RIGHT NOW IT GIVES INCOMPREHENSIBLE 
   failed to synthesize instance
     ArrayTypeNotation (DataArrayN Float (Fin 2)) (Fin 3) (typeOf 1.0)
     
TODO: Allow for `X^[*]` notation 


Let's back up and talk about the notation `Float^[n]` and how it connects to `DataArray X` we talked about previously. An array `x : Float^[n]` has length `n` and thus can be indexed with number `0..(n-1)`. The type expressing all natural numbers smaller then `n` is denoted with `Fin n`. It is defined as a structure:
```lean
structure Fin (n : Nat) where
  val  : Nat
  isLt : val < n
```
which holds the value `val` and a proof `isLt` that the value is infact smaller then `n`. 

`Float^[n]` is just a syntactic sugar for `DataArrayN Float (Fin n)` which is  `DataArray Float` together with a proof that the size of the array is `n`. In general, `Fin n` can be replaced with an arbitrary index type `I`. The definition of `DataArrayN` is:
```lean
structure DataArrayN (X : Type) (I : Type) where
  data : DataArray X
  h_size : card I = data.size
```
which is an array `data` with a proof that the array size it equal to the cardinality of the index set `I`. In the case of `I = Fin n` we have `card (Fin n) = n.`

Having the flexibility using an arbitrary type `I` as index is already sufficient to support arbitrary n-dimensional array. To get matrices we pick `I = Fin n × Fin m`. In other words matrix is just an array indexed by pair of indices `(i,j)` where `0≤i<n` and `0≤j<m`. Thus `DataArrayN Float (Fin n × Fin m)` is just a `n×m` matrix and the syntactic sugar for it is `Float^[n,m]`. We can generalize this and pick `I = Fin n₁ × ... × Fin nᵣ` which yields `r`-dimensional array with dimensions `n₁, ..., nᵣ`. The syntactic sugar for `DataArrayN Float (Fin n₁ × ... × Fin nᵣ)` is `Float^[n₁, ..., nᵣ]`.

Have a look at chapter 1.4. Structures in Functional Programming in LeanTo learn more about structures 


Let's go over the basic operations on arrays in *SciLean*. As we mentioned previously you can create `List` with `[a,b,...]` or `Array` with `#[a,b,...]`. Here we will mainly focus on `DataArray` that uses `⊞[a,b,...]` so let's create one
```lean
def u :=  ⊞[1.0, 2.0]
```
we can access its elements with bracket notation `u[i]`
```
#eval u[0]
#eval u[1]
```
Lean can leverage the index information in the type of `u` so when we write 
```
#eval ∑ i, u[i]
```
or 
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
#check A[(0,1)]
```
which might look like an odd quirk of our definition of matrix but hopeful later on you will see that this generality allows us to work with indices that have a proper meaning rather being a meaningless number.



Popular method for creating arrays in Python is list comprehension. To some capacity this can be viewed as process turning a function, `f : Idx → Elem`, into an array `DataArraN Elem Idx`. The notation is very similar to lambda notation `fun x => f x`
```
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
def outerProduct {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for i in IndexType.univ Fin n do
    for j in IndexType.univ Fin m do
      A[i,j] := x[i]*y[j]
  return A
```
We first create mutable zero matrix and then set every. The function `IndexType.univ I` creates a range that runs over all the elements of `I`. When working with matrices, one has to be careful if they are in column major or row major ordering and accordingly iterate over `i` first and then over `j`. We will explain later how this is done in *SciLean* so for now it is safe to just iterate over both indices simultaneously and we get the optimal order
```lean
def outerProduct {n m : Nat} (x : Float^[n]) (y : Float^[m]) := Id.run do
  let mut A : Float^[n,m] := 0
  for (i,j) in (IndexType.univ (Fin n × Fin m)) do
    A[i,j] := x[i]*y[j]
  return A
```

Of course the above implementation of has the drawback that it first initialized the whole matrix to zero and then go over the matrix again and set it up to the correct value. Sometimes it is much more natural to create the matrix element by element. We can create an array with dynamic size and push element one by one. Once we are done we can fix the dimensions of the matrix.
```lean
def outerProduct {n m : Float} (x : Float^[n]) (y : Float^[m]) : Float^[n,m] := Id.run do
  let mut A : DataArray Float := ⊞[]
  A := reserve A (n*m)
  for (i,j) in (IndexType.univ (Fin n × Fin m)) do
    A := A.push (x[i]*y[j])
  return { data:= A, h_size:= sorry }
```
Recall that `Float^[n,m]` is just syntax for `DataArrayN Float (Fin n × Fin m)` and `DataArrayN X I` is just a structure holding `data : DataArray X` and a proof `h_size : data.size = card I`. In this case, we provide the matrix `A` and in the second element we should provide a proof that `A.size = card (Fin n × Fin m) = n*m`. Right now, we do not want to focus on proofs to we just omit it. Deciding when to provide proofs and when to omit them is a crucial skill when writing programs in Lean. Often it is very useful to just state what your program is supposed to do. It is a an amazing tool to clarify in your head what program are you actually writing. On the other hand, providing all the proofs can be really tedious and often a waste of time if you have to reorganize you program and all your proofs are suddently invalid.
