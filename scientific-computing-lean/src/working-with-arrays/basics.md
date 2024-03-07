# Basic Operations

*Give and overview of how to work with arrays `Float^[n, ...,m]`*
- *getting, setting elements - known size vs unknown size*
- *constructing new arrays, from function or element by element*
- *reshaping*


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


Let's back up and talk about the notaion `Float^[n]` and how it connects to `DataArray X` we talked about previous. An array `x : Float^[n]` has length `n` and thus can be indexed with number `0..(n-1)`. The type expressing all natural numbers smaller then `n` is denoted with `Fin n`. It is defined as a structure:
```lean
structure Fin (n : Nat) where
  val  : Nat
  isLt : val < n
```
which holds the value `val` and a proof `isLt` that the value is infact smaller then `n`. 

`Float^[n]` is just a sytactic sugar for `DataArrayN Float (Fin n)` which is  `DataArray Float` together with a proof that the size of the array is `n`. In general, `Fin n` can be replaced with arbitrary index type `I`. The defintion of `DataArrayN` is:
```lean
structure DataArrayN (X : Type) (I : Type) where
  data : DataArray X
  h_size : card I = data.size
```
which is an array `data` with a proof that the array size it equal to the cardinality of the index set `I`. In the case of `I = Fin n` we have `card (Fin n) = n.`

The index type `I` can really be almost any finite type. For example, when we pick `I = Fin n × Fin m` we get an array indexed by a pair of indices `(i,j)` where `0≤i<n` and `0≤j<m`. Thus `DataArrayN Float (Fin n × Fin m)` is just a `n×m` matrix and shorthand notation for it is `Float^[n,m]`. We can generalize this and pick `I = Fin n₁ × ... × Fin nᵣ` which yields multi dimensional array of rank `r` with dimensions `n₁, ..., nᵣ`. The short hand sysntax for `DataArrayN Float (Fin n₁ × ... × Fin nᵣ)` is `Float^[n₁, ..., nᵣ]`.


## Element Access


## Array Construction


```lean
def literalArray (x : Float^[2]) : Float^[2,3] := 
  ⊞[x[0]^0, x[0]^1, x[0]^2;
    x[1]^0, x[1]^1, x[1]^2]
```


```lean
def funElements (x : Float^[n]) (m : Nat) := 
  ⊞ ((i,j) : Fin n × Fin m) => x[i]^j
```


```lean
def setElements (x : Float^[n]) (m : Nat) := Id.run do
  let mut A : Float^[n,m] := 0
  for (i,j) in (IndexType.univ (Fin n × Fin m)) do
    A[i,j] := x[i]^j
  return A
```


```lean
def setElements (x : Float^[n]) (m : Nat) := Id.run do
  let mut A : Float^[n,m] := 0
  for (i,j) in (IndexType.univ (Fin n × Fin m)) do
    A[i,j] := x[i]^j
  return A
```


```lean
def pushElements (x : Float^[n]) (m : Nat) := Id.run do
  let mut A : Float^[*] := ⊞[]
  A := reserve A (n*m)
  for (i,j) in (IndexType.univ (Fin n × Fin m)) do
    A := A.push (x[i]^j)
  return ⟨A, sorry⟩
```

