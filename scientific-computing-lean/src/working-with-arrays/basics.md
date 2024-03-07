# Basic Operations

*Give and overview of how to work with arrays `Float^[n, ...,m]`*
- *getting, setting elements - known size vs unknown size*
- *constructing new arrays, from function or element by element*
- *reshaping*


What distinguishes Lean from many other programming languages is that Lean is so called dependently typed programming language. This allows us to work with arrays that have their dimensions specified in their type. For example, vector dot product can be defined as
```
def dot {n : Nat} (x y : Float^[n]) : Float := ∑ i, x[i] * y[i]
```
This function accepts the size of the array as an argument `n : Nat` and then two arrays of the same size `n`. The meaning of *dependently typed* is that the type of function argument can depend on the value of another argument. Here the type of `x` and `y` is `Float^[n]` which depends on the first argument `n`. This is really not possible in ordinary programming languages, some of them allow you to provide the dimension at compile time. In Lean this is not the case, the dimension `n` can be determined completly at runtime.

As you can see, one of the nice advantages is that we didn't have to specify the range over which we want to sum at it is automatically infered it should sum over the numbers `0..(n-1)`.

We can test you the function with
```
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0]
```
When calling a function, you have to provide only the arguments with normal braces, such as `(x y : Float^[n])`. Arguments with the curly braces `{n : Nat}` are implicit and will be infered automatically from the other arguments, from `x` and `y` in this case. Lean prevents us from providing arrays of different lenghts 
```
#eval dot ⊞[1.0,1.0] ⊞[1.0,1.0,1.0]
```
TODO: FIX ERROR MESSGE FOR THIS - RIGHT NOW IT GIVES INCOMPREHENSIBLE 
   failed to synthesize instance
     ArrayTypeNotation (DataArrayN Float (Fin 2)) (Fin 3) (typeOf 1.0)
     
TODO: Allow for `X^[*]` notation 








--- talk about fixed size arrays

Lean is depenently types programming language this allows us to specify array sizes in the type of an array. For example to define fixed size array we can define this structure
```
structure ArrayN (X : Type) (n : Nat) where
    data : Array X
    h_size : data.size = n
```
Which is just a pair of an array `data : Array X` together with a proof that the size of `data` is `n`. Using this we can for example implement dot product function
```
def dot {n : Nat} (x y : ArrayN Float n) : Float := ∑ i, x[i] * y[i]
```
and we do not need to check that `x` and `y` are of the same size because the compiler will prevent us from calling such function on arrays of different lengths.

