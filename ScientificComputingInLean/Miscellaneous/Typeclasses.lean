import SciLean
import ScientificComputingInLean.Meta

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000000

open SciLean

#doc (Manual) "Typeclasses as Interfaces and Function Overloading" =>

Typeclasses in Lean bring together multiple concepts from other programming languages, notably function overloading and interfaces. In this section, we will focus on how to use typeclasses in Lean and how they relate to these familiar programming paradigms. For a deeper explanation of typeclasses we refer the reader to [Overloading and Type Classes in FPiL](https://lean-lang.org/functional_programming_in_lean/type-classes.html)


# Function overloading

```lean (show:=false)
namespace Overloading
```

In many programming languages, function overloading allows the same function name to have different implementations depending on the types of its arguments. This is sometimes called **ad-hoc polymorphism**, where the behavior of a function adapts based on the types of its inputs.

In Lean, function overloading is achieved through typeclasses. A simple example is defining a `size` function that works on different types:

```lean
class Size (A : Type) where
  size : A -> Nat
```

This defines a function `size` for any type `A`, as long as there’s an instance of `Size` for that type. We can define an instance of `Size` for lists, where the size of a list corresponds to its length:

```lean
instance {A : Type} : Size (List A) where
  size l := l.length
```

For strings, `size` can return the length of the string:

```lean
instance : Size String where
  size s := s.length
```

For the type `Unit` (which has only one value), the size can always return `0`:

```lean
instance : Size Unit where
  size _ := 0
```

With these instances, the `size` function is now overloaded and can be used with different types:

```lean
#eval Size.size [1, 2, 3]
#eval Size.size "hello"
#eval Size.size ()
```

A more complex example of function overloading is scalar multiplication, where we want to multiply elements of a type `X` by a scalar of type `R`:

```lean
class SMul (R X : Type) where
  smul : R -> X -> X

export SMul (smul)
```

The `smul` function allows us to define scalar multiplication for any pair of types `R` and `X`. The command `export SMul (smul)` exports `smul` from `SMul` namespace so we can write just `smul` instead of `SMul.smul`. Here’s how we might multiply a list of natural numbers by a scalar:

```lean
def natListSMul (n : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs => n * x :: natListSMul n xs

instance : SMul Nat (List Nat) := ⟨natListSMul⟩
```

This instance allows us to multiply a list of natural numbers by a natural number. However, we can generalize this further to work with any list of `X` where scalar multiplication between `R` and `X` is already defined:

```lean
def listSMul [SMul R X] (r : R) (l : List X) : List X :=
  match l with
  | [] => []
  | x :: xs => smul r x :: listSMul r xs

instance : SMul Nat Nat := ⟨fun x y => x * y⟩
instance [SMul R X] : SMul R (List X) := ⟨listSMul⟩
```

Now we can scalar multiply not only lists of natural numbers but also lists of any type `X` where `smul` is defined. We can even apply this recursively to lists of lists:

```lean
#eval smul 10 [1, 2]
#eval smul 10 [[1, 2], [3, 4]]
#eval smul 10 [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]
```

In these examples, `smul` is overloaded based on the types involved, allowing flexible behavior for scalar multiplication.

Previously, for `size` and `smul`, the output type was either known or closely related to the input types. A more advanced example is **matrix multiplication**, where the output type is different from any of the input types. Multiplying two matrices `A : Float^[n, m]` and `B : Float^[m, k]` results in a matrix of type `Float^[n, k]`. The output type is fully determined by the input types but is not directly one of them. We can express this relationship using an **output parameter**:

```lean
class MyMul (X Y : Type) (Z : outParam Type) where
  mymul : X -> Y -> Z

export MyMul (mymul)
```

The `outParam` keyword tells Lean’s type inference that the output type `Z` is determined by the input types `X` and `Y`. We can then define an instance for matrix multiplication:

```lean
instance : MyMul (Float^[n,m]) (Float^[m,k]) (Float^[n,k]) where
  mymul A B := ⊞ i j => ∑ l, A[i,l] * B[l,j]

#eval mymul ⊞[10.0,1;0,1000] ⊞[1.0,2;3,4]
```

Lean already comes with a variety of typeclasses for **heterogeneous operations**, such as {name}`HAdd`, {name}`HMul`, and others, which are used every time you write `+`, `*`, or similar operations. These typeclasses enable function overloading for basic operators, providing an expressive and flexible way to define operations for a variety of types.

```lean
set_option pp.notation false in
#check 2 + 3 
#eval 2 + 3 
set_option pp.notation false in
#check [1, 2, 3] ++ [4, 5, 6]
#eval [1, 2, 3] ++ [4, 5, 6]
```

By turning off notation, `set_option pp.notation false`, we can see that `+` is a syntax for {name}`HAdd.hAdd` and `++` is syntax for {name}`HAppend.hAppend`

```lean (show:=false)
end Overloading
```

## Where is the Overloaded Function Defined?

```lean (show:=false)
namespace FindOverload
```

When dealing with overloaded functions in Lean, it's important to know how to trace back to where specific implementations are defined. Overloaded functions, like `HAdd.hAdd`, have different implementations depending on the types they work with. Simply navigating to the definition of the typeclass `HAdd` will not show the specific implementations; it will only take you to the typeclass itself.

To find the exact definition of an overloaded function, you can use several techniques. Let’s explore these methods with an example.

### Finding the Definition Using `#synth`

The `#synth` command can be used to discover which instance of a typeclass is being utilized. For example, if you want to find out where negation for integers is defined, you can use:

```lean (name:=intneginst)
#synth Neg Int
```

The output of this command will show which instance of the `Neg` typeclass is being used for integers:

```leanOutput intneginst
Int.instNegInt
```

This tells us that the instance for negation on integers is {name}`Int.instNegInt`. To view the details of this instance, you can print it out:

```lean (name:=intneginst2)
#print Int.instNegInt
```

The output will provide the definition of the instance:

```
def Int.instNegInt : Neg ℤ := { neg := Int.neg } 
```

Here, {name}`Int.instNegInt` is defined as an instance of the {name}`Neg` typeclass for integers, with `neg` being implemented by the function {name}`Int.neg`. This shows how the `-` operator for integers is handled.

### Alternative Method: Using `pp.all`

Another method to locate the specific instance is by using the `pp.all` option, which allows you to see all implicit arguments in your code. This can be particularly useful for understanding which instance is applied:

```lean
set_option pp.all true in
#check fun x : Int => - x
```

The result of this command will show:

```
fun (x : Int) => @Neg.neg.{0} Int Int.instNegInt x : Int → Int
```

This output indicates that the negation operation for integers uses the instance {name}`Int.instNegInt`, showing that `Neg.neg` is applied with the specific instance for integers.

By using these techniques, you can effectively trace back from an overloaded function to its specific instance, helping you understand how different types are handled by Lean’s typeclass system.

```lean (show:=false)
end FindOverload
```

## Defining Functions "Inductively" on the Type

```lean (show:=false)
namespace InductiveOverload
```

In Lean, defining functions "inductively" on types involves creating instances for various cases of a type in order to handle arbitrary nesting and combinations of types such as lists, arrays, and products. This technique resembles mathematical induction, where we handle base cases and then generalize to more complex cases. Although Lean's `Type` is not an inductive data type, we can mimic inductive definitions by providing instances for each specific case we want to cover. This approach allows us to define flexible functions over a subset of types.

### Example: Summing Nested Structures

Let’s define a function `sum` that computes the sum of all natural numbers in an expression that can be an arbitrary combination of lists, arrays, and products. For example, we want `sum (#[1,2], [(10,20),(5,15)], 100)` to equal `163`. Here, the argument is of type `Array Nat × List (Nat × Nat) × Nat`.

First, define a typeclass `Sum` for our function:

```lean
class Sum (A : Type) where
  sum : A -> Nat

export Sum (sum)
```

#### Base Case: Natural Numbers

We start by defining the `sum` function for the base case, which is {name}`Nat`:

```lean
instance : Sum Nat where
  sum n := n
```

This instance handles the simplest case where the type is a natural number itself.

#### Inductive Step: Lists

To handle lists of natural numbers or other types, we need to define how to sum elements of lists. For this, we assume that we have a `Sum` instance for the type of list elements. Here's how we define `Sum` for lists:

```lean
instance [Sum A] : Sum (List A) where
  sum l := l.foldl (fun acc a => acc + sum a) 0
```

This instance uses `foldl` to accumulate the sum of a list by applying the `sum` function to each element and adding the results.

Now, we can compute the sum of lists of natural numbers:

```lean
#eval sum [1, 2, 3, 4] 
#eval sum [[1, 2, 3], [4]]
```

#### Inductive Step: Products

Next, we handle products of two types. To sum the elements of a product, we need `Sum` instances for both components of the product:

```lean
instance [Sum X] [Sum Y] : Sum (Prod X Y) where
  sum := fun (x, y) => sum x + sum y
```

This instance sums the components of a product by applying `sum` to each component and adding the results.

#### Handling More Complex Cases


Our current implementation of `sum` effectively handles nested lists and products but encounters issues when dealing with elements that are not inherently summable. For example:

```lean (error:=true)
#eval sum [("dog", 15), ("cat", 2), ("elephant", 400)]
```

In this case, `sum` fails because tuples containing a string and a number do not have a direct `Sum` instance defined.

To address such scenarios, one approach is to provide a default `Sum` instance for any type. This instance would act as a fallback when no more specific `Sum` instance is applicable:

```lean
instance (priority := low) : Sum A where
  sum a := 0
```

We assign a low priority to this default instance because it is intended to be used only as a fallback. By giving it low priority, Lean will prefer more specific `Sum` instances over this default one, preventing it from overriding cases where a more appropriate instance exists. This approach helps ensure that the default instance does not inadvertently mask other `Sum` implementations and is only used when no other suitable instance can be found.

```lean
#eval sum [("dog", 15), ("cat", 2), ("elephant", 400)]
```


### Working with Functions of Arbitrary Arity

One important application of defining functions inductively is to handle functions with arbitrary arity. For instance, consider uncurry functions, which transform functions from tuples into functions with multiple arguments. While one might want to define an uncurry function like this:

```
def uncurry (f : X₁ → ... → Xₙ → Y) (x : X₁ × ... × Xₙ) : Y := f x.1 ... x.n
```

Lean does not support ellipses (`...`) for arbitrary arity directly. Instead, we use typeclasses to define a general `Uncurry` typeclass:

```lean
class Uncurry (F : Type) (Xs Y : outParam Type) where
  uncurry : F → Xs → Y

export Uncurry (uncurry)
```

Here, `F` represents a function type `X1 → ... → Xn → Y`, and `Xs` represents the product type `X1 × ... × Xn`.

We define instances for different numbers of arguments by induction. For `n = 1`, we have:

```lean
instance : Uncurry (X → Y) X Y where
  uncurry := fun f => f
```

For the inductive step, where we have `n + 1` arguments:

```lean
instance [Uncurry F Xs Y] : Uncurry (X → F) (X × Xs) Y where
  uncurry := fun f (x, xs) => Uncurry.uncurry (f x) xs
```

And a simple test:
```lean
#eval uncurry (fun a b c d : Nat => a + b + c + d) (1,2,3,4)
```

This general `uncurry` function is already provided by mathlib with {name}`Function.HasUncurry.uncurry` and notation `↿f` for `Function.HasUncurry.uncurry f`.

```lean
#eval (↿fun a b c d : Nat => a + b + c + d) (1,2,3,4)
```



### Exercise

1. Privide overload of `sum` for {name}`Array`. The following whould work
```
example : sum (#[1,3,4], [#[(10,5),(20,8)], #[100]], 1000) = 1251 := by 
  native_decide
```
::: Solution

```lean
instance [Sum A] : Sum (Array A) where
  sum l := l.foldl (fun acc a => acc + sum a) 0

example : sum (#[1,3,4], [#[(10,5),(20,8)], #[100]], 1000) = 1251 := by   
  native_decide
```

:::

2. Define function that computes the size of product type i.e. `prodSize (X₁ × ... × Xₙ) = n`.
   Also implement "flat" version which takes into account associativity of product i.e. it counts
   the size of the product irrespective of the product bracketing. Make the following work

```
example : prodSize (Nat × Nat × Nat) = 3 := by decide
example : prodSize ((Nat × Nat) × Nat) = 2 := by decide
   
example : flatProdSize (Nat x Nat x Nat) = 3 := by decide
example : flatProdSize ((Nat x Nat) x Nat) = 3 := by decide
```

::: Solution

```lean
class ProdSize (X : Type) where
  prodSize : Nat
  
export ProdSize (prodSize)

instance (priority:=low) {X} : ProdSize X where
  prodSize := 1

instance (priority:=low) {X Y} [ProdSize Y] : ProdSize (X×Y) where
  prodSize := 1 + prodSize Y

example : prodSize (Nat × Nat × Nat) = 3 := by decide
example : prodSize ((Nat × Nat) × Nat) = 2 := by decide

class FlatProdSize (X : Type) where
  flatProdSize : Nat
  
export FlatProdSize (flatProdSize)

instance (priority:=low) {X} : FlatProdSize X where
  flatProdSize := 1

instance (priority:=low) {X Y} [FlatProdSize X] [FlatProdSize Y] : 
    FlatProdSize (X×Y) where
  flatProdSize := flatProdSize X + flatProdSize Y

example : flatProdSize (Nat × Nat × Nat) = 3 := by decide
example : flatProdSize ((Nat × Nat) × Nat) = 3 := by decide
```

:::
 
3. Define function curry that takes a function `f : X₁ × ... × Xₙ → Y` and produces function `g : X₁ → ... → Xₙ → Y`.

::: Solution
```lean
class Curry (Xs Y : Type) (F : outParam Type) where
  curry : (Xs → Y) → F

instance (priority:=low) {X Y} : Curry X Y (X→Y) where
  curry := fun f => f

instance [Curry Xs Y F] : Curry (X×Xs) Y (X→F) where
  curry := fun f x => Curry.curry (fun xs => f (x,xs))

#eval (Curry.curry fun ((a,b,c,d) : ℕ×ℕ×ℕ×ℕ) => a + b + c + d) 1 2 3 4
```

:::

4. Define function that returns i-th element of product type `X₁ × ... × Xₙ`. This is somewhat tricky as you have to do induction in `i` and `n`.


::: Solution
```lean
class ProdGet (Xs : Type) (n : Nat) (Xn : outParam Type) where
  get : Xs -> Xn

instance (priority:=low) : ProdGet X 0 X where
  get := fun x => x

instance : ProdGet (X × Xs) 0 X where
  get := fun (x,xs) => x

instance [ProdGet Xs n Xn] : ProdGet (X × Xs) (n+1) Xn where
  get := fun (x,xs) => ProdGet.get n xs

#eval ProdGet.get 0 (1,"hello",3.1415)
#eval ProdGet.get 1 (1,"hello",3.1415)
#eval ProdGet.get 2 (1,"hello",3.1415)
```
:::

5. Again define function that returns `i-th` element of product type but now ignores associativity of the product i.e. `get 0 ((0,1),(2,3)) = 0` because previously we got `get 0 ((0,1),(2,3)) = (0,1)`.

6. Define complete interface for product types that allows you to get, set and modify elements of arbitrary product type.


```lean (show:=false)
end InductiveOverload
```

### Polymorphism Over Types and Terms

```lean (show:=false)
namespace OverloadTypeAndTerm
```

In the earlier sections, we defined a polymorphic function `size` that operates on collections like {name}`List` or {name}`Array`. However, what if we want to extend this functionality to types themselves? For instance, we might want `size Bool = 2`, `size Unit = 1`, and `size Empty = 0`. The initial approach we used would require adding instances for `Size Type`, which is problematic because we cannot directly provide a `size` for any arbitrary type.

To solve this, we need to redefine the typeclass `Size` so that it can handle both types and values. The key idea is to make the argument of the `size` function part of the typeclass itself rather than a parameter of the function:

```lean
class Size {A : Type u} (a : A) where
  size : Nat

instance {A} (l : List A) : Size l where
  size := l.length

instance {A} (a : Array A) : Size a where
  size := a.size
```

In this refined definition, `Size` is parameterized by a value `a` of type `A`, which allows us to define instances for specific types. For example:

```lean
instance : Size Bool where
  size := 2
```

Notice that we use `A : Type u` instead of just `A : Type`. The reason for this is that Lean uses a concept called **universe polymorphism**. If we simply wrote `A : Type`, it would restrict `A` to the lowest universe level, `Type 0`, which contains types like `Nat` or `Bool`. However, for the above instance `Size Bool` we need `A = Type` thus `A : Type 1`. Lean's type theory is stratified into multiple **universes** to avoid paradoxes like Russell's paradox.

To see this in action, you can run the following command:

```lean (name:=typetype)
#check Type
```
```leanOutput typetype
Type : Type 1 
```

This tells us that `Type` itself lives in `Type 1`, meaning that `Type 0 : Type 1`. More generally, `Type u` refers to a type in any universe level `u`, where `Type u : Type (u+1)`. By using `A : Type u`, we allow `A` to belong to **any universe level**, making `Size` more flexible and applicable to a wider range of types, including types themselves like `Bool`, `Unit`, and `Empty`.

We achieved a more general `size` function that works polymorphically not only over collections but also over types themselves.

### Exercises

1. Define a function `first?` that returns the first element of a value `x` wrapped in an `Option`. If `x` is empty, the function should return `none`. We want the following results:
```
example : first? [1, 2, 3] = .some 1 := by decide
example : first? Bool = .some false := by decide
example : first? ([] : List ℕ) = none := by decide
example : first? Empty = none := by decide
```

::: Solution

```lean
class First {A : Type u} (a : A) (B : outParam (Type v)) where
  first? : Option B

export First (first?)

instance (l : List A) : First l A where
  first? := l.head?

instance : First Bool Bool where
  first? := .some false

instance : First Empty Empty where
  first? := .none

instance : First (Fin n) (Fin n) where
  first? :=
    if h : n ≠ 0 then
      .some ⟨0, by omega⟩
    else
      .none

example : first? [1, 2, 3] = .some 1 := by decide
example : first? Bool = .some false := by decide
example : first? ([] : List ℕ) = none := by decide
example : first? Empty = none := by decide
```
:::


2. General pair function. Define function `pair` that for two types `X` and `Y` returns `X × Y` but for two elements `(x : X)` and `(y : Y)` returns `(x,y)`.

```
example {X Y : Type} : pair X Y = X × Y := by rfl
example {X Y : Type} (x : X) (y : Y) : pair x y = (x,y) := by rfl
```

::: Solution
```lean

class Pair {X Y : Type*} (x : X) (y : Y) 
           (XY : outParam Type*) where
  pair : XY

export Pair (pair)

instance {X Y : Type*} : Pair X Y (Type _) where
  pair := X × Y

instance {X Y : Type*} (x : X) (y : Y) : Pair x y (X×Y) where
  pair := (x,y)


example {X Y : Type} : pair X Y = (X × Y) := by rfl
example {X Y : Type} (x : X) (y : Y) : pair x y = (x,y) := by rfl


-- Alternative definition together with notation which requires some knowledge 
-- of metaprogramming.
-- Have a look at this Zulip thread for motivation 
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.8A.97.20notation.20for.20types.20and.20elements/near/321358639
class Pair' {X Y : Type*} (x : X) (y : Y) 
            {XY : outParam Type*} (xy : outParam XY) where

open Lean Elab Term Meta in
scoped elab x:term "⊗" y:term : term => withFreshMacroScope do
  _ ← synthInstance (← elabType (← `(Pair' $x $y ?m)).raw)
  elabTerm (← `(?m)).raw none

instance {X Y : Type*} : Pair' X Y (X×Y) := ⟨⟩
instance {X Y : Type*} (x : X) (y : Y) : Pair' x y (x,y) := ⟨⟩

-- Notice that the result it the familiar `X × Y` and `(x,y)` i.e. the notation
-- `⊗` unifies product notation for types and elements.
#check ℕ ⊗ ℕ     -- ℕ × ℕ
#check (0:ℕ) ⊗ 1  -- (0,1)
```

:::


```lean (show:=false)
end OverloadTypeAndTerm
```


# Typeclasses as Interfaces

```lean (show:=false)
namespace TCInterfaces
```

After exploring function overloading, we can now turn to another powerful application of typeclasses in Lean: defining **interfaces** for types. While function overloading allows different functions to be chosen based on the types of arguments, typeclasses can also be used to define a set of required behaviors for a type.

In this sense, typeclasses in Lean are similar to **interfaces** in object-oriented programming (OOP) languages, where a typeclass defines a set of operations or properties that a type must implement. Unlike traditional OOP, where interfaces are often rigid and tied to specific types, Lean’s typeclass system is more flexible, allowing types to implement typeclasses after they are defined and providing a more modular way to express behaviors.

## Defining an Array-like Interface

For example, let's define a typeclass that expresses that a type `Arr` behaves like an array, providing operations to access an element by index and get the length of the array. This is how we might define such a typeclass in Lean:

```lean
class ArrayLike (Arr : Type) (Elem : outParam Type) where
  get : Arr → Nat → Option Elem
  length : Arr → Nat
```

This defines an interface for any type `Arr` that behaves like an array. For a type to implement this interface, it must provide definitions for both `get` and `length`. The **`get`** function retrieves an element by index, returning `Option Elem` to handle out-of-bounds access. The **`length`** function simply returns the length of the array.

### Implementing the Interface

Next, let's implement this interface for specific types, such as `List A`. Lists in Lean already have a concept of length and indexed access, so this is a natural fit for our `ArrayLike` interface:

```lean
instance {A} : ArrayLike (List A) A where
  get l n := if h : n < l.length then some (l.get ⟨n,h⟩) else none
  length l := l.length
```

Here, we define an instance of `ArrayLike` for `List A`. The **`get`** function checks if the index is within bounds and retrieves the element if possible, returning `none` if the index is out of range. The **`length`** function simply calls the built-in `length` method of the list.

### Extending the Interface to Other Types

We can extend the `ArrayLike` interface to other types, such as arrays:

```lean
instance {A} : ArrayLike (Array A) A where
  get a n := a.get? n
  length a := a.size
```

In this instance, we use the built-in `get?` method of `Array` for safe element access, which already returns an `Option A`. The `length` method is implemented using the `size` function of arrays.

### Conclusion

Typeclasses in Lean provide a flexible way to define interfaces for types, similar to interfaces in object-oriented languages. By using typeclasses like `ArrayLike`, we can define operations such as `get` and `length`, which can then be implemented for various types like `List` and `Array`. This allows us to write generic functions that work across multiple types, promoting code reuse and flexibility.

Unlike traditional interfaces, typeclasses allow us to retroactively add functionality to types without modifying their original definitions. This makes them a powerful tool for modular, extensible design in Lean, enabling polymorphism and cleaner abstractions in complex codebases.

```lean (show:=false)
end TCInterfaces
```
