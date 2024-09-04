import ScientificComputingInLean.Meta
import SciLean
import SciLean.Data.Fintype.Quotient

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxRecDepth   100000000
set_option maxHeartbeats 100000000

open Lean.MessageSeverity
open SciLean

set_default_scalar ℝ

#doc (Manual) "Expression Compiler" =>


In this section we will show how to write a simple function transformation that compiles certain subset of Lean expressions to a very simple language. 

The motivation is that we would like to take a lean function and convert it into a function that can be executed on GPU. We define a simple language of functions that can be executed on GPU.

We will consider a language where every function take `r` arguments of type `Float` and returns `Float`


Let's start by defining structures representing primitive functions and constans and then we will define the type representing expressions in our simple language.



A primitive function of arity `r` is represented by the following structure
```lean
structure Function (arity : Nat) where
  val : (Fin arity → Float) → Float
  name : String
```
`val` is the lean interpretation of this function and `name` is a name of this name of the function in our desired target language.

Note that the input type of `val` is `(Fin r → Float)` which one of many representations of an array of `r` values. Alternativelly we could use type `Float × ... × Float` as input but working with it is much harder.


For example addition and multiplication of two numbers can be defined as
```lean
def add : Function 2 :=
{
  val := fun xs => xs 0 + xs 1
  name := "add"
}

def mul : Function 2 :=
{
  val := fun xs => xs 0 * xs 1
  name := "mul"
}
```

Similarly for primitive constants of dimension `n` we use this structure
```lean
structure Constant where
  val : Float
  name : String
deriving Inhabited
```

An expression of our language is a function of arity `r`, input dimensions `ns 0, ... ns (r-1)` and output dimension `m` is represented by the following inductive data type
```lean
inductive ExprRepr : (arity : Nat) → Type where
  | var (r : Nat) (i : Fin r) : ExprRepr r
  | fn {r : Nat} (f : Function r) : ExprRepr r
  | const (r : Nat) (c : Constant) : ExprRepr r
  | comp {s r : Nat} (f : ExprRepr s) 
         (gs : (i : Fin s) → ExprRepr r) : ExprRepr r
```
The first constructore `var` allows us to pick one of the input arguments and return it as an output. The next two `fn` and `const` creates turns primitive function or constant to an expression. Lastly the `comp` constructor takes an expression of arity `s` and composes it with `s` expressions `gs 0, ..., gs (s-1)`.

The reason why we named this type `ExprRepr` and not `Expr` will be explained a bit later.

For example a function adding a vector to itself would be represented by the following expression
```lean
#check ExprRepr.comp (.fn add) (fun _ => .var 1 0)
```
Which correponds to the expression `add(x0, x0)` if `.var 1 0` corresponds to `x0`.

Now we can write a function that takes an expression `(e : ExprRepr r)` and turns it into C function. This is very easy because we do not allow for partial applications or lambda abstractions.

```lean
def ExprRepr.toCCodeBody (e : ExprRepr r) : String :=
  match e with
  | .var _ i => s!"x{i}"
  | .fn f => toString f.name
  | .const _ f => toString f.name
  | .comp (.const _ f) _ => toString f.val
  | @comp r _ f gs => Id.run do
    let mut s := s!"{f.toCCodeBody}("
    for i in fullRange (Fin r) do
      if i.1 ≠ 0 then
        s := s ++ ", "
      s := s ++ (gs i).toCCodeBody
    s := s ++ ")"
    return s

def ExprRepr.toCCodeHeader (_ : ExprRepr r) (name : String) : String := Id.run do
  let mut s := s!"float {name}("
  for i in fullRange (Fin r) do
    if i.1 ≠ 0 then
      s := s ++ ", "
    s := s ++ s!"float x{i}"
  s := s ++ ")"
  return s

def ExprRepr.toCCode (e : ExprRepr r) (name : String) : String := Id.run do
  s!"{e.toCCodeHeader name}\{\n  return {e.toCCodeBody};\n}"
```


Let's compile the previous example 
```lean (name:=addselfcpp)
#eval (ExprRepr.comp (.fn (add)) (fun _ : Fin 2 => .var 1 0))
      |>.toCCode "add_self"
```
```leanOutput addselfcpp
"float add_self(float x0){\n  return add(x0, x0);\n}"
```

# Compiling from Lean to Expressions

Writing down `ExprRepr` is very tedious. We would like to take a Lean expression on automatically turn in into `ExprRepr` is possible. Therefore let's define a funciton `compile` that turns a Lean expression to `ExprRepr`. Before doing so we need to define a function `ExprRepr.toLean` taking `(e : ExprRepr r ns m)` and interpreting it as a Lean function of type `((i : Fin r) → Float) → Float`. Once we have this function we can formally specify `compile` function.

```lean
def ExprRepr.toLean 
    (e : ExprRepr r) (xs : (i : Fin r) → Float) : Float :=
  match e with
  | var _ i => xs i
  | .fn f => f.val xs
  | .const _ c => c.val
  | .comp f gs =>
    let f' := f.toLean
    let ys := fun j => (gs j).toLean xs
    f' ys
```



Now we can define/specify `compile` function in nonconstructive way. If there is a representation `(e : Expr r)` a a function `f` then return it otherwise return some junk value.
```lean (keep:=false)
open Classical in
@[fun_trans]
noncomputable
def compile (f : Float → Float) : ExprRepr 1 :=
  if h : ∃ (e : ExprRepr 1), 
           f = (fun x => e.toLean (fun _ => x)) then
    choose h
  else
    .const _ default
```

Unfortunatelly this definition has a serious flaw. For a function `(f : Float → Float)` there can be multiple expressions `ExprRepr` representing this function. Therefore `compile f` is not really uniquelly defined and as it is we would not be able to prove anything about this funciton.

The usuall mathematical remedy is to work with equivalence classes of all the expressions that represent the same function. This might sound a bit bizare for any practical purposes but we are in luck because Lean has first class support for quotient types. We can define `Expr r` as equivalence class of all the expressions `(e : ExprRepr r)` such that they have the same interpretation as lean functions.

To define `Expr` we first have to equip {name}`ExprRepr` with a natural notion of equivalence i.e. `e` and `e'` are equivalent if their Lean interpretations are the same. The typeclass {name}`Setoid` execatly captures that fact that a type has a natural notion of a equivalence.
```lean
instance {r} : Setoid (ExprRepr r) where
  r := fun e e' => e.toLean = e'.toLean
  iseqv := by constructor <;> aesop
```

Once we have {name}`Setoid` structure on {name}`ExprRepr` we can quotion define `Expr` using {name}`Quotient`.
```lean
def Expr (r) := Quotient (α:=ExprRepr r) (by infer_instance)
```

## Quotient Intermezzo

::: TODO

Rewrite this subsection to also use {name}`Quotient`.

:::

In general, for a relation `(r : X → X → Prop)` the type `Quot r` will create a quotient of `X` along the relation `r`. (More preciselly, `Quot r` is a quotient of `X` along the smallest relation containing `r`). Working with quotient is actually very common in programming. For example, we can represent multisets of natural numbers `List Nat` but we have two options how to maintain the multiset invariant. Either work with lists that are sorted
```lean
def MultiSetV1 := { l : List Nat // l.Sorted (· ≤ ·)}
```
This is the usual approach as maintaining the sorted invariant is relativelly easy.

Alternativelly, we can work with unsorted lists but we require that any function consuming such list produces the same values whenever we permute the list. This is a really dangerous and error prone way of working with multisets and it is almost never done this way. In Lean, things can be different as it is theorem prover and such invariant is not just an gentleman agreement but the compiler can force user to prove it everytime they use a multiset. 

Therefore we can define a relation `multiSetRel : List Nat → List Nat → Prop` 
```lean
structure multiSetRel (l l' : List Nat) : Prop where
  hl : l.length = l'.length
  hperm : ∃ π : Fin l.length → Fin l.length, 
    π.Bijective ∧ ∀ i, l.get (π i) = l'.get (hl▸ i)
```
waking that `multiSetRel l l` are equivalent if they have the same length `hl` and there exists a permuation `π` such that if we permute `l` by it we obtain `l'`.

Now we can define multisets as a quotient of `List Nat` by this relation.
```lean
def MultiSetV2 := Quot multiSetRel
```

Using function {name}`Quot.lift` can for example define a function `sum` that adds all the elements together
```lean
def MultiSetV2.sum (s : MultiSetV2) : Nat :=
  Quot.lift (fun repr => ∑ i, repr.get i) sorry_proof s
```
As we are not too interested in proving things in this book we just omit the proof with `sorry_proof` but this anytime we use `Quot.lift` to work with `(s : MultiSetV2)` through its list representation we are reminded that such function should be independent on the particular odering of the list.

One big advantage of the second approach to multisets is that it does not use ordering on the numbers therefore we can have a multiset of objects that can't be ordered.

Lasty, for an element `(x : X)` and relation `r : X → X → Prop` we can create and element of the quotient `Quot r` with `Quot.mk r x`. Usually we omit `r` as it can be infered from the context. 

For example we can create a multiset from the list {lean}`[0,4,3,10]`.
```lean
#check (Quot.mk _ [0,4,3,10] : MultiSetV2)
```

::: TODO

Talk about {name}`Quot.unquot` which allows us to recover the runtime representant of `(x : Quot r)`

:::

## Back to Compilation

Let's go back to compiling lean expressions. Hopefully we have convinced you that the 

```lean
open Classical in
@[fun_trans]
noncomputable
def compile (f : (Fin n → Float) → Float) : Expr n :=
  if h : ∃ (e : ExprRepr n), 
           f = e.toLean then
    ⟦choose h⟧
  else
    ⟦.const _ default⟧
```

Working with {name}`Quot.mk` and {name}`Quot.lift` is tedious so often we want to define the same function that live on the original type as on the quotient type. In our case we want to define analogues of  {name}`ExprRepr.var`, {name}`ExprRepr.fn`, {name}`ExprRepr.const` and {name}`ExprRepr.comp` on {name}`Expr`.

The first three are very easy
```lean
def Expr.var (r : Nat) (i : Fin r) : Expr r := ⟦.var r i⟧
def Expr.fn (f : Function r) : Expr r := ⟦.fn f⟧
def Expr.const (r : Nat) (c : Constant) : Expr r := ⟦.const r c⟧
```

The last one is quite a bit harder as it accepts {name}`Expr` as input therefore we need to use {name}`Quot.lift` to define the function on the representan `ExprRepr` and then show it is independent.
```lean
def Expr.comp (f : Expr s) (g : (i : Fin s) → Expr r) : Expr r :=
  f.lift (fun frepr =>
    (Quotient.finLiftOn g (fun gsrepr => 
      ⟦.comp frepr gsrepr⟧) 
    (by sorry_proof))) 
  (by sorry_proof)
```

We can start writing function transformation theorems. The identity rule takes a function that picks one of the inputs and produces {name}`Expr.var`
```lean
@[fun_trans]
theorem compile.id_rule (i : Fin n) : 
  compile (fun x : (Fin n → Float) => x i) = .var n i := sorry_proof
```

The composition rule has to take function `f` with arity `s` and a collection of `s` functions `(g · i)` with arity `r`.
```lean
@[fun_trans]
theorem compile.comp_rule 
  (f : (Fin s → Float) → Float) (g : (Fin r → Float) → Fin s → Float) : 
  compile (fun x => f (g x)) 
  = 
  let f' := compile f
  let g' := fun i => compile (g · i)
  .comp f' g' := sorry_proof
```

::: TODO

As stated these theorems are false. We should add a predicate that function is compilable `IsCompilable f`.

:::


Function transformation theorem for addition and multiplication
```lean
@[fun_trans]
theorem compile.add_rule 
  (f g : (Fin n → Float) → Float) : 
  compile (fun x => f x + g x) 
  = 
  let f' := compile f
  let g' := compile g
  .comp (.fn add) ![f',g'] := sorry_proof

@[fun_trans]
theorem compile.mul_rule 
  (f g : (Fin n → Float) → Float) : 
  compile (fun x => f x * g x) 
  = 
  let f' := compile f
  let g' := compile g
  .comp (.fn mul) ![f',g'] := sorry_proof
```


Lean uses `OfNat.ofNat n` to represent numerical constants for any type and `OfScientific.ofScientific` to represent numerical constants in scientific notation. We first define {name}`Constant` for both and then provide transformation rules.
```lean
def natConst (n : Nat) : Constant where
  val := (n : Float)
  name := toString n

def scientificConst 
    (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) : Constant 
where
  val := OfScientific.ofScientific mantissa exponentSign decimalExponent
  name := toString (OfScientific.ofScientific mantissa exponentSign decimalExponent)

@[fun_trans]
theorem compile.ofNat_rule 
  (i : Nat) : 
  compile (fun _ : Fin n → Float => OfNat.ofNat i) 
  = 
  (.const n (natConst i)) := sorry_proof

@[fun_trans]
theorem compile.ofScientific_rule : 
  compile (fun _ : Fin r → Float => OfScientific.ofScientific n b m) 
  = 
  (.const r (scientificConst n b m)) := sorry_proof
```


Let's test {name}`compile` on a simple function of two arguments
```lean (name:=compilesimple1)
#check (compile (fun x : (Fin 2 → Float) => 3.1415 * (x 0 + x 1 + 5))) 
  rewrite_by fun_trans
```
```leanOutput compilesimple1
(Expr.fn mul).comp
  ![Expr.const 2 (scientificConst 31415 true 4),
    (Expr.fn add).comp ![(Expr.fn add).comp ![Expr.var 2 0, Expr.var 2 1], Expr.const 2 (natConst 5)]] : Expr 2
```
We can see that {name}`compile` has been completely eliminated.

The last step of is to generate the corresponding C code for a given `(e : Expr r)`. To do that we need access the corresponding `ExprRepr r` and call {name}`ExprRepr.toCCode`. Previously we have discussed that accessing the runtime representative with {name}`Quot.unquot` is unsound therefore implementing `Expr.toCCode` has to be unsound too.
```lean
unsafe def Expr.toCCode {r} (e : Expr r) (name : String) : String := 
  e.unquot.toCCode name
```

```lean (name:=compilesimple2)
#eval (compile (fun x : (Fin 2 → Float) => 3.1415 * (x 0 + x 1 + 5))) 
  rewrite_by fun_trans |>.toCCode "foo"
```
```leanOutput compilesimple2
"float foo(float x0, float x1){\n  return mul(3.141500, add(add(x0, x1), 5));\n}"
```



## Exercises

1. Using {name}`compile` is not completely ergonomic. Define `compile1 : (Float → Float) → Expr 1`, `compile2 : (Float → Float → Float) → Expr 2`, ... . Mark these function with `@[simp]` attribute for `fun_trans` to automatically unfold them. For example, you should be able to able to write
```
#eval (compile2 (fun x y => (x + y) * (x + y))) 
      rewrite_by fun_trans |>.toCCode "foo"
```

::: Solution
```lean
@[simp]
noncomputable
def compile1 (f : Float → Float) : Expr 1 :=
  compile (fun x : Fin 1 → Float => f (x 0))

@[simp]
noncomputable
def compile2 (f : Float → Float → Float) : Expr 2 :=
  compile (fun x : Fin 2 → Float => f (x 0) (x 1))


#eval (compile1 (fun x => (x + x) * x)) 
  rewrite_by 
    fun_trans
  |>.unquot.toCCode "foo1"

#eval (compile2 (fun x y => (x + y) * (x + y))) 
  rewrite_by fun_trans
  |>.unquot.toCCode "foo2"
```
:::


2. Define function transformations for other operations like division, negation or special functions like `sin`, `cos`, `exp`, ..

3. Add support for infix notation for generated C code. 

4. (very hard/research direction) Extend {name}`ExprRepr` to support let bindings and add function transformation for let bindings. 

(Right now it is not clear to me how to do this.)

5. (very hard/research direction) Generalize this approach to a function of arbitrary types.

The main idea would be to modify the definition of {name}`Function` and {name}`ExprRepr` to the following
```lean
namespace Generalization
/-- 
Structure representing primitive function of type `X 0 × ... × X (r-1) → Y`
-/
structure Function (r : Nat) (Xs : Fin r → Type) (Y : Type) where
  val : ((i : Fin r) → Xs i) → Y
  name : Lean.Name

/-- Expression representing function of arity `r` with input types 
`X 0, ..., X (r-1)` and output type `Y`-/
inductive ExprRepr : (r : Nat) → (Xs : Fin r → Type) → (Y : Type) → Type 1 
where
  | var (r : Nat) (Xs : Fin r → Type) (i : Fin r) : ExprRepr r Xs (Xs i)
  | fn {r : Nat} {Xs : Fin r → Type} {Y : Type} 
       (f : Function r Xs Y) : ExprRepr r Xs Y
  | comp {s r : Nat} {Xs : Fin r → Type} {Ys : Fin s → Type} {Z : Type}
         (f : ExprRepr s Ys Z) 
         (gs : (i : Fin s) → ExprRepr r Xs (Ys i)) : ExprRepr r Xs Y

end Generalization
```
