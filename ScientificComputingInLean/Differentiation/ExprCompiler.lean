import ScientificComputingInLean.Meta
import SciLean

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

We will consider a language where every function take `r` arguments with types `Float^[n₁], ..., Float^[nᵣ]` and produces and array of type `Float^[m]`


Let's start by defining structures representing primitive functions and constans and then we will define the type representing expressions in our simple language.



A primitive function of arity `r`, input dimensions `ns 0, ... ns (r-1)` and output dimension `m` is represented by the following structure
```lean
structure Function (r : Nat) (ns : Fin r → Nat) (m : Nat) where
  (val : ((i : Fin r) → Float^[ns i]) → Float^[m])
  (name : Lean.Name)
```
`val` is the lean interpretation of this function and `name` is a name of this name of the function in our desired target language.

Note that the input type of `val` is `((i : Fin r) → Float^[ns i])` which one of many representations of an array of `r` values with types `Float^[ns 0], ...,  Float^[ns (r-1)]`. Alternativelly we could use type `Float^[ns 0] × ... ×  Float^[ns (r-1)]` as input but working with it is much harder.


For example addition of two vectors can be defined as
```lean
def add {n : Nat} : Function 2 (fun _ => n) n :=
{
  val := fun xs => xs 0 + xs 1
  name := `add
}
```
or scalar multiplication
```lean
def smul {n : Nat} : 
  Function 2 (fun i => match i with | ⟨0,_⟩ => 1 | ⟨1,_⟩ => n) n := 
{
  val := fun xs => (xs 0)[0] • xs 1
  name := `smul
}
```

Similarly for primitive constants of dimension `n` we use this structure
```lean
structure Constant (n : Nat) where
  (val : Float^[n])
  (name : Lean.Name)
deriving Inhabited
```

An expression of our language is a function of arity `r`, input dimensions `ns 0, ... ns (r-1)` and output dimension `m` is represented by the following inductive data type
```lean
inductive ExprRepr : (arity : Nat) → (Fin arity → Nat) → Nat → Type where
  | var (r) (ns : Fin r → Nat) (i : Fin r) : ExprRepr r ns (ns i)
  | fn (f : Function r ns m) : ExprRepr r ns m
  | const (r) (ns : Fin r → Nat)
          (c : Constant m)  : ExprRepr r ns m
  | comp (f : ExprRepr s ms k) 
         (gs : (i : Fin s) → ExprRepr r ns (ms i)) : ExprRepr r ns k
```
The first constructore `var` allows us to pick one of the input arguments and return it as an output. The next two `fn` and `const` creates turns primitive function or constant to an expression. Lastly the `comp` constructor takes an expression of arity `s` and input dimensions `ms 0, ..., ms (s-1)` and composes it with `s` expressions `gs 0, ..., gs (s-1)`.

The reason why we named this type `ExprRepr` and not `Expr` will be explained a bit later.

For example a function adding a vector to itself would be represented by the following expression
```lean
#check ExprRepr.comp (.fn add) (fun _ => .var 1 (fun _ => 3) 0)
```
Which correponds to the expression `add(x0, x0)` if `.var 1 (fun _ => 3) 0` corresponds to `x0`.

Now we can write a function that takes an expression `(e : ExprRepr r ns m)` and turns it into C++ function. This is very easy because we do not allow for partial applications or lambda abstractions.

```lean
def ExprRepr.toCppCodeBody (e : ExprRepr r n m) : String :=
  match e with
  | .var _ _ i => s!"x{i}"
  | .fn f => toString f.name
  | .const _ _ f => toString f.name
  | .comp (.const _ _ f) _ => toString f.val
  | @comp r _ _ _ _ f gs => Id.run do
    let mut s := s!"{f.toCppCodeBody}("
    for i in fullRange (Fin r) do
      if i.1 ≠ 0 then
        s := s ++ ", "
      s := s ++ (gs i).toCppCodeBody
    s := s ++ ")"
    return s

def ExprRepr.toCppCodeHeader (_ : ExprRepr r ns m) (name : String) : String := Id.run do
  let mut s := s!"std::array<Float,{m}> {name}("
  for i in fullRange (Fin r) do
    if i.1 ≠ 0 then
      s := s ++ ", "
    s := s ++ s!"std::array<Float,{ns i}> x{i}"
  s := s ++ ")"
  return s

def ExprRepr.toCppCode (e : ExprRepr r ns m) (name : String) : String := Id.run do
  s!"{e.toCppCodeHeader name}\{\n  return {e.toCppCodeBody};\n}"
```


Let's compile the previous example 
```lean (name:=addselfcpp)
#eval (ExprRepr.comp (.fn add) (fun _ => .var 1 (fun _ => 3) 0))
      |>.toCppCode "add_self"
```
```leanOutput addselfcpp
"std::array<Float,3> add_self(std::array<Float,3> x0){\n  return add(x0, x0);\n}"
```

# Compiling from Lean to Expressions

Writing down `ExprRepr` is very tedious. We would like to take a Lean expression on automatically turn in into `ExprRepr` is possible. Therefore let's define a funciton `compile` that turns a Lean expression to `ExprRepr`. Before doing so we need to define a function `ExprRepr.toLean` taking `(e : ExprRepr r ns m)` and interpreting it as a Lean function of type `((i : Fin r) → Float^[ns i]) → Float^[m]`. Once we have this function we can formally specify `compile` function.

```lean
def ExprRepr.toLean 
    (e : ExprRepr r ns m) (xs : (i : Fin r) → Float^[ns i]) : Float^[m] :=
  match e with
  | var _ ns i => xs i
  | .fn f => f.val xs
  | .const _ _ c => c.val
  | .comp f gs =>
    let f' := f.toLean
    let ys := fun j => (gs j).toLean xs
    f' ys
```



Now we can define/specify `compile` function in nonconstructive way. If there is a representation `(e : Expr r ns m)` a a function `f` then return it otherwise return some junk value.
```lean (keep:=false)
open Classical in
@[fun_trans]
noncomputable
def compile (f : Float^[m] → Float^[n]) : ExprRepr 1 (fun _ => m) n :=
  if h : ∃ (e : ExprRepr 1 (fun _ => m) n), 
           f = (fun x => e.toLean (fun _ => x)) then
    choose h
  else
    .const _ _ default
```

Unfortunatelly this definition has a serious flaw. For a function `(f : Float^[m] → Float^[n])` there can be multiple expressions `ExprRepr` representing this function. Therefore `compile f` is not really uniquelly defined and as it is we would not be able to prove anything about this funciton.

The usuall mathematical remedy is to work with equivalence classes of all the expressions that represent the same function. This might sound a bit bizare for any practical purposes but we are in luck because Lean has first class support for quotient types. We can define `Expr r ns m` as equivalence class of all the expressions `e : Expr r ns m` such that they have the same interpretation as lean functions.
```lean
def Expr (r ns m) := Quot (fun (e e' : ExprRepr r ns m) => e.toLean = e'.toLean)
```

## Quotient Intermezzo

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


Lasty, for an element `(x : X)` and relation `r : X → X → Prop` we can create and element of the quotient `Quot r` with `Quot.mk r x`. Usually we omit `r` as it can be infered from the context. 

For example we can create a multiset from the list {lean}`[0,4,3,10]`.
```lean
#check (Quot.mk _ [0,4,3,10] : MultiSetV2)
```


## Back to Compilation

Let's go back to compiling lean expressions. Hopefully we have convinced you that the 

```lean
open Classical in
@[fun_trans]
noncomputable
def compile (f : Float^[m] → Float^[n]) : Expr 1 (fun _ => m) n :=
  if h : ∃ (e : ExprRepr 1 (fun _ => m) n), 
           f = (fun x => e.toLean (fun _ => x)) then
    Quot.mk _ (choose h)
  else
    Quot.mk _ (.const _ _ default)
```

Working with {name}`Quot.mk` and {name}`Quot.lift` is tedious so often we want to define the same function that live on the original type as on the quotient type. In our case we want to define analogues of  {name}`ExprRepr.var`, {name}`ExprRepr.fn`, {name}`ExprRepr.const`, {name}`ExprRepr.comp` on {name}`Expr`.

The first three are very easy
```lean
def Expr.var (r : Nat) (ns : Fin r → Nat) (i : Fin r) : Expr r ns (ns i) :=
  Quot.mk _ (.var r ns i)

def Expr.fn (f : Function r ns m) : Expr r ns m :=
  Quot.mk _ (.fn f)

def Expr.const (r : Nat) (ns : Fin r → Nat) (c : Constant m) : Expr r ns m :=
  Quot.mk _ (.const r ns c)
```

The next two are a bit harder as then should accept {name}`Expr` as input therefore we need to use {name}`Quot.lift` to define the function on the representan `ExprRepr` and then show it is independent.
```lean
def Quot.liftForallOn {I} {X : I → Type}
  {r : (i : I) → X i → X i → Prop}
  (xs : (i : I) → Quot (r i))
  (f : ((i : I) → X i) → Y)
  (h : ∀ (xs xs' : (i : I) → X i), (∀ i, r i (xs i) (xs' i)) → f xs = f xs') : Y := sorry


def Expr.comp (f : Expr s ms k) (g : (i : Fin s) → Expr r ns (ms i)) : 
    Expr r ns k :=
  f.lift (fun frepr =>
    (Quot.liftForallOn g (fun gsrepr => 
      Quot.mk _ (.comp frepr gsrepr)) sorry_proof)) sorry_proof
    -- g.lift (fun grepr =>
    --   ⟦.comp frepr grepr⟧)
    --   (by intro a b h;
    --       apply (Equivalence.quot_mk_eq_iff sorry_proof _ _).2;
    --       simp[Expr.Repr.toLean,h]))
    -- (by intro a b h; simp; congr; funext gr;
    --     apply (Equivalence.quot_mk_eq_iff sorry_proof _ _).2;
    --     simp[Expr.Repr.toLean,h])
```
