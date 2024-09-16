import SciLean
import ScientificComputingInLean.Meta

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000000

open SciLean

#doc (Manual) "Working with Quotients" =>

```lean (show:=false)
namespace WorkingWithQuotients
```

A common programming task is working with sets, which are collections of objects without any particular order. In practice, a simple way to handle small sets is to store the elements in a list (or array) and ensure no duplicates, while also making sure that functions on these lists do not rely on the order of the elements. However, typical programming languages do not enforce these invariants, and programmers must take extra care. One common trick is to keep the list sorted, which can reduce the likelihood of accidentally relying on element order. This approach, however, is limited, especially when working with elements that have no natural ordering, or when sorting is too costly.

In mathematics, one possible definition of a multiset is that it is a list of elements, but we impose an equivalence relation: two lists are equivalent if one is a permutation of the other. For example, `[1, 2, 3]` is equivalent to `[3, 2, 1]` but not to `[1, 2, 2]`. In this context, a multiset is the set of all lists that are permutations of each other—i.e., an equivalence class.  In Lean, we can work with such equivalence classes directly using **quotients**.

# Unordered Pair

Let’s start with a simpler example: unordered pairs of two natural numbers. Suppose we begin with an ordered pair `(a, b)` and define an equivalence relation such that `(a, b) ~ (c, d)` if either `a = c ∧ b = d` or `a = d ∧ b = c`.

We define the equivalence relation as follows:

```lean
def equiv : ℕ × ℕ → ℕ × ℕ → Prop :=
  fun (a, b) (c, d) => (a = c ∧ b = d) ∨ (a = d ∧ b = c)
```

Now we define an unordered pair as the quotient of `ℕ × ℕ` by this equivalence:

```lean
def UnorderedPair := Quot equiv
```

The `Quot` type constructor in Lean takes an equivalence relation `r : X → X → Prop` and creates a new type that represents the equivalence classes of `X` under this relation. Essentially, `Quot r` is a way to work with sets of equivalent values without dealing directly with the specific elements of these sets.

When working with quotients in Lean, it’s useful to understand how Lean manages equivalence classes. Internally, Lean treats each quotient type as if it stores just one representative from each equivalence class. However, unlike in some other programming languages, Lean enforces that any functions defined on these quotient types must be proven to be independent of the choice of representative. This means you must ensure that your functions produce consistent results regardless of which specific element of the equivalence class is used.


Let’s define a function that sums the elements of an unordered pair. In Lean, defining functions on quotients requires using `Quot.lift`, which lets you work with representatives while ensuring that the result is independent of which representative is chosen:

```lean
def UnorderedPair.sum (p : UnorderedPair) : Nat :=
  Quot.lift 
    (fun (a, b) => a + b) 
    (by 
      intro (a,b) (c,d); simp_all [equiv]; 
      intro h; cases h 
      case inl h => rw[h.left]; rw[h.right]
      case inr h => rw[h.left]; rw[h.right]; simp[add_comm]) 
    p
```

Here, `Quot.lift` takes three arguments: a function that works on representatives, `fun (a, b) => a + b`, a proof that the function respects the equivalence relation and an element of the quotient type `p`.

To create an element of a quotient, we use `Quot.mk`. For example, to construct an unordered pair:

```lean
#check Quot.mk equiv (1, 2)
```

::: TODO

Add functions
 - `UnorderedPair.toString`
 - `UnorderedPair.toStringRepr`
 - `UnorderedPair.normalizedRepr`

:::

# Symbolic Expressions

Let's explore a more intricate example involving symbolic expressions with free variables and a single binary operation. Our goal is to handle expressions in a way that respects mathematical properties such as associativity and the existence of a unit element.

We start by defining an inductive type `Expr` to represent these symbolic expressions:

```lean
inductive Expr where
  | one
  | var (n : Nat)
  | mul (x y : Expr)
deriving Repr
```

Here, `Expr` consists of three constructors:
- `one`, representing the multiplicative identity,
- `var n`, representing a variable with identifier `n`,
- `mul x y`, representing the multiplication of two expressions `x` and `y`.

We would like the multiplication to to be associative and `one` as multiplicative unit. Therefore we need to define equivalence relation on `Expr` that expresses this and then take an quotient of `Expr`. 

One way of defining this equivalence relation is to defined normalization function that takes and expression and normalizes it to an unique element. In this particular case, we remove all multiplications by `one` and right associate all multiplication. We achieve this by mapping `Expr` to `List Nat` and back:

```lean
def Expr.toList (e : Expr) : List Nat :=
  match e with
  | one => []
  | var n => [n]
  | mul x y => x.toList ++ y.toList

def Expr.ofList (l : List Nat) : Expr :=
  match l with
  | [] => .one
  | n :: ns => mul (.var n) (ofList ns)

def Expr.normalize (e : Expr) : Expr :=
  .ofList e.toList
```

For instance, the expression `mul (mul (var 0) (mul one (var 1))) (mul (var 2) (var 3))` normalizes to `mul (var 0) (mul (var 1) (mul (var 2) (mul (var 3) one)))`:

```lean
#eval Expr.mul (.mul (.var 0) (.mul .one (.var 1))) (.mul (.var 2) (.var 3))  
          |>.normalize
```


Instead of using `Quot` we will use `Quotient` which provides a better user experience. To use `Quotient` we have to provide an instance of `Setoid Expr` which attaches relation to `Expr` and proves that it is an equivalence:

```lean
instance ExprSetoid : Setoid Expr where
  r := fun x y => x.normalize = y.normalize
  iseqv := by 
    constructor
    · intro; rfl
    · intro _ _ h; rw[h]
    · intro _ _ _ h q; rw[h]; rw[q] 
```

Now we can define the quotinet of `Expr`:

```lean
def ExprMonoid := Quotient ExprSetoid
```

Based on the name, `ExprMonoid` forms mathematical monoid. To prove all the necessary monoid theorems we will need the that `Expr.ofList` is injective function:
```lean
theorem Expr.ofList_injective {l s : List ℕ} 
    (h : Expr.ofList l = Expr.ofList s) : l = s := 
  match l, s, h with
  | [], [], _ => rfl
  | l::ls, s::ss, h => by 
    simp_all [ofList]
    induction h
    rename_i h
    apply ofList_injective h
```

This lemma shows that if two lists `l` and `s` produce the same expression via `Expr.ofList`, then the lists themselves must be equal.


We can also prove that normalization of already normalized element does nothing:
```lean
theorem Expr.normalize_normalize (e : Expr) : 
    e.normalize.normalize = e.normalize := by
  unfold Expr.normalize
  induction e.toList
  · simp[Expr.ofList, Expr.toList]
  · simp_all[Expr.ofList, Expr.toList]
```

For ease of debugging and display, we define a function to convert expressions into strings:

```lean
def Expr.toString (e : Expr) : String :=
  match e with
  | .one => "1"
  | .mul x y => s!"({x.toString} * {y.toString})"
  | .var n => s!"#{n}"
```

This function provides a human-readable representation of an `Expr`.

## Monoid Structure of `ExprMonoid`

Using the quotient type `ExprMonoid`, we can show that it forms a monoid where multiplication is associative and has a unit element:

```lean
instance : Monoid ExprMonoid where
  mul x y := x.liftOn₂ y (fun x y => ⟦.mul x y⟧) 
    (by intro a b a' b' ha hb; dsimp
        apply Quotient.sound
        simp_all [HasEquiv.Equiv, Setoid.r, Expr.normalize, Expr.toList]
        have ha := Expr.ofList_injective ha
        have bh := Expr.ofList_injective hb
        congr)
  one := ⟦.one⟧
  mul_assoc := by
    intro a b c
    apply Quotient.ind (q:=c)
    apply Quotient.ind (q:=b)
    apply Quotient.ind (q:=a)
    intro a b c
    apply Quotient.sound
    simp_all only [HasEquiv.Equiv, Setoid.r, Expr.normalize, Expr.toList]
    apply congr_arg
    apply List.append_assoc
  one_mul := by
    intro a
    apply Quotient.ind (q:=a)
    intro a
    apply Quotient.sound
    simp_all only [HasEquiv.Equiv, Setoid.r, Expr.normalize, Expr.toList]
    apply congr_arg
    apply List.nil_append
  mul_one := by
    intro a
    apply Quotient.ind (q:=a)
    intro a
    apply Quotient.sound
    simp_all only [HasEquiv.Equiv, Setoid.r, Expr.normalize, Expr.toList]
    apply congr_arg
    apply List.append_nil
```

To define multiplication we used {name}`Quotient.liftOn₂` insteald of {name}`Quot.lift`. Also instead of {name}`Quot.mk` to create an element of quotient we used the notation `⟦·⟧`. The proofs are rather verbose on purpose so you can step through them step by step and get an idea what does it takes to prove properties when using quotients.


For debuging purposes we might want to print out an element of `ExprMonoid`. To maintain consistency of the system we have to print out the string representation of the normalized element:
```lean
def ExprMonoid.toString (e : ExprMonoid) : String := 
  e.liftOn (fun x => x.normalize.toString) 
    (by intro a b h 
        have h := Expr.ofList_injective h
        simp[Expr.normalize]
        congr)
```
Sometime we might also want to see the actual representant of `(e : ExprMonoid)`. We can accesse it with `Quotient.unquot` but this function is **unsafe** as it might produce different results for propositionally equal arguments i.e. an unsafe function `f` might for arguments `x` and `y` that are equail, `x = y`, produce different results `f x ≠ f y`.
```lean
unsafe def ExprMonoid.toStringRepr (e : ExprMonoid) : String := 
  e.unquot.toString
```
This function is very usefull for debuging but any function using it must be marked as **unsafe**.


Another useful function is one that normalizes the underlining representation:
```lean
def ExprMonoid.normalize (e : ExprMonoid) : ExprMonoid := 
  e.liftOn (fun x => ⟦x.normalize⟧) 
    (by intro a b h 
        have h := Expr.ofList_injective h
        simp[Expr.normalize]
        congr)
```

We can show that normalization does not change the actual mathematical element:

```lean
theorem ExprMonoid.normalize_eq (e : ExprMonoid) : e.normalize = e := by
  apply Quotient.ind (q:=e)
  intro x
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r]
  apply Expr.normalize_normalize
```

### Example Usage

```lean (keep := false)
def var (n : Nat) : ExprMonoid := ⟦.var n⟧
def e := var 0 * var 1 * 1 * 1 * var 0

-- show the mathematical element
#eval e.toString

-- show the underlining representation
#eval e.toStringRepr

-- show the underlining representation after normalization
#eval e.normalize.toStringRepr
```

This example demonstrates converting and normalizing symbolic expressions into their string representations, showcasing the power of quotients in Lean for maintaining mathematical invariants while managing complex symbolic data.


```lean (show:=false)
end WorkingWithQuotients
```
