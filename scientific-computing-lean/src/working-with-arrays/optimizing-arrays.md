# Optimizing Array Expressions

Lean is an interactive theorem prover. In this chapter, we will demonstrate how to use Lean as an interactive compiler or computer algebra system. We will focus on a common compiler optimization with arrays: loop fusion, which involves merging two loops into one. We will show how to craft such optimizations, explore them interactively, and discuss how to automate them.

Program optimization can be seen as rewriting a program into another program that is equivalent. By "equivalent," we mean that for the same input, these programs produce the same output. There is a close parallel to theorem proving. Often, to prove equality `x = y`, we simplify `x` to `x'` and `y` to `y'`. If `x'` is identical to `y'`, we have proven that `x = y`. Lean provides a general-purpose expression simplifier called `simp`, which has a database of rewrite rules and tries to apply them to subexpressions.

For example, in Lean, there is a theorem stating that adding zero does not change the value:
```lean
@[simp] theorem Nat.add_zero (n : Nat) : n + 0 = n := rfl
```
Adding the attribute `@[simp]` adds this theorem to the `simp` database of theorems it tries to apply.

We can simplify any expression `e` by using `e rewrite_by simp`:
```lean
#check (0 + 5 + 0) rewrite_by simp
```
This returns `5 : ℕ`, showing that all the zero additions have been eliminated. We can inspect what the simplifier did by turning on some options:
```lean
set_option trace.Meta.Tactic.simp.rewrite true in
#check (0 + 5 + 0) rewrite_by simp
```
This produces:
```
[Meta.Tactic.simp.rewrite] @zero_add:1000, 0 + 5 ==> 5
[Meta.Tactic.simp.rewrite] @add_zero:1000, 5 + 0 ==> 5
```
We can see that the simplifier first simplifies the subexpression `0 + 5` to `5` and then `5 + 0` to `5`.

The simplifier has many options and configurations. By default, `simp` uses all the theorems marked with `simp`. However, it is often useful to narrow it down to a specific set of theorems. You can do this by using `simp only`, which does not use any theorems at all, performing only basic lambda calculus reductions, like beta reduction, which turns `(fun x => f x) y` into `f y`. To explicitly specify a set of theorems to use, use square brackets:
```lean
#check (0 + 5 + 0) rewrite_by simp only [add_zero]
```
This produces `0 + 5`, as only the rewrite rule `add_zero` is allowed.


## Loop Fusion

This theorem illustrates the concept of loop fusion, which is relevant to program optimization. Consider the theorem:

```lean
theorem mapMono_mapMono {I} [IndexType I] (x : Float^[I]) (f g : Float → Float) :
    (x.mapMono f |>.mapMono g) = x.mapMono fun x => g (f x) := ...
```

This theorem shows that two `mapMono` operations can be fused into one. The function `mapMono` can be implemented with a for loop, so this theorem states that two for loops can be merged into one.

In numerical linear algebra, a common operation is computing `a•x+y` for `a : Float`, `x` and `y` of type `Float^[n]`. Scalar multiplication and addition on `Float^[n]` can be implemented using `mapMono`, which means that `a•x+y` contains two loops that can be fused together using the above theorem.

```lean
def saxpy {n} (a : Float) (x y : Float^[n]) := (a•x+y)
  rewrite_by
    simp only [HAdd.hAdd, Add.add, HSMul.hSMul, SMul.smul]
    simp only [mapMono_mapIdxMono]
```

The `saxpy` function computes `a•x+y`, and by adding `rewrite_by ...`, we rewrite `a•x+y` to:

```lean
x.mapIdxMono fun i x => a * x + y[i]
```

The first `simp only` command unfolds the definitions of all the arithmetic operations, revealing the use of `mapMono` and `mapIdxMono` used to implement arithmetic operations on arrays. The syntax `x + y` is just a syntactic sugar for `HAdd.hAdd x y`. If you want to see the actual definitions, you can add `set_option pp.notation false` somewhere in your file.

Sometimes, it's useful to keep the default or naive implementation of a function intact and only instruct the compiler to use the optimized version when compiling the code. This can be achieved using the `def_optimize` command.

For example, let's define a naive version of `saxpy`:

```lean
def saxpy_naive {n} (a : Float) (x y : Float^[n]) := a•x+y
```

To instruct the compiler to replace `saxpy_naive` with the optimized version, we use the `def_optimize` command:

```lean
def_optimize saxpy_naive by
  simp only [HAdd.hAdd, Add.add, HSMul.hSMul, SMul.smul]
  simp only [mapMono_mapIdxMono]
```

This command creates a new definition `saxpy_naive.optimized`, which is an optimized version of `saxpy_naive`. It also creates a new theorem called `saxpy_naive.optimize_rule`, which states that `saxpy_naive = saxpy_naive.optimized` and marks it with the `@[csimp]` attribute. The `csimp` attribute is similar to `simp`, but it stands for "compiler simp," and the corresponding theorems are only applied during compilation.



## Optimizing Array Indexing

Our approach to arrays, allowing indexing with an arbitrary type `I`, incurs a performance cost as the current Lean compiler can't optimize all layers of abstraction away. However, the flexibility of Lean enables us to engineer such optimizations ourselves without needing to modify the compiler.

Consider matrix-vector multiplication:

```lean
def matVecMul {n m} (A : Float^[n,m]) (x : Float^[m]) := ⊞ i => ∑ j, A[i,j] * x[j]
```

Recall that `Float^[n,m]` stands for `DataArrayN Float (Fin n × Fin m)`, a data structure indexed by `Fin n × Fin m`. The generic type `A × B` presents an issue because currently, any product type is implemented as a pair of pointers. Therefore, the index access `A[i,j]` first constructs the index `(i,j)`, which is a pair of pointers to `i` and `j`, stored somewhere on the heap. This is highly inefficient. We want to rewrite `A[i,j]` to `A.data.get (i*m+j)`, computing the linear index `i*m+j` and avoiding the construction of the product `(i,j)`.

```lean
def_optimize matVecMul by
  simp only [GetElem.getElem, LeanColls.GetElem'.get, DataArrayN.get, IndexType.toFin, id,
             Fin.pair, IndexType.fromFin, Fin.cast, IndexType.card]
```

This optimization results in:

```lean
⊞ i => ∑ j, A.data.get ⟨↑i * m + ↑j, ⋯⟩ * x.data.get ⟨↑j, ⋯⟩
```

The optimization simply forces the inlining of the mentioned functions. To simplify this process, there is a tactic `optimize_index_access` that calls `simp` with the appropriate settings and theorems.

Next, let's consider the dot product of two matrices:

```lean
def matDot {n m} (A B : Float^[n,m]) := ∑ (ij : Fin n × Fin m), A[ij] * B[ij]
```

Explicitly mentioning the type of the index `ij : Fin n × Fin m` highlights that this function again creates the problematic product type. We want to iterate this sum over the range `0,...,n*m-1` and use this linear index to access the matrices.

```lean
def_optimize matDot by
  rw[sum_linearize] -- rewrite `sum` over `Fin n × Fin m` to `fold` over `Fin (n*m)`
  simp only [GetElem.getElem, LeanColls.GetElem'.get, DataArrayN.get] -- unfold several layers of abstraction for `get` function
  simp only [toFin_fromFin] -- simplify `toFin (fromFin i)` to `i`
  simp only [Fin.cast, IndexType.card] -- clean up some expressions
```

This optimization results in:

```lean
∑ (i : Fin (n*m)), A.data.get ⟨↑i,⋯⟩ * B.data.get ⟨↑i,⋯⟩
```

This can also be achieved by calling the `optimize_index_access` tactic in a single line.

