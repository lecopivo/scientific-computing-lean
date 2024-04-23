# Optimizing Array Expressions

*Show how one can optimize array expressin*

- *explain how Lean can be used as interactive compiler*
- *simple BLAS oprations like `c = a*x + y` and turn it into `c = map x (fun i xi => a*xi + y[i]`*
- *issue with multidimensional indices and conversion to linear indices*



Lean is an interactive theorems prover and in this chapter we will show how to use Lean as interactive compiler/computer algebra system. An exmaple of common compiler optimization with arrays is loop fusion i.e. merging two loop into one. We will show how to craft such optimizations, expore them interactively and how to automate them. 

We can view program optimization as rerwiting a program into another program that is equal and by equal we mean that for the same input these programs produce the same output. There is a very close parallel to theorem proving. Very often to prove equality `x = y` we just simplify `x` to `x'` and `y` to `y'` and if `x'` happends to be identical to `y'` we have just proven that `x = y`. Lean provides a general pupose expression simplifier, called `simp`, which has a database of rewrite rules and tries to apply them to subexpression. 


For example, in Lean there is theorem that adding zero does not change the value. 
```
@[simp] theorem Nat.add_zero (n : Nat) : n + 0 = n := rfl
```
Adding this attribute `@[simp]` adds this theorem to the `simp`'s database of theorems it tries to apply. 

We can simplify any expression `e` by `e rewrite_by simp`
```
#check (0 + 5 + 0) rewrite_by simp
```
which returns `5 : ℕ` i.e. all the zero adition has been eliminated. We can actually inspect what did the simplifier did by turning on some options
```
set_option trace.Meta.Tactic.simp.rewrite true in
#check (0 + 5 + 0) rewrite_by simp
```
produces
```
[Meta.Tactic.simp.rewrite] @zero_add:1000, 0 + 5 ==> 5
[Meta.Tactic.simp.rewrite] @add_zero:1000, 5 + 0 ==> 5
```
So we can see that the simplifier first simplifies the subexpression `0 + 5` to `5` and then `5 + 0` to `5`.

The simplifier has many options and configurations. By default `simp` uses all the theorems marked with `simp`. Often it is usefull to narrow it down to only a specific set of theorems. You can call `simp only` which does not use any theorems at all, it just preforms basic lambda claclus reductions, like beta reduction which turns `(fun x => f x) y` to `f y`. To give explicit set of theorems to use use squared brackets `simp only [add_zero]`

```
#check (0 + 5 + 0) rewrite_by simp only [add_zero]
```
produces `0 + 5` as only the rewrite by `add_zero` is allowed. 



What does this have to do with programs optimization? Consider this theorem
```
theorem mapMono_mapMono {I} [IndexType I] (x : Float^[I]) (f g : Float → Float) :
    (x.mapMono f |>.mapMono g) = x.mapMono fun x => f (g x) := ...
```
which fuses two `mapMono` into one. 


Recall `softMax` from previous chapter
```
def softMax {I} [IndexType I]
  (r : Float) (x : Float^[I]) : Float^[I] := Id.run do
  let m := x.reduce (max · ·)
  let x := x.mapMono fun x => x-m
  let x := x.mapMono fun x => exp r*x
  let w := x.reduce (·+·)
  let x := x.mapMono fun x => x/w
  return x
```

We can defined "optimized" version 
```
def softMax_optimized {I} [IndexType I] (r : Float) (x : Float^[I]) := 
    (softMax r x) rewrite_by unfold softmax; simp only [mapMono_mapMono]
```
where we first unfold the definition of `softMax` by `unfold softMax` and then apply the theorem `mapMono_mapMono` through simplifier. If you plase cursor at the and of `simp only [mapMono_mapMono]` you will see the resulting expression
```
Id.run
    (pure
      (DataArrayN.mapMono x fun x_1 =>
        exp r *
            (x_1 /
              DataArrayN.reduce (DataArrayN.mapMono x fun x_2 => exp r * x_2 - DataArrayN.reduce x fun x x_3 => max x x_3)
                fun x x_2 => x + x_2) -
          DataArrayN.reduce x fun x x_2 => max x x_2))
```
This is a bit of an incomprehensible mess. The issue is that `simp` by default destroys let bindings. This is because `simp` was originally devised for simplifying expressions not programs. To keep let bindings intact we can turn on zeta reduction `(config:={zeta:=false})`


```
def softMax_optimized {I} [IndexType I] (r : Float) (x : Float^[I]) := 
    (softMax r x) rewrite_by unfold softmax; simp (config:={zeta:=false, }) only [mapMono_mapMono]
```
but now the theorem can't be applied as the let bindings are blocking it.

Dealing correctly with let bindings a tricky problem and right now we will just do it manually. We can call `let_unfold x` which will destroy the first let binding with the name `x`. 
```
def softMax_optimized {I} [IndexType I] (r : Float) (x : Float^[I]) := 
    (softMax r x) 
    rewrite_by 
      unfold softmax
      let_unfold x
      simp (config:={zeta:=false}) only [mapMono_mapMono]
```
The result is
```
Id.run
    (let m := x.reduce fun x x_1 => max x x_1;
    let x := x.mapMono fun x => exp r * x - m;
    let w := x.reduce fun x x_1 => x + x_1;
    let x := x.mapMono fun x => x / w;
    pure x)
```

...
