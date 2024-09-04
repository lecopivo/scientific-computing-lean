import ScientificComputingInLean.Meta
import SciLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.hashCommand false
set_option linter.haveLet 0

set_option maxHeartbeats 1000000000

open Lean.MessageSeverity
open SciLean

#doc (Manual) "Derivative Rules" =>

# Basic Rules

Repeat again what needs to be done and state that it can be done with `def_fun_trans` and `def_fun_prop`

simple vs compositional form

# Rules with Conditions

How to state rules with condition on the arguments

# Higher Order Functions

How to state rules for higherder functions like

```lean
def applyTwice (f : X → X) (x : X) : X := f (f x)
```


# Recursive Functions

How to compute derivatives for recursive functions
```lean
def applyNTimes (n : Nat) (f : X → X) (x : X) : X := 
  match n with
  | 0 => x
  | n+1 => applyNTimes n f (f x)
```


# Custom Structures

How to define custom structure, add vector space structure and automatically generate all the rules for its projections.

Generating it for this structure should be easy
```lean
structure Float2 where
  (x y : Float)
```

This is more complicated
```lean
structure Vec2 (R : Type) [RCLike R] where
  (x y : R)

structure Vec2' (R : Type) where
  (x y : R)
```

This is really hard to do automatically
```lean
structure Sphere (R X : Type) [RCLike R] [NormedAddCommGroup X] [NormedSpace R X] where
  r : R
  c : X

structure Sphere' (R X : Type) where
  r : R
  c : X
```
