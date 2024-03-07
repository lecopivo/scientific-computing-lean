# Tensor Operatsions

*doing arithmetics on indices is a bit painful and commond practices and usefull tricks should be explained here*
*usage of `Fin n`, `ZMod n`, `Icc a b`*
*show implementation of convolution and many of its variants*



Matrix multiplication 
```lean
def matMul {n m : Nat} (A : Float^[n,m]) (x : Float^[m]) : Float^[n] :=
  ⊞ (i : Fin n) => ∑ j : Fin m, (A[i,j] : Float) * x[j]
```

Matrix norm
```lean
def matrixNorm {n m : Nat} (A : Float^[n,m]) : Float :=
  sqrt (∑ i j, A[i,j])
```


## Operations on Indices


1d convolution 
```lean
def Fin.shift (i : Fin n) (j : Nat) : Fin n := ⟨(i.1 + j)%n, sorry_proof⟩

def convolution {n m : Nat} (w : Float^[m]) (x : Float^[n]) : Float^[n] :=
  ⊞ i => ∑ j, (w[j] : Float) * x[i.shift j]
```

1d convolution 
```lean
def Fin.shift (i : Fin n) (j : Nat) : Fin n := ⟨(i.1 + j)%n, sorry_proof⟩

def convolution {n m : Nat} (w : Float^[m]) (x : Float^[n]) : Float^[n] :=
  ⊞ i => ∑ j, (w[j] : Float) * x[i.shift j]
```


## Physics Example

### Ricci decomposition
```lean
variable {n : Nat}
  (R : Float^[n,n,n,n])
  (g20 : Float^[n,n])
  (g02 : Float^[n,n])

def Ricci := ⊞ (j,k) => ∑ i l, (g20[i,l] : Float) * (R[i,j,k,l] : Float)
def Curvature := ∑ j k, (g20[j,k] : Float) * (Ricci R g20)[j,k]
def RicciTraceLess := (Ricci R g20) - (Curvature R g20/n) • g02
def S := ⊞ (i,j,k,l) => (Curvature R g20/(n*(n-1))) * ((g02[i,l] : Float) * (g02[j,k] : Float) - (g02[i,k] : Float) * (g02[j,l] : Float))
def E := ⊞ (i,j,k,l) =>
  let Z := RicciTraceLess R g20 g02
  (1.0/(n-2)) *  ((Z[i,l] : Float) * (g02[j,k] : Float)
                - (Z[j,l] : Float) * (g02[i,k] : Float)
                - (Z[i,k] : Float) * (g02[j,l] : Float)
                + (Z[j,k] : Float) * (g02[i,l] : Float))
def W := R + S R g20 g02 - E R g20 g02
```
