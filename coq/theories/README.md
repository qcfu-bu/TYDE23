# Calculus of Linear Constructions

## Sort relations

### Order
```
≤  U  L
U  T  T
L  F  T
```

### Addition
```
⋅  U  L
U  U  L
L  L  L
```

## Core typing rules

```
Γ ▹ U
————————————————
Γ ⊢ s@i :U U@i+1


Γ ▹ U    Γ ⊢ A :U s@i    [Γ, x :s A] ⊢ B :U r@i
———————————————————————————————————————————————
Γ ⊢ Πt (x :s A :r B) :U t@i


Γ ▹ U
———————————————————
Γ, x :s A ⊢ x :s A


Γ ▹ t     [Γ] ⊢ Πt (x :s A :r B) :U t@i     Γ, x :s A ⊢ n :r B
———————————————————————————————————————————————————————————————
Γ ⊢ λt (x :s A).n :t Πt (x :s A :r B)


Γ2 ▹ s    Γ1 ⊢ m :t Πt (x :s A :r B)     Γ2 ⊢ n :s A
—————————————————————————————————————————————————————
Γ1 ∘ Γ2 ⊢ m n :r B[n/x]


Γ ⊢ m :s A     [Γ] ⊢ B :U s@i     A ⪯ B
————————————————————————————————————————
Γ ⊢ m :s B
```

## Data typing rules
See formalization in [clc_typing.v](clc_typing.v) for details.
