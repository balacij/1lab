<!--
```agda
open import 1Lab.Type.Sigma
open import 1Lab.Path
open import 1Lab.Type

open import Data.Product.NAry
open import Data.Maybe.Base
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Bool
open import Data.List.Base using (_∷_ ; [] ; _++_ ; List)

import Data.List as List

open import Meta.Traversable
open import Meta.Foldable
open import Meta.Append
open import Meta.Idiom
open import Meta.Bind
open import Meta.Alt
```
-->

```agda
module Data.Dequeue.Base where
```

<!--
```agda
private variable
  ℓ : Level
  A B : Type ℓ
```
-->


```agda
record Dequeue {ℓ} (A : Type ℓ) : Type ℓ where
    constructor queue
    field
        left : List A
        right : List A
```

```agda
to-list : Dequeue A → List A
to-list (queue ls rs) = ls ++ List.reverse rs

reverse : Dequeue A → Dequeue A 
reverse (queue ls rs) = queue rs ls

reverse-to-list : (xs : Dequeue A) → to-list (reverse xs) ≡ List.reverse (to-list xs)
reverse-to-list (queue ls rs) = 
    rs ++ List.reverse ls                             ≡˘⟨ ap (_++ List.reverse ls) (List.reverse-reverse rs) ⟩ 
    List.reverse (List.reverse rs) ++ List.reverse ls ≡˘⟨ List.reverse-++ ls (List.reverse rs) ⟩ 
    List.reverse (ls ++ List.reverse rs)              ∎

amortizel : Dequeue A → Dequeue A
amortizel q = queue (to-list q) []

amortizer : Dequeue A → Dequeue A
amortizer (queue ls rs) = queue [] (rs ++ List.reverse ls)
```

```agda
pushl : A → Dequeue A → Dequeue A
pushl e (queue ls rs) = queue (e ∷ ls) rs

snoc : Dequeue A → A → Dequeue A
snoc (queue ls rs) e = queue ls (e ∷ rs)
```

```agda
popl : A → Dequeue A → A × Dequeue A
popl e (queue (l ∷ ls) rs) = (l , queue ls rs)
popl e (queue [] rs) with List.reverse rs
... | [] = e , queue [] []
... | r ∷ rs = r , queue rs []

lemma
  : (def x : A) (xs : Dequeue A)
  → fst (popl def (pushl x xs)) ≡ x
lemma def x xs = refl

cool
  : (def x : A) (xs : Dequeue A)
  → (snd (popl def (pushl x xs))) ≡ xs
cool def x (queue ls rs) = refl

corollary : (def x : A) (dq : Dequeue A)
          → (popl def (pushl x dq)) ≡ (x , dq)
corollary _ _ _ = refl
```

```agda
popr : A → Dequeue A → Dequeue A × A
popr e (queue ls (x ∷ rs)) = queue ls rs , x
popr e (queue ls []) with List.reverse ls
... | [] = queue [] [] , e
... | l ∷ ls = queue [] ls , l
```


```agda
dropl : Dequeue A → Dequeue A
dropl (queue (_ ∷ ls) rs) = queue ls rs
dropl (queue [] rs) = queue (List.tail $ List.reverse rs) []

dropr : Dequeue A → Dequeue A
dropr (queue ls (_ ∷ rs)) = queue ls rs
dropr (queue ls []) = queue [] (List.tail $ List.reverse ls)
```
