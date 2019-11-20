module coinductive-tutorial where

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A

open Stream
open import Relation.Binary.PropositionalEquality

record _≈_ {A : Set} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd-≈ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl xs

even : ∀ {A} → Stream A → Stream A
hd (even x) = hd x
tl (even x) = even (tl (tl x))

odd : ∀ {A} → Stream A → Stream A
odd x = even (tl x)

open import Data.Product

split : ∀ {A} → Stream A → Stream A × Stream A
split xs =  even xs , odd xs

merge : ∀ {A} → Stream A × Stream A → Stream A
hd (merge (fst , snd)) = {!!}
tl (merge (fst , snd)) = {!!}

merge-split-id : ∀ {A} (xs : Stream A) → merge (split xs) ≈ xs
merge-split-id = {!!}