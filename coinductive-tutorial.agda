{-# OPTIONS --guardedness #-}
module coinductive-tutorial where

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : Stream A

open Stream
open import Relation.Binary.PropositionalEquality

record _≈_ {A : Set} (xs : Stream A) (ys : Stream A) : Set where
  coinductive
  field
    hd-≈ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys

even : ∀ {A} → Stream A → Stream A
hd (even x) = hd x
tl (even x) = even (tl (tl x))

odd : ∀ {A} → Stream A → Stream A
odd x = even (tl x)

open import Data.Product

split : ∀ {A} → Stream A → Stream A × Stream A
split xs =  even xs , odd xs

merge : ∀ {A} → Stream A × Stream A → Stream A
hd (merge (fst , snd)) = hd fst
tl (merge (fst , snd)) = merge (snd , tl fst)

open _≈_

merge-split-id : ∀ {A} (xs : Stream A) → merge (split xs) ≈ xs
hd-≈ (merge-split-id _ ) = refl
tl-≈ (merge-split-id xs) = merge-split-id (tl xs)

uncons : ∀ {A} → Stream A → A × Stream A
uncons xs = hd xs , tl xs

cons : ∀ {A} → A × Stream A → Stream A
hd (cons (fst , snd)) = fst
tl (cons (fst , snd)) = snd

-- | ref.) https://stackoverflow.com/questions/59022907/how-can-i-prove-that-cons-after-uncons-over-coinductive-lista-k-a-stream-are-i
refl-≈ : ∀ {A} {xs : Stream A} → xs ≈ xs
hd-≈ refl-≈ = refl
tl-≈ refl-≈ = refl-≈

cons-uncons-id : ∀ {A} (xs : Stream A) → cons (uncons xs) ≈ xs
hd-≈ (cons-uncons-id _ ) = refl
tl-≈ (cons-uncons-id xs) = refl-≈

open import Data.Nat

ones : Stream ℕ
hd ones = 1
tl ones = ones

tl-ones-ones-id : tl ones ≈ ones
tl-ones-ones-id = refl-≈

-- ref.) http://www.cse.chalmers.se/~abela/talkFrankfurt2015.pdf
unfold : {S A : Set} → ((S → A) × (S → S)) → S → Stream A
hd (unfold (h , t) s) = h s
tl (unfold (h , t) s) = unfold (h , t) (t s)

open import Function using (_∘_)

map′ : ∀ {A B} → (A → B) → Stream A → Stream B
map′ f xs = unfold (f ∘ hd , tl) xs

from : ℕ → Stream ℕ
hd (from n) = n
tl (from n) = from (suc n)

nats : Stream ℕ
nats = from 0
