module tpp2018 where

open import Data.Bool hiding (_≟_; _≤?_; _≤_)
open import Data.Bool.Properties hiding (_≤?_)
open import Data.Fin hiding (_+_; _≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Vec
open import Data.Unit using (⊤; tt)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat

1+m≤?1+n⇒m≤?n : (m n : ℕ) → True (m ≤? n) → True (suc m ≤? suc n)
1+m≤?1+n⇒m≤?n m n p with m ≤? n
1+m≤?1+n⇒m≤?n m n tt | yes m≤n with suc m ≤? suc n
1+m≤?1+n⇒m≤?n m n tt | yes m≤n | yes p = tt
1+m≤?1+n⇒m≤?n m n tt | yes m≤n | no ¬p = ¬p (s≤s m≤n)

indexAt : {A : Set}{k : ℕ}{k≥1 : k ≥ 1} → Vec A k → (n : ℕ) → A
indexAt {k = suc k} {k≥1 = s≤s k≥1} xs m
  = lookup xs (#_ (m % (suc k)) {n = suc k} {m<n = 1+m≤?1+n⇒m≤?n (m % suc k) k (help m k)})
  where
    help : ∀ m k → T ⌊ mod-helper 0 k m k ≤? k ⌋
    help m k with (m%n<n m k)
    help m k | s≤s p with mod-helper 0 k m k ≤? k
    help m k | s≤s p | yes q = tt
    help m k | s≤s p | no ¬q = ¬q p

ex1 : Vec ℕ 3
ex1 = 1 ∷ 1 ∷ 1 ∷ []

ex2 : Vec ℕ 2
ex2 = 2 ∷ 0 ∷ []

ex3 : Vec ℕ 3
ex3 = 1 ∷ 5 ∷ 3 ∷ []

ex4 : Vec ℕ 4
ex4 = 2 ∷ 0 ∷ 1 ∷ 9 ∷ []

isValid : {k : ℕ}{k≥1 : k ≥ 1}
  → (xs : Vec ℕ k) → (m n : ℕ) → m + (indexAt {k≥1 = k≥1} xs m) ≡ n + (indexAt {k≥1 = k≥1} xs n) → m ≡ n
isValid (x ∷ xs) m n prf = {!!}
