module tpp2018 where

open import Data.Bool hiding (_≟_; _≤?_; _≤_)
open import Data.Bool.Properties hiding (_≤?_; _≟_)
open import Data.Fin hiding (_+_; _≟_; _≤?_; _≤_)
open import Data.Empty
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_)
open import Data.Vec
open import Data.Vec.Properties
open import Data.Unit using (⊤; tt)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Nat

infix 3 _⇔_
_⇔_ : ∀ P Q → Set
p ⇔ q = (p → q) × (q → p)

1+m≤?1+n⇒m≤?n : (m n : ℕ) → True (m ≤? n) → True (suc m ≤? suc n)
1+m≤?1+n⇒m≤?n m n p with m ≤? n | suc m ≤? suc n
1+m≤?1+n⇒m≤?n m n tt | yes m≤n | yes 1+m≤1+n = tt
1+m≤?1+n⇒m≤?n m n tt | yes m≤n | no  1+m≰1+n = 1+m≰1+n (s≤s m≤n)

indexAt : {A : Set}{k : ℕ} → Vec A (suc k) → (n : ℕ) → A
indexAt {k = k} xs n = lookup xs (#_ (n % suc k) {n = suc k} {m<n = 1+m≤?1+n⇒m≤?n (n % suc k) k (help n k)})
  where
    help : ∀ m k → T ⌊ mod-helper 0 k m k ≤? k ⌋
    help m k with (m%n<n m k)
    help m k | s≤s p with mod-helper 0 k m k ≤? k
    help m k | s≤s p | yes q = tt
    help m k | s≤s p | no ¬q = ¬q p

valid1 : Vec ℕ 3
valid1 = 1 ∷ 1 ∷ 1 ∷ []

valid2 : Vec ℕ 2
valid2 = 2 ∷ 0 ∷ []

valid3 : Vec ℕ 3
valid3 = 1 ∷ 5 ∷ 3 ∷ []

valid4 : Vec ℕ 4
valid4 = 2 ∷ 0 ∷ 1 ∷ 9 ∷ []

invalid1 : Vec ℕ 3
invalid1 = 1 ∷ 2 ∷ 1 ∷ []

invalid2 : Vec ℕ 2
invalid2 = 3 ∷ 0 ∷ []

invalid3 : Vec ℕ 3
invalid3 = 1 ∷ 3 ∷ 5 ∷ []

invalid4 : Vec ℕ 4
invalid4 = 2 ∷ 0 ∷ 1 ∷ 8 ∷ []

injective : (f : ℕ → ℕ) → Set
injective f = (m n : ℕ) → f m ≡ f n → m ≡ n

phi : {k : ℕ} → Vec ℕ (suc k) → ℕ → ℕ
phi xs n = n + indexAt xs n

iota : (k : ℕ) → Vec ℕ k
iota k = tabulate toℕ

_notElem_ : {k : ℕ} → ℕ → Vec ℕ k → Bool
x notElem [] = true
x notElem (y ∷ ys) = not (x ≡ᵇ y) ∧ x notElem ys

unique : ∀ {k} → Vec ℕ k → Bool
unique [] = true
unique (x ∷ xs) = x notElem xs ∧ unique xs

data Valid : {k : ℕ} → Vec ℕ (suc k) → Set where
  valid : {k : ℕ} (xs : Vec ℕ (suc k)) → injective (phi xs) → Valid xs
  invalid : {k : ℕ} (xs : Vec ℕ (suc k)) → ¬ injective (phi xs) → Valid xs

isValid : {k : ℕ} → Vec ℕ (suc k) → Bool
isValid {k} xs = unique (zipWith (λ a i → (a + i) % suc k) xs (iota (suc k))) 

problem1 : ∀ k xs → isValid {k} xs ≡ true ⇔ Valid xs
problem1 k xs = {!!} , {!!}
