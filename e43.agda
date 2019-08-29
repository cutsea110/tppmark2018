module e43 where

open import Agda.Builtin.Nat using (_==_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; length; fromVec; toList)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_×_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; tabulate)
open import Size using (∞)
open import Codata.Stream using (Stream; _∷_; head; tail; cycle)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True; False)

infix 3 _⇔_
_⇔_ : ∀ P Q → Set
p ⇔ q = (p → q) × (q → p)

1+m≤?1+n⇒m≤?n : (m n : ℕ) → True (m ≤? n) → True (suc m ≤? suc n)
1+m≤?1+n⇒m≤?n m n p with m ≤? n | suc m ≤? suc n
1+m≤?1+n⇒m≤?n m n tt | yes m≤n | yes 1+m≤1+n = tt
1+m≤?1+n⇒m≤?n m n tt | yes m≤n | no  1+m≰1+n = 1+m≰1+n (s≤s m≤n)

_!_ : {A : Set} → Stream A ∞ → ℕ → A
s ! zero = head s
s ! suc i = tail s ! i

record Site∅ : Set where
  coinductive
  constructor ⊢_
  field
    seq : Stream ℕ ∞

record Site : Set where
  coinductive
  constructor _⊢_
  field
    air : ℕ
    seq : Stream ℕ ∞

open Site
open Site∅

Waiting : Site∅ → Site∅
seq (Waiting s) = 0 ∷ record { force = seq s }

FirstToss : Site → Site∅
seq (FirstToss s) = suc (air s) ∷ record { force = seq s }

CatchToss : Site → Site
air (CatchToss s) = 0
seq (CatchToss s) = suc (air s) ∷ record { force = seq s }

NotToss : Site → Site
air (NotToss s) = suc (air s)
seq (NotToss s) = 0 ∷ record { force = seq s }

Tossable : (ns : Site) → (ms : Site) → air ns ≢ air ms → Site
air (Tossable ns ms n≢m) = suc (air ns)
seq (Tossable ns ms n≢m) = suc (air ms) ∷ record { force = seq ns }

indexAt : {A : Set} (xs : List⁺ A) → (i : ℕ) → (i<len : i < length xs) → A
indexAt (x ∷ xs) zero i<len = x
indexAt (_ ∷ x ∷ xs) (suc i) (s≤s i<len) = indexAt (x ∷ xs) i i<len

phi : (xs : List⁺ ℕ) → (n : ℕ) → (n<len : n < length xs) → ℕ
phi = indexAt

injective : (f : ℕ → ℕ) → Set
injective f = (m n : ℕ) → f m ≡ f n → m ≡ n

iota : (n : ℕ) → (0<n : 0 < n) → List⁺ ℕ
iota (suc n) (s≤s 0<n) = fromVec {n = n} (tabulate toℕ)

_elem_ : ℕ → List ℕ → Bool
_ elem [] = false
z elem (x ∷ xs) = (z == x) ∨ (z elem xs)

_elem⁺_ : ℕ → List⁺ ℕ → Bool
x elem⁺ xs = x elem (toList xs)

unique : List ℕ → Bool
unique [] = true
unique (_ ∷ []) = true
unique (x ∷ xs) = not (x elem xs) ∧ unique xs

unique⁺ : List⁺ ℕ → Bool
unique⁺ xs = unique (toList xs)

isValid : List⁺ ℕ → Bool
isValid xs = {!!}

-- sample
module _  where
  to10 : List⁺ ℕ
  to10 = iota 10 (s≤s z≤n)

  -- valid
  toss111 : Site∅
  toss111 = ⊢ cycle (1 ∷ 1 ∷ 1 ∷ [])

  toss20 : Site∅
  toss20 = ⊢ cycle (2 ∷ 0 ∷ [])
  
  toss153 : Site∅
  toss153 = ⊢ cycle (1 ∷ 5 ∷ 3 ∷ [])

  toss2019 : Site∅
  toss2019 = ⊢ cycle (2 ∷ 0 ∷ 1 ∷ 9 ∷ [])

  toss441 : Site∅
  toss441 = ⊢ cycle (4 ∷ 4 ∷ 1 ∷ [])
  
  -- invalid
  toss121 : Site∅
  toss121 = ⊢ cycle (1 ∷ 2 ∷ 1 ∷ [])

  toss30 : Site∅
  toss30 = ⊢ cycle (3 ∷ 0 ∷ [])

  toss135 : Site∅
  toss135 = ⊢ cycle (1 ∷ 3 ∷ 5 ∷ [])

  toss2018 : Site∅
  toss2018 = ⊢ cycle (2 ∷ 0 ∷ 1 ∷ 8 ∷ [])
