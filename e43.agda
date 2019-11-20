module e43 where

open import Agda.Builtin.Nat using (mod-helper)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; T)
open import Data.Fin using (toℕ; fromℕ≤; #_)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; length; fromVec; toList; zipWith)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _+_; _≡ᵇ_)
open import Data.Nat.DivMod using (_%_; m%n<n)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; tabulate; fromList; lookup) renaming ([] to ⟨⟩; _∷_ to _∷̌_; [_] to ⟨_⟩)
open import Size using (∞)
open import Codata.Stream using (Stream; _∷_; head; tail; cycle)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; sym)
open _≡_
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True; False; ⌊_⌋)

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

indexAt : {A : Set}{k : ℕ} → Vec A (suc k) → (n : ℕ) → A
indexAt {k = k} xs n = lookup xs (#_ (n % suc k) {n = suc k} {m<n = 1+m≤?1+n⇒m≤?n (n % suc k) k (help n k)})
  where
    help : ∀ m k → T ⌊ mod-helper 0 k m k ≤? k ⌋
    help m k with (m%n<n m k)
    help m k | s≤s p with mod-helper 0 k m k ≤? k
    help m k | s≤s p | yes q = tt
    help m k | s≤s p | no ¬q = ¬q p

elementAt : {A : Set} (xs : List⁺ A) → (n : ℕ) → A
elementAt xs n = indexAt (fromList (toList xs)) n

phi : (xs : List⁺ ℕ) → (i : ℕ) → ℕ
phi xs i = i + elementAt xs i

injective : (f : ℕ → ℕ) → Set
injective f = (m n : ℕ) → f m ≡ f n → m ≡ n

iota : (n : ℕ) → (0<n : 0 < n) → List⁺ ℕ
iota (suc n) (s≤s 0<n) = fromVec {n = n} (tabulate toℕ)

_elem_ : ℕ → List ℕ → Bool
_ elem [] = false
z elem (x ∷ xs) = (z ≡ᵇ x) ∨ (z elem xs)

_elem⁺_ : ℕ → List⁺ ℕ → Bool
x elem⁺ xs = x elem (toList xs)

unique : List ℕ → Bool
unique [] = true
unique (_ ∷ []) = true
unique (x ∷ xs) = not (x elem xs) ∧ unique xs

unique⁺ : List⁺ ℕ → Bool
unique⁺ xs = unique (toList xs)

isValid : List⁺ ℕ → Bool
isValid xs = unique⁺ (zipWith (λ a i →  (a + i) % sz) xs (iota sz (s≤s z≤n)))
  where sz = length xs

data Valid : List⁺ ℕ → Set where
  valid : (xs : List⁺ ℕ) → injective (phi xs) → Valid xs

isValid⇒Valid : (xs : List⁺ ℕ) → isValid xs  ≡ true → Valid xs
isValid⇒Valid (x ∷ []) refl = valid (x ∷ []) {!!}
isValid⇒Valid (z ∷ x ∷ xs) prf = {!!}

Valid⇒isValid : (xs : List⁺ ℕ) → Valid xs → isValid xs  ≡ true
Valid⇒isValid (x ∷ xs) (valid .(x ∷ xs) prf) = {!!}

problem1 : (xs : List⁺ ℕ) → isValid xs ≡ true ⇔ Valid xs
problem1 xs = isValid⇒Valid xs , Valid⇒isValid xs

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
