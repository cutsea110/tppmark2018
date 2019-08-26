module stream-e43 where

open import Agda.Builtin.List
open import Codata.Stream
open import Data.Maybe renaming (nothing to ⟨⟩; just to ⟨_⟩)
open import Data.Nat
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Relation.Binary.PropositionalEquality
open import Size

infix 5 _∷~_

_∷~_ : {A : Set} → A → Stream A ∞ → Stream A ∞
x ∷~ xs = x ∷ record { force = xs }

infix 4 _⊢_

data _⊢_ : Maybe ℕ → Stream ℕ ∞ → Set where
  Waiting   : {t : Stream ℕ ∞} → ⟨⟩ ⊢ t → ⟨⟩ ⊢ 0 ∷~ t
  FirstToss : {n : ℕ}{t : Stream ℕ ∞} → ⟨ n ⟩ ⊢ t → ⟨⟩ ⊢ suc n ∷~ t
  CatchToss : {n : ℕ}{t : Stream ℕ ∞} → ⟨ n ⟩ ⊢ t → ⟨ 0 ⟩ ⊢ suc n ∷~ t
  NotToss   : {n : ℕ}{t : Stream ℕ ∞} → ⟨ n ⟩ ⊢ t → ⟨ suc n ⟩ ⊢ 0 ∷~ t
  Tossable  : {n m : ℕ}{t : Stream ℕ ∞} → ⟨ n ⟩ ⊢ t → ⟨ m ⟩ ⊢ t → (n≢m : n ≢ m) → ⟨ suc n ⟩ ⊢ suc m ∷~ t

-- valid sample
toss111 : List⁺ ℕ
toss111 = (1 ∷ 1 ∷ 1 ∷ [])

toss20 : List⁺ ℕ
toss20 = (2 ∷ 0 ∷ [])

toss153 : List⁺ ℕ
toss153 = (1 ∷ 5 ∷ 3 ∷ [])

toss2019 : List⁺ ℕ
toss2019 = (2 ∷ 0 ∷ 1 ∷ 9 ∷ [])

toss441 : List⁺ ℕ
toss441 = (4 ∷ 4 ∷ 1 ∷ [])


-- invalid sample
toss121 : List⁺ ℕ
toss121 = (1 ∷ 2 ∷ 1 ∷ [])

toss30 : List⁺ ℕ
toss30 = (3 ∷ 0 ∷ [])

toss135 : List⁺ ℕ
toss135 = (1 ∷ 3 ∷ 5 ∷ [])

toss2018 : List⁺ ℕ
toss2018 = (2 ∷ 0 ∷ 1 ∷ 8 ∷ [])
