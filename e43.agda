module e43 where

open import Data.List renaming (_∷_ to _∷~_)
open import Data.Nat
open import Data.Maybe renaming (nothing to ⟨⟩; just to ⟨_⟩)
open import Relation.Binary.PropositionalEquality hiding ([_])

data _⊢_ : Maybe ℕ → List ℕ → Set where
  Waiting   : {t : List ℕ}
    → ⟨⟩ ⊢ (t ++ [ 0 ]) → ⟨⟩ ⊢ (0 ∷~ t)
  FirstToss : {n : ℕ}{t : List ℕ}
    → ⟨ n ⟩ ⊢ (t ++ [ suc n ]) → ⟨⟩ ⊢ (suc n ∷~ t)
  CatchToss : {n : ℕ}{t : List ℕ}
    → ⟨ n ⟩ ⊢ (t ++ [ suc n ]) → ⟨ 0 ⟩ ⊢ (suc n ∷~ t)
  NotToss   : {n : ℕ}{t : List ℕ}
    → ⟨ n ⟩ ⊢ (t ++ [ 0 ]) → ⟨ suc n ⟩ ⊢ (0 ∷~ t)
  Tossable  : {n m : ℕ}{t : List ℕ}
    → ⟨ n ⟩ ⊢ (t ++ [ suc m ]) → ⟨ m ⟩ ⊢ (t ++ [ suc m ]) → (n≢m : n ≢ m) → ⟨ suc n ⟩ ⊢ (suc m ∷~ t)


-- valid sample
toss111 : ⟨⟩ ⊢ (1 ∷~ 1 ∷~ 1 ∷~ [])
toss111 = {!!}

toss20 : ⟨⟩ ⊢ (2 ∷~ 0 ∷~ [])
toss20 = {!!}

toss153 : ⟨⟩ ⊢ (1 ∷~ 5 ∷~ 2 ∷~ [])
toss153 = {!!}

toss2019 : ⟨⟩ ⊢ (2 ∷~ 0 ∷~ 1 ∷~ 9 ∷~ [])
toss2019 = {!!}

toss441 : ⟨⟩ ⊢ (4 ∷~ 4 ∷~ 1 ∷~ [])
toss441 = {!!}

-- invalid sample
toss121 : ⟨⟩ ⊢ (1 ∷~ 2 ∷~ 1 ∷~ [])
toss121 = {!!}

toss30 : ⟨⟩ ⊢ (3 ∷~ 0 ∷~ [])
toss30 = {!!}

toss135 : ⟨⟩ ⊢ (1 ∷~ 3 ∷~ 5 ∷~ [])
toss135 = {!!}

toss2018 : ⟨⟩ ⊢ (2 ∷~ 0 ∷~ 1 ∷~ 8 ∷~ [])
toss2018 = {!!}
