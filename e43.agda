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
