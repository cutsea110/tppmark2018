
module e43 where

open import Data.List.NonEmpty
open import Data.Nat
open import Size
open import Codata.Stream
open import Relation.Binary.PropositionalEquality

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
air (Tossable ns ms prf) = suc (air ns)
seq (Tossable ns ms prf) = suc (air ms) ∷ record { force = seq ns }

open import Data.List
open import Data.List.NonEmpty

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
