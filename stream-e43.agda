open import Agda.Builtin.List
open import Codata.Stream
open import Data.Nat
open import Data.List.NonEmpty using (_∷_)
open import Size

-- valid sample
toss111 : Stream ℕ ∞
toss111 = cycle (1 ∷ 1 ∷ 1 ∷ [])

toss20 : Stream ℕ ∞
toss20 = cycle (2 ∷ 0 ∷ [])

toss153 : Stream ℕ ∞
toss153 = cycle (1 ∷ 5 ∷ 3 ∷ [])

toss2019 : Stream ℕ ∞
toss2019 = cycle (2 ∷ 0 ∷ 1 ∷ 9 ∷ [])

toss441 : Stream ℕ ∞
toss441 = cycle (4 ∷ 4 ∷ 1 ∷ [])


-- invalid sample
toss121 : Stream ℕ ∞
toss121 = cycle (1 ∷ 2 ∷ 1 ∷ [])

toss30 : Stream ℕ ∞
toss30 = cycle (3 ∷ 0 ∷ [])

toss135 : Stream ℕ ∞
toss135 = cycle (1 ∷ 3 ∷ 5 ∷ [])

toss2018 : Stream ℕ ∞
toss2018 = cycle (2 ∷ 0 ∷ 1 ∷ 8 ∷ [])
