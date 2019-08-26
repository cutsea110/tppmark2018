open import Agda.Builtin.List
open import Codata.Stream
open import Data.Maybe renaming (nothing to ⟨⟩; just to ⟨_⟩)
open import Data.Nat
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Size

record SiteSwap : Set where
  constructor fromList
  field
    tosses : List⁺ ℕ
  t = cycle tosses
  ∷~ = tail t

-- valid sample
toss111 : SiteSwap
toss111 = fromList (1 ∷ 1 ∷ 1 ∷ [])

toss20 : SiteSwap
toss20 = fromList (2 ∷ 0 ∷ [])

toss153 : SiteSwap
toss153 = fromList (1 ∷ 5 ∷ 3 ∷ [])

toss2019 : SiteSwap
toss2019 = fromList (2 ∷ 0 ∷ 1 ∷ 9 ∷ [])

toss441 : SiteSwap
toss441 = fromList (4 ∷ 4 ∷ 1 ∷ [])


-- invalid sample
toss121 : SiteSwap
toss121 = fromList (1 ∷ 2 ∷ 1 ∷ [])

toss30 : SiteSwap
toss30 = fromList (3 ∷ 0 ∷ [])

toss135 : SiteSwap
toss135 = fromList (1 ∷ 3 ∷ 5 ∷ [])

toss2018 : SiteSwap
toss2018 = fromList (2 ∷ 0 ∷ 1 ∷ 8 ∷ [])
