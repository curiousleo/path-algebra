open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

module Dijkstra.EstimateOrder
  {c ℓ₁ ℓ₂}
  (ord : DecTotalOrder c ℓ₁ ℓ₂)
  where

open import Data.Fin using (Fin)
open import Data.Sum
open import Data.Vec

open import Function

open import Relation.Nullary

open DecTotalOrder ord renaming (Carrier to Weight)

estimateOrder : ∀ {n} (est : Fin n → Weight) → DecTotalOrder _ _ _
estimateOrder {n} est =
  record
    { Carrier         = Fin n
    ; _≈_             = _≈ᵉ_
    ; _≤_             = _≤ᵉ_
    ; isDecTotalOrder =
        record
          { isTotalOrder = isTotalOrderᵉ
          ; _≟_          = _≈ᵉ?_
          ; _≤?_         = _≤ᵉ?_
          }
    }
  where
    open IsEquivalence isEquivalence
      using ()
      renaming ( refl to ≈-refl
               ; sym to ≈-sym
               ; trans to ≈-trans
               )

    _≈ᵉ_ _≤ᵉ_ : Rel (Fin n) _
    _≈ᵉ_ = _≈_ on est
    _≤ᵉ_ = _≤_ on est

    _≈ᵉ?_ : Decidable _≈ᵉ_
    a ≈ᵉ? b = est a ≟ est b

    _≤ᵉ?_ : Decidable _≤ᵉ_
    a ≤ᵉ? b = est a ≤? est b

    totalᵉ : Total _≤ᵉ_
    totalᵉ a b with total (est a) (est b)
    ... | inj₁ estᵃ≤estᵇ = inj₁ estᵃ≤estᵇ
    ... | inj₂ estᵇ≤estᵃ = inj₂ estᵇ≤estᵃ

    isTotalOrderᵉ =
      record
        { isPartialOrder =
            record
              { isPreorder =
                  record
                    { isEquivalence =
                        record
                          { refl  = ≈-refl
                          ; sym   = ≈-sym
                          ; trans = ≈-trans
                          }
                    ; reflexive = reflexive
                    ; trans     = trans
                    }
              ; antisym = antisym
              }
        ; total = totalᵉ
        }
