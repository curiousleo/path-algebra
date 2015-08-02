------------------------------------------------------------------------
-- Dijkstra correctness proof
--
-- Dijkstra algebra definition
------------------------------------------------------------------------

module Dijkstra.Algebra where

open import Algebra public
open import Algebra.Structures
open import Algebra.FunctionProperties as FunctionProperties
  using (Op₁; Op₂)
import Algebra.MoreFunctionProperties as MoreFunctionProperties

open import Data.Product
open import Function
open import Level
open import Relation.Binary

record IsDijkstraAlgebra {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                         (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  open MoreFunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ + 0#
    +-selective           : Selective +
    +-zero                : Zero 1# +

    *-identityˡ           : LeftIdentity 1# *
    *-cong                : * Preserves₂ ≈ ⟶ ≈ ⟶ ≈

    +-absorbs-*           : + Absorbs *

  open IsCommutativeMonoid +-isCommutativeMonoid public
         hiding (identityˡ)
         renaming ( assoc       to +-assoc
                  ; ∙-cong      to +-cong
                  ; isSemigroup to +-isSemigroup
                  ; identity    to +-identity
                  ; isMonoid    to +-isMonoid
                  ; comm        to +-comm
                  )


record DijkstraAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ
    _≟_              : Decidable _≈_
    _+_               : Op₂ Carrier
    _*_               : Op₂ Carrier
    0#                : Carrier
    1#                : Carrier
    isDijkstraAlgebra : IsDijkstraAlgebra _≈_ _+_ _*_ 0# 1#

  open IsDijkstraAlgebra isDijkstraAlgebra public

  decSetoid : DecSetoid c ℓ
  decSetoid =
    record
      { Carrier          = Carrier
      ; _≈_              = _≈_
      ; isDecEquivalence =
          record { isEquivalence = isEquivalence ; _≟_ = _≟_ }
      }

  +-commutativeMonoid : CommutativeMonoid _ _
  +-commutativeMonoid =
    record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _∙_ = _+_
      ; ε = 0#
      ; isCommutativeMonoid = +-isCommutativeMonoid
      }

  open CommutativeMonoid +-commutativeMonoid
    using (setoid)
    renaming (monoid to +-monoid) public
