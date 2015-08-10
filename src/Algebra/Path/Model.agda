------------------------------------------------------------------------
-- Dijkstra correctness proof
--
-- A model Dijkstra algebra
------------------------------------------------------------------------

module Algebra.Path.Model where

open import Algebra.Path.Structure

open import Data.Nat.InfinityExtension
open import Data.Nat.InfinityExtension.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  hiding (cong)

-- Naturals extended with a point at infinity form a model of a DijkstraAlgebra.
ℕ∞-dijkstra-algebra : DijkstraAlgebra _ _
ℕ∞-dijkstra-algebra =
  record
  { Carrier = ℕ∞
  ; _≈_ = _≡_
  ; _≟_ = _≟∞_
  ; _+_ = _⊓_
  ; _*_ = _+_
  ; 0# = ∞
  ; 1# = ↑ 0
  ; isDijkstraAlgebra =
      record
      { +-isCommutativeMonoid =
          record
          { isSemigroup =
              record
              { isEquivalence = isEquivalence
              ; assoc = ⊓-assoc
              ; ∙-cong = cong₂ _⊓_
              }
          ; identityˡ = ⊓-identityˡ
          ; comm = ⊓-comm
          }
      ; +-selective = ⊓-selective
      ; +-zero = ⊓-zero
      ; *-identityˡ = +-identity
      ; *-cong = cong₂ _+_
      ; +-absorbs-* = ⊓-absorbs-+
      }
  }

-- The unit type equipped with degenerate _+_ and _*_ operations also satisfies the
-- axioms for a Dijkstra algebra:
unit-dijkstra-algebra : DijkstraAlgebra _ _
unit-dijkstra-algebra =
  record
  { Carrier = ⊤
  ; _≈_ = _≡_
  ; _≟_ = _≟_
  ; _+_ = _+ᵤ_
  ; _*_ = _+ᵤ_
  ; 0# = tt
  ; 1# = tt
  ; isDijkstraAlgebra =
    record
    { +-isCommutativeMonoid =
      record
      { isSemigroup =
        record
        { isEquivalence = isEquivalence
        ; assoc = assoc
        ; ∙-cong = cong
        }
      ; identityˡ = identityˡ
      ; comm = comm
      }
    ; +-selective = selective
    ; +-zero = zero
    ; *-identityˡ = identityˡ
    ; *-cong = cong
    ; +-absorbs-* = absorbs
    }
  }
  where
    open import Algebra.FunctionProperties (_≡_ {A = ⊤})
    open import Algebra.MoreFunctionProperties (_≡_ {A = ⊤})

    _+ᵤ_ : Op₂ ⊤
    u +ᵤ v = tt

    assoc : Associative _+ᵤ_
    assoc u v w = refl

    cong : _+ᵤ_ Preserves₂ _≡_ ⟶ _≡_ ⟶ _≡_
    cong prf₁ prf₂ = refl
    
    identityˡ : LeftIdentity tt _+ᵤ_
    identityˡ tt = refl

    comm : Commutative _+ᵤ_
    comm tt tt = refl

    selective : Selective _+ᵤ_
    selective tt tt = inj₁ refl

    zeroˡ : LeftZero tt _+ᵤ_
    zeroˡ tt = refl

    zeroʳ : RightZero tt _+ᵤ_
    zeroʳ tt = refl

    zero : Zero tt _+ᵤ_
    zero = zeroˡ , zeroʳ

    absorbs : _+ᵤ_ Absorbs _+ᵤ_
    absorbs tt tt = refl
