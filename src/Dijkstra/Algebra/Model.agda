------------------------------------------------------------------------
-- Dijkstra correctness proof
--
-- A model Dijkstra algebra
------------------------------------------------------------------------

module Dijkstra.Algebra.Model where

open import Dijkstra.Algebra

open import Data.Nat.InfinityExtension
open import Data.Nat.InfinityExtension.Properties
open import Data.Product

open import Relation.Binary.PropositionalEquality

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
