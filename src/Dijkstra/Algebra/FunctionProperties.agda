open import Relation.Binary

module Dijkstra.Algebra.FunctionProperties
       {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Algebra.FunctionProperties _≈_ public

open import Data.Sum

Selective : Op₂ A → Set _
Selective _∙_ = ∀ x y → ((x ∙ y) ≈ x) ⊎ ((x ∙ y) ≈ y)
