open import Dijkstra.Algebra

module Dijkstra.Adjacency
       {c ℓ} (alg : DijkstraAlgebra c ℓ)
       where

open import Level

open import Data.Fin using (Fin)
open import Data.Matrix
open import Data.Nat.Base using (ℕ)

import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

open DijkstraAlgebra alg renaming (Carrier to Weight)

-- An adjacency matrix is a square matrix of weights whose diagonal
-- entries are equivalent to 1#
record Adj (n : ℕ) : Set (c ⊔ ℓ) where
  constructor _▦[_]
  field
    matrix : Matrix Weight n n
    diag   : ∀ i → (matrix [ i , i ]) ≈ 1#

-- Identity adjacency matrix
I : ∀ {n} → Adj n
I = matrix ▦[ diag ]
  where
    matrix : Matrix Weight _ _
    matrix = tabulate (diagonal 0# 1#)

    diag : ∀ i → (matrix [ i , i ]) ≈ 1#
    diag i = reflexive (P.trans (lookup∘tabulate i i) (diagonal-diag i))

-- Shorthand for identity matrix lookup
I[_,_] : ∀ {size} → Fin size → Fin size → Weight
I[ i , j ] = Adj.matrix I [ i , j ]
