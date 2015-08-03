------------------------------------------------------------------------
-- Path algebra
--
-- Definition of an abstract version of the Bellman-Ford algorithm
------------------------------------------------------------------------

open import Dijkstra.Algebra
open import Dijkstra.Adjacency

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)

module BellmanFord.Algorithm
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    {n} (adj : Adj alg (suc n))
    where

open import Data.Fin.Subset using (⊤)
open import Data.Matrix using (_[_,_])

-- Bring the algebra's operators, constants and properties into scope
open DijkstraAlgebra alg renaming (Carrier to Weight)
open import Dijkstra.Bigop +-commutativeMonoid using (⨁-syntax)

-- Shorthand for adjacency matrix lookup
A[_,_] : Fin (suc n) → Fin (suc n) → Weight
A[ i , j ] = Adj.matrix adj [ i , j ]

-- Recursive version of Bellman-Ford
estimate : ℕ → (Fin (suc n)) → (Fin (suc n)) → Weight
estimate zero      i j = A[ i , j ]
estimate (suc ctd) i j = l i j + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))
  where l = estimate ctd
