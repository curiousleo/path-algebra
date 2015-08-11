------------------------------------------------------------------------
-- Dijkstra correctness proof
--
-- Example of a shortest-path computation
------------------------------------------------------------------------

module Dijkstra.Example where

import Data.Matrix.Adjacency as Adj
open import Algebra.Path.Structure
open import Algebra.Path.Model
  renaming (ℕ∞-path-algebra to alg)
import Dijkstra.Algorithm as Algo

open import Data.Fin using (zero; suc)
open import Data.Nat as Nat
open import Data.Matrix as M
open import Data.Nat.InfinityExtension
open import Data.Vec as V

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Adj alg
open PathAlgebra alg renaming (Carrier to Weight)
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)

rls : ∀ {n} → Adj (suc n) → Matrix Weight (suc n) (suc n)
rls adj = M.tabulate (λ i → let open Algo alg i adj in estimate _ {≤-refl})

------------------------------------------------------------------------
-- Example 3×3 matrix

adj3 : Adj 3
adj3 = matrix ▦[ diag ]
  where
    matrix : Matrix Weight 3 3
    matrix =   (↑ 0 ∷ ↑ 4 ∷ ↑ 1 ∷ [])
             ∷ (∞   ∷ ↑ 0 ∷ ↑ 2 ∷ [])
             ∷ (↑ 1 ∷ ↑ 2 ∷ ↑ 0 ∷ [])
             ∷ []

    diag : ∀ i → matrix [ i , i ] ≈ ↑ 0
    diag zero             = refl
    diag (suc zero)       = refl
    diag (suc (suc zero)) = refl
    diag (suc (suc (suc ())))

rls-expected3 : Matrix Weight 3 3
rls-expected3 = (↑ 0 ∷ ↑ 3 ∷ ↑ 1 ∷ [])
              ∷ (↑ 3 ∷ ↑ 0 ∷ ↑ 2 ∷ [])
              ∷ (↑ 1 ∷ ↑ 2 ∷ ↑ 0 ∷ [])
              ∷ []

rls-correct3 : Pointwise _≡_ (rls adj3) rls-expected3
rls-correct3 = λ r c → refl

------------------------------------------------------------------------
-- Example 5×5 matrix

adj5 : Adj 5
adj5 = matrix ▦[ diag ]
  where
    matrix : Matrix Weight 5 5
    matrix =   (↑ 0 ∷ ↑ 1 ∷ ∞   ∷ ∞   ∷ ∞   ∷ [])
             ∷ (↑ 1 ∷ ↑ 0 ∷ ↑ 2 ∷ ↑ 1 ∷ ↑ 1 ∷ [])
             ∷ (∞   ∷ ↑ 2 ∷ ↑ 0 ∷ ↑ 1 ∷ ↑ 1 ∷ [])
             ∷ (∞   ∷ ↑ 1 ∷ ↑ 1 ∷ ↑ 0 ∷ ∞   ∷ [])
             ∷ (∞   ∷ ↑ 1 ∷ ↑ 1 ∷ ∞   ∷ ↑ 0 ∷ [])
             ∷ []

    diag : ∀ i → matrix [ i , i ] ≈ ↑ 0
    diag zero                         = refl
    diag (suc zero)                   = refl
    diag (suc (suc zero))             = refl
    diag (suc (suc (suc zero)))       = refl
    diag (suc (suc (suc (suc zero)))) = refl
    diag (suc (suc (suc (suc (suc ())))))
    
rls-expected5 : Matrix Weight 5 5
rls-expected5 = (↑ 0 ∷ ↑ 1 ∷ ↑ 3 ∷ ↑ 2 ∷ ↑ 2 ∷ [])
              ∷ (↑ 1 ∷ ↑ 0 ∷ ↑ 2 ∷ ↑ 1 ∷ ↑ 1 ∷ [])
              ∷ (↑ 3 ∷ ↑ 2 ∷ ↑ 0 ∷ ↑ 1 ∷ ↑ 1 ∷ [])
              ∷ (↑ 2 ∷ ↑ 1 ∷ ↑ 1 ∷ ↑ 0 ∷ ↑ 2 ∷ [])
              ∷ (↑ 2 ∷ ↑ 1 ∷ ↑ 1 ∷ ↑ 2 ∷ ↑ 0 ∷ [])
              ∷ []

{-
-- Gave up type-checking this after 30 minutes
rls-correct : Pointwise _≡_ (rls adj5) rls-expected5
rls-correct = λ r c → refl
-}
