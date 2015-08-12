------------------------------------------------------------------------
-- Path algebra
--
-- Correctness proof of an abstract version of the Bellman-Ford
-- algorithm
------------------------------------------------------------------------

open import Algebra.Path.Structure
import Data.Matrix.Adjacency as Adj

open import Data.Fin using (Fin; zero; suc; inject₁)
open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _N≤_)

module BellmanFord.Correctness
    {c ℓ} (alg : PathAlgebra c ℓ)
    {n} (adj : Adj.Adj alg (suc n))
    where

open import Algebra.Path.Properties
open import BellmanFord.Algorithm alg adj

import Data.Fin.Properties as F
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Nat.MoreProperties using (≤-step′)
open import Data.Matrix
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Data.Vec using ([]; _∷_; here; there)

open import Function using (_∘_)

open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

open Adj alg

-- Bring the algebra's operators, constants and properties into scope
open PathAlgebra alg renaming (Carrier to Weight)
open RequiresPathAlgebra alg using (+-idempotent; decTotalOrderᴸ)
open DecTotalOrder decTotalOrderᴸ using (_≤_)
open import Dijkstra.Bigop +-commutativeMonoid
open EqR setoid

-- Recursive version of Bellman-Ford
{-
estimate : ℕ → (Fin (suc n)) → Weight
estimate zero      j = A[ i , j ]
estimate (suc ctd) j = l j + (⨁[ k ← ⊤ ] (A[ i , k ] * l k))
  where l = estimate ctd
-}

-- Left-local solution. The aim is to prove that this holds for ctd = n
LLS : ℕ → Fin (suc n) → Fin (suc n) → Set _
LLS ctd i j = let l = estimate ctd in
  l i j ≈ I[ i , j ] + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))

correct : ∀ n i j → LLS (suc n) i j
correct zero i j with i F.≟ j
... | yes i≡j = let l = estimate 1 in
  begin
    A[ i , j ] + _
      ≡⟨ P.cong₂ _+_ (P.cong₂ A[_,_] (P.refl {x = i}) (P.sym i≡j)) P.refl ⟩
    A[ i , i ] + _
      ≈⟨ +-cong (Adj.diag adj i) refl ⟩
    1# + _
      ≈⟨ proj₁ +-zero _ ⟩
    1#
      ≈⟨ sym (proj₁ +-zero _) ⟩
    1# + _
      ≡⟨ P.cong₂ _+_ (P.sym (diagonal-diag i)) P.refl ⟩
    diagonal 0# 1# i i + _
      ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i i)) P.refl ⟩
    I[ i , i ] + _
      ≡⟨ P.cong₂ _+_ (P.cong₂ I[_,_] (P.refl {x = i}) i≡j) P.refl ⟩
    I[ i , j ] + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))
  ∎
... | no ¬i≡j = let l = estimate 1 in
  begin
    A[ i , j ] + (⨁[ q ← ⊤ ] (A[ i , q ] * A[ q , j ]))
      ≈⟨ +-cong (sym (proj₁ +-identity _)) refl ⟩
    (0# + A[ i , j ]) + (⨁[ q ← ⊤ ] (A[ i , q ] * A[ q , j ]))
      ≡⟨ P.cong₂ _+_ (P.cong₂ _+_ (P.sym (diagonal-nondiag i j ¬i≡j)) P.refl) P.refl ⟩
    (diagonal 0# 1# i j + A[ i , j ]) + (⨁[ q ← ⊤ ] (A[ i , q ] * A[ q , j ]))
      ≡⟨ P.cong₂ _+_ (P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i j)) P.refl) P.refl ⟩
    (I[ i , j ] + A[ i , j ]) + (⨁[ q ← ⊤ ] (A[ i , q ] * A[ q , j ]))
      ≈⟨ {!!} ⟩
    I[ i , j ] + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))
  ∎
      
correct (suc n) i j =
  begin
    l i j + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))
      ≈⟨ +-cong (correct n i j) refl ⟩
    (I[ i , j ] + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))) + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))
      ≈⟨ +-assoc _ _ _ ⟩    
    I[ i , j ] + ((⨁[ q ← ⊤ ] (A[ i , q ] * l q j)) + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j)))
      ≈⟨ +-cong refl (+-idempotent _) ⟩
    I[ i , j ] + (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))
      ≈⟨ +-cong refl (fold-cong (λ q → A[ i , q ] * l q j) _ ⊤ (λ q _ → *-cong refl (lemma q))) ⟩
    I[ i , j ] + (⨁[ q ← ⊤ ] (A[ i , q ] * l′ q j))
  ∎
  where
    l′ = estimate (suc (suc n))
    l  = estimate (suc n)

    lemma = λ q →
      begin
        l q j                  ≈⟨ correct n q j ⟩
        I[ q , j ] + _         ≈⟨ +-cong refl (sym (+-idempotent _)) ⟩
        I[ q , j ] + (_ + _)   ≈⟨ sym (+-assoc _ _ _) ⟩
        (I[ q , j ] + _) + _   ≈⟨ +-cong (sym (correct n q j)) refl ⟩
        l q j + (⨁[ t ← ⊤ ] (A[ q , t ] * l t j))
      ∎
