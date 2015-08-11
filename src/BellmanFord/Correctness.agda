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

argmin : ∀ {n} → (xs : Subset n) → (sz : ℕ) → suc sz ≡ Sub.size xs → (f : Fin n → Weight) → ∃ λ i → i ∈ xs × f i ≈ (⨁[ j ← xs ] f j)
argmin [] sz () f
argmin (inside ∷ xs) zero eq f = zero , (here , {!!})
argmin (outside ∷ xs) zero eq f = let i , i∈xs , eq≈ = argmin xs zero eq (f ∘ suc ) in (suc i) , ({!!} , {!!})
argmin (inside ∷ xs) (suc sz) eq f = {!+-selective (f zero) (f (suc (proj₁ (argmin xs sz ? ?))))!}
argmin (outside ∷ []) (suc sz) () f
argmin (outside ∷ inside ∷ xs) (suc sz) eq f = let i , i∈xs , eq≈ = argmin xs sz {!eq!} (f ∘ Fin.suc ∘ suc) in
  {!!}
argmin (outside ∷ outside ∷ xs) (suc sz) eq f = {!!}

find-min : (ctd : ℕ) → ∀ i j →
           let l = estimate ctd in
           ∃ λ q → ∀ q′ → A[ i , q ] * l q j ≤ A[ i , q′ ] * l q′ j
find-min zero i j = i , λ q′ → 0# ,
  (begin
    A[ i , i ] * A[ i , j ]
     ≈⟨ {!!} ⟩
    A[ i , q′ ] * A[ q′ , j ] + 0#
  ∎)
find-min (suc ctd) i j = {!!}

path-relax : (ctd : ℕ) → {lt : ctd N≤ n} → ∀ i j →
             let l = estimate ctd in
             ∃ λ qs → (Sub.size qs ≡ suc ctd) × (⨁[ q ← qs ] (A[ i , q ] * l q j)) ≈
                                                (⨁[ q ← ⊤ ] (A[ i , q ] * l q j))
path-relax zero i j = ⁅ i ⁆ , Sub.size⁅i⁆≡1 i ,
  (begin
    (⨁[ q ← ⁅ i ⁆ ] (A[ i , q ] * A[ q , j ]))
      ≈⟨ {!!} ⟩
    A[ i , i ] * A[ i , j ]
      ≈⟨ {!!} ⟩
    1# * A[ i , j ]
      ≈⟨ {!Adj.diag!} ⟩
    A[ i , j ]
      ≈⟨ {!!} ⟩
    (⨁[ q ← ⊤ ] (A[ i , q ] * A[ q , j ]))
  ∎)
path-relax (suc ctd) {lt} i j = let qs , eq≡ , eq≈ = path-relax ctd {≤-step′ lt} i j in
  ⁅ {!!} ⁆ ∪ qs , ({!!} , {!!})

correct : ∀ n i j → LLS n i j
correct zero i j with i F.≟ j
... | yes i≡j = let l = estimate zero in
  begin
    A[ i , j ]
      ≡⟨ P.cong₂ A[_,_] (P.refl {x = i}) (P.sym i≡j) ⟩
    A[ i , i ]
      ≈⟨ Adj.diag adj i ⟩
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
... | no ¬i≡j = let l = estimate zero in
  begin
    A[ i , j ]
      ≈⟨ sym (proj₁ +-identity _) ⟩
    0# + A[ i , j ]
      ≡⟨ P.cong₂ _+_ (P.sym (diagonal-nondiag i j ¬i≡j)) P.refl ⟩
    diagonal 0# 1# i j + A[ i , j ]
      ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i j)) P.refl ⟩
    I[ i , j ] + A[ i , j ]
      ≈⟨ +-cong refl {!!} ⟩
    I[ i , j ] + (⨁[ q ← ⊤ ] (A[ i , q ] * A[ q , j ]))
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
    l′ = estimate (suc n)
    l  = estimate n

    lemma = λ q →
      begin
        l q j                  ≈⟨ correct n q j ⟩
        I[ q , j ] + _         ≈⟨ +-cong refl (sym (+-idempotent _)) ⟩
        I[ q , j ] + (_ + _)   ≈⟨ sym (+-assoc _ _ _) ⟩
        (I[ q , j ] + _) + _   ≈⟨ +-cong (sym (correct n q j)) refl ⟩
        l q j + (⨁[ t ← ⊤ ] (A[ q , t ] * l t j))
      ∎
