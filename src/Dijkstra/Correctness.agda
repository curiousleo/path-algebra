------------------------------------------------------------------------
-- Dijkstra correctness proof
--
-- This file contains the proof that the abstract version of Dijkstra's
-- algorithm from Dijkstra.Algorithm computes the right-local solution
-- of one matrix row
------------------------------------------------------------------------

open import Dijkstra.Algebra
import Dijkstra.Adjacency as Adj

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
  using (ℕ; zero; suc; z≤n)
  renaming (_≤_ to _N≤_)

module Dijkstra.Correctness
    {c ℓ} (alg : DijkstraAlgebra c ℓ)
    {n} (i : Fin (suc n)) (adj : Adj.Adj alg (suc n))
    where

open import Dijkstra.Algebra.Properties
open import Dijkstra.Algorithm alg i adj
open import Dijkstra.Properties alg i adj

open import Data.Fin.Properties as FP using (_≟_)
open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Matrix
open import Data.Nat.MoreProperties using (≤-step′)
open import Data.Nat.Properties using (≤-step)
open import Data.Product using (proj₁)
open import Data.Sum using (inj₁; inj₂)
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_; _≢_)
open P.≡-Reasoning
  using ()
  renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _■)

open Adj alg
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl)
open DijkstraAlgebra alg renaming (Carrier to Weight)
open RequiresDijkstraAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤_)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open import Dijkstra.Bigop +-commutativeMonoid
open EqR setoid

-- Partial right-local solution. This definition is suited for an
-- inductive proof (step by step)
pRLS : (ctd : ℕ) {lt : ctd N≤ n} → Pred (Fin (suc n)) _
pRLS ctd {lt} j = let r = estimate ctd {lt} in
  r j ≈ I[ i , j ] + (⨁[ k ← seen ctd {lt} ] (r k * A[ k , j ]))

-- Right-local solution. The aim is to prove that this holds for ctd = n
RLS : (ctd : ℕ) {lt : ctd N≤ n} → Pred (Fin (suc n)) _
RLS ctd {lt} j = let r = estimate ctd {lt} in
  r j ≈ I[ i , j ] + (⨁[ k ← ⊤ ] (r k * A[ k , j ]))

-- Inductive proof that Dijkstra's algorithm computes the partial
-- right-local solution
pcorrect : (ctd : ℕ) {lt : ctd N≤ n} → ∀ j → pRLS ctd {lt} j
pcorrect zero      {lt} j with i FP.≟ j
... | yes i≡j =
  begin
    r j             ≡⟨⟩
    A[ i , j ]      ≡⟨ P.cong₂ A[_,_] (P.refl {x = i}) j≡i ⟩
    A[ i , i ]      ≈⟨ Adj.diag adj i ⟩
    1#              ≈⟨ sym (proj₁ +-zero _) ⟩
    1#         + _  ≈⟨ +-cong (sym (Adj.diag I j)) refl ⟩
    I[ j , j ] + _  ≡⟨ P.cong₂ _+_ (P.cong₂ I[_,_] j≡i (P.refl {x = j})) P.refl ⟩
    I[ i , j ] + _
  ∎
  where
    r = estimate zero {z≤n}
    j≡i = P.sym i≡j

... | no ¬i≡j =
  begin
    A[ i , j ]                             ≈⟨ sym (proj₁ +-identity _) ⟩
    0#                 + A[ i , j ]        ≡⟨ P.cong₂ _+_ (P.sym (diagonal-nondiag i j ¬i≡j)) P.refl ⟩
    diagonal 0# 1# i j + A[ i , j ]        ≡⟨ P.cong₂ _+_ (P.sym (lookup∘tabulate {f = diagonal 0# 1#} i j)) P.refl ⟩
    I[ i , j ]         + A[ i , j ]        ≈⟨ +-cong refl (sym (*-identityˡ _)) ⟩
    I[ i , j ]         + 1# * A[ i , j ]   ≈⟨ +-cong refl (*-cong (sym (Adj.diag adj i)) refl) ⟩
    I[ i , j ]         + r i * A[ i , j ]  ≈⟨ +-cong refl (sym (fold-⁅i⁆ (λ k → r k * A[ k , j ]) i)) ⟩
    I[ i , j ]         + (⨁[ k ← ⁅ i ⁆ ] (r k * A[ k , j ]))
  ∎
  where
    r = estimate zero {z≤n}

pcorrect (suc ctd) {lt} j =
  begin
    r′ j
      ≡⟨⟩
    r j + r q * A[ q , j ]
      ≈⟨ +-cong (pcorrect ctd {≤-step′ lt} j) refl ⟩
    (I[ i , j ] + (⨁[ k ← vs ] (r k * A[ k , j ]))) + r q * A[ q , j ]
      ≈⟨ +-assoc _ _ _ ⟩
    I[ i , j ] + ((⨁[ k ← vs ] (r k * A[ k , j ])) + r q * A[ q , j ])
      ≈⟨ +-cong refl (+-cong (fold-cong f f′ vs (λ k k∈vs → lemma k k∈vs)) (*-cong (sym (+-absorbs-* _ _)) refl)) ⟩
    I[ i , j ] + ((⨁[ k ← vs ] (r′ k * A[ k , j ])) + r′ q * A[ q , j ])
      ≈⟨ +-cong refl (+-cong refl (sym (fold-⁅i⁆ f′ q))) ⟩
    I[ i , j ] + ((⨁[ k ← vs ] (r′ k * A[ k , j ])) + (⨁[ k ← ⁅ q ⁆ ] (r′ k * A[ k , j ])))
      ≈⟨ +-cong refl (sym (fold-∪ +-idempotent f′ (seen ctd) ⁅ q ⁆)) ⟩
    I[ i , j ] + (⨁[ k ← vs ∪ ⁅ q ⁆ ] (r′ k * A[ k , j ]))
      ≡⟨⟩
    I[ i , j ] + (⨁[ k ← seen (suc ctd) {lt} ] (r′ k * A[ k , j ]))
  ∎
  where
    r′ = estimate (suc ctd) {lt}
    r  = estimate ctd {≤-step′ lt}
    q  = Sorted.head _ (queue ctd {lt})
    f  = λ k → r k * A[ k , j ]
    f′ = λ k → r′ k * A[ k , j ]
    vs = seen ctd {≤-step′ lt}
    lemma : ∀ k → k ∈ vs → f k ≈ f′ k
    lemma k k∈vs = *-cong (sym (estimate-lemma ctd k k∈vs)) refl

-- Dijkstra's algorithm computes the right-local solution. This follows
-- directly from the inductive partial correctness proof above (pcorrect).
correct : ∀ j → RLS n {≤-refl} j
correct j = pRLS→RLS (pcorrect n j)
  where
    pRLS→RLS : ∀ {j} → pRLS n {≤-refl} j → RLS n {≤-refl} j
    pRLS→RLS {j} p =
      begin
        r j
          ≈⟨ p ⟩
        I[ i , j ] + (⨁[ k ← seen n {≤-refl} ] (r k * A[ k , j ]))
          ≡⟨ P.cong₂ _+_ P.refl (P.cong₂ ⨁-syntax P.refl (Sub.n→⊤ (seen n) (seen-size n))) ⟩
        I[ i , j ] + (⨁[ k ← ⊤ ] (r k * A[ k , j ]))
      ∎
      where
        r = estimate n {≤-refl}
