------------------------------------------------------------------------
-- Dijkstra correctness proof
--
-- Properties of Dijkstra's algorithm
------------------------------------------------------------------------

open import Algebra.Path.Structure
open import Data.Matrix.Adjacency

open import Data.Fin using (Fin)
open import Data.Nat
  using (ℕ; zero; suc)
  renaming (_≤_ to _N≤_)

module Dijkstra.Properties
    {c ℓ} (alg : PathAlgebra c ℓ)
    {n} (i : Fin (suc n)) (adj : Adj alg (suc n))
    where

open import Algebra.Path.Properties
open import Dijkstra.Algorithm alg i adj

open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Matrix
open import Data.Nat.MoreProperties using (≤-step′)
open import Data.Nat.Properties using (≤-step)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Vec as V
import Data.Vec.Properties as VP
import Data.Vec.Sorted as Sorted

open import Function using (_$_; _∘_; flip)
open import Function.Equivalence using (module Equivalence)
open import Function.Equality using (module Π)
open Π using (_⟨$⟩_)

open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.EqReasoning as EqR
import Relation.Binary.PropositionalEquality as P
open P using (_≡_; _≢_)
open P.≡-Reasoning
  using ()
  renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _■)

-- Bring the algebra's operators, constants and properties into scope
open PathAlgebra alg renaming (Carrier to Weight)
open RequiresPathAlgebra alg

-- This decidable total order is used to sort vertices by their
-- current estimate
open DecTotalOrder decTotalOrderᴸ using (_≤_)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)

-- Setoid reasoning for the PathAlgebra setoid
open EqR setoid

private

  -- The head of the queue has the smallest estimated distance of any vertex
  -- that has not been visited so far
  q-lemma : (step : ℕ) {s<n : suc step N≤ n} → ∀ k → k ∉ seen step {≤-step′ s<n} →
            let r = estimate step {≤-step′ s<n}
                q = Sorted.head _ (queue step {s<n}) in
            r k + r q ≈ r q
  q-lemma step {s<n} k k∉vs = rq⊴ᴸrk⟶rk+rq≈rq ⟨$⟩ S.head-≤ (∈-lemma k∉vs)
    where
      r = estimate step {≤-step′ s<n}

      module S = Sorted (estimateOrder r)
      open DecTotalOrder (estimateOrder r)
        using () renaming (_≤_ to _≤ᵉ_)

      q = S.head (queue step {s<n})

      ∈-lemma : ∀ {k} → k ∉ seen step {≤-step′ s<n} → k S.∈ queue step {s<n}
      ∈-lemma {k} k∉vs = queue⇒queue′ step {s<n} (λ qs → k S.∈ qs) (∈-lemma′ k∉vs)
        where
          ∈-lemma′ : ∀ {k} → k ∉ seen step {≤-step′ s<n} → k S.∈ queue′ step {≤-step′ s<n}
          ∈-lemma′ k∉vs = S.fromVec-∈¹ (Sub.toVec-∈¹ (Sub.∁-∈′ k∉vs))

      open Equivalence (equivalentᴸ (r q) (r k)) renaming (from to rq⊴ᴸrk⟶rk+rq≈rq)

  -- If a vertex has not been visited in step (suc step) then it has not
  -- been visited in step step
  not-seen : (step : ℕ) {s<n : suc step N≤ n} → ∀ k → k ∉ seen (suc step) {s<n} →
             k ∉ seen step {≤-step′ s<n}
  not-seen step {s<n} k k∉vs′ k∈vs = k∉vs′ (Sub.∪-∈′ k _ _ k∈vs)

-- Once a node has been visited its estimate is optimal
pcorrect-lemma : (step : ℕ) {s<n : suc step N≤ n} → ∀ {j k} →
                 let vs = seen step {≤-step′ s<n}
                     r = estimate step {≤-step′ s<n} in
                 j ∈ vs → k ∉ vs → r j + r k ≈ r j
pcorrect-lemma zero {j = j} j∈vs k∉vs =
  begin
    A[ i , j ] + _  ≈⟨ +-cong lemma refl ⟩
    1#         + _  ≈⟨ proj₁ +-zero _ ⟩
    1#              ≈⟨ sym lemma ⟩
    A[ i , j ]
  ∎
  where
    lemma : A[ i , j ] ≈ 1#
    lemma =
      begin
        A[ i , j ]  ≡⟨ P.cong₂ A[_,_] (P.refl {x = i}) (Sub.i∈⁅i⁆′ i j j∈vs) ⟩
        A[ i , i ]  ≈⟨ Adj.diag adj i ⟩
        1#
      ∎

pcorrect-lemma (suc step) {s<n} {j} {k} j∈vs′ k∉vs′
  with Sub.∪-∈ {suc n} j (seen step) ⁅ Sorted.head _ (queue step) ⁆ j∈vs′

... | inj₁ j∈vs =
  begin
    r′ j + r′ k                                          ≡⟨⟩
    (r j + r q * A[ q , j ]) + (r k + r q * A[ q , k ])  ≈⟨ +-cong (+-comm _ _) refl ⟩
    (r q * A[ q , j ] + r j) + (r k + r q * A[ q , k ])  ≈⟨ +-assoc _ _ _ ⟩
    r q * A[ q , j ] + (r j + (r k + r q * A[ q , k ]))  ≈⟨ +-cong refl lemma ⟩
    r q * A[ q , j ] + r j                               ≈⟨ +-comm _ _ ⟩
    r j + r q * A[ q , j ]                               ≡⟨⟩
    r′ j
  ∎
  where
    r  = estimate step {≤-step′ (≤-step′ s<n)}
    r′ = estimate (suc step) {≤-step′ s<n}
    q  = Sorted.head _ (queue step {≤-step′ s<n})

    pcorrect₁ = pcorrect-lemma step {≤-step′ s<n} j∈vs (not-seen step k k∉vs′)
    pcorrect₂ = pcorrect-lemma step {≤-step′ s<n} j∈vs (q∉seen step)
    pcorrect₃ = pcorrect-lemma step {≤-step′ s<n} j∈vs (q∉seen step)

    lemma : r j + (r k + r q * A[ q , k ]) ≈ r j
    lemma =
      begin
        r j + (r k + r q * A[ q , k ])  ≈⟨ sym (+-assoc _ _ _) ⟩
        (r j + r k) + r q * A[ q , k ]  ≈⟨ +-cong pcorrect₁ refl ⟩
        r j + r q * A[ q , k ]          ≈⟨ +-cong (sym pcorrect₂) refl ⟩
        (r j + r q) + r q * A[ q , k ]  ≈⟨ +-assoc _ _ _ ⟩
        r j + (r q + r q * A[ q , k ])  ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
        r j + r q                       ≈⟨ pcorrect₃ ⟩
        r j
      ∎

... | inj₂ j∈⁅q⁆ =
  begin
    r′ j + r′ k                                          ≡⟨⟩
    (r j + r q * A[ q , j ]) + (r k + r q * A[ q , k ])  ≡⟨ j≡q₁ ⟩
    (r q + r q * A[ q , j ]) + (r k + r q * A[ q , k ])  ≈⟨ +-cong (+-absorbs-* _ _) refl ⟩
    r q + (r k + r q * A[ q , k ])                       ≈⟨ sym (+-assoc _ _ _) ⟩
    (r q + r k) + r q * A[ q , k ]                       ≈⟨ +-cong (+-comm _ _) refl ⟩
    (r k + r q) + r q * A[ q , k ]                       ≈⟨ +-assoc _ _ _ ⟩
    r k + (r q + r q * A[ q , k ])                       ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
    r k + r q                                            ≈⟨ lemma ⟩
    r q                                                  ≈⟨ sym (+-absorbs-* _ _) ⟩
    r q + r q * A[ q , j ]                               ≡⟨ j≡q₂ ⟩
    r j + r q * A[ q , j ]                               ≡⟨⟩
    r′ j
  ∎
  where
    r  = estimate step {≤-step′ (≤-step′ s<n)}
    r′ = estimate (suc step) {≤-step′ s<n}
    q  = Sorted.head _ (queue step {≤-step′ s<n})
    j≡q : j ≡ q
    j≡q = Sub.i∈⁅i⁆′ {suc n} q j j∈⁅q⁆

    j≡q₁ = P.cong₂ _+_ (P.cong₂ _+_ (P.cong r j≡q) P.refl) P.refl
    j≡q₂ = P.cong₂ _+_ (P.cong r (P.sym j≡q)) P.refl
    lemma = q-lemma step {≤-step′ s<n} k (not-seen step k k∉vs′)

-- The distance estimate of a vertex stays the same once it has been visited.
-- This lemma is used in the correctness proof
estimate-lemma : (step : ℕ) {s<n : suc step N≤ n} → ∀ k → k ∈ seen step {≤-step′ s<n} →
                 estimate (suc step) {s<n} k ≈ estimate step {≤-step′ s<n} k
estimate-lemma step {s<n} k k∈vs =
  begin
    r′ k                            ≡⟨⟩
    r k + r q * A[ q , k ]          ≈⟨ +-cong (sym pcorrect) refl ⟩
    (r k + r q) + r q * A[ q , k ]  ≈⟨ +-assoc _ _ _ ⟩
    r k + (r q + r q * A[ q , k ])  ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
    r k + r q                       ≈⟨ pcorrect ⟩
    r k
  ∎
  where
    r  = estimate step {≤-step′ s<n}
    r′ = estimate (suc step) {s<n}
    q  = Sorted.head _ (queue step {s<n})

    pcorrect = pcorrect-lemma step {s<n} k∈vs (q∉seen step)

------------------------------------------------------------------------
-- Additional properties

-- The set of visited vertices is never empty
seen-nonempty : (step : ℕ) {s≤n : step N≤ n} → Nonempty (seen step {s≤n})
seen-nonempty zero      = Sub.⁅i⁆-nonempty i
seen-nonempty (suc step) = Sub.∪-nonempty¹ _ _ (seen-nonempty step)

-- Any vertex contained in the set of vertices visited in step (suc step)
-- was either the head of the queue in step step or already in the set of
-- visited vertices in step step
seen-preserved : (step : ℕ) {s<n : suc step N≤ n} → ∀ {j} → j ∈ seen (suc step) {s<n} → j ≡ Sorted.head _ (queue step) ⊎ j ∈ seen step
seen-preserved step {s<n} {j} j∈vs′ with Sub.∪-∈ j (seen step) ⁅ Sorted.head _ (queue step) ⁆ j∈vs′
... | inj₁ j∈seen = inj₂ j∈seen
... | inj₂ j∈⁅q⁆  = inj₁ (Sub.i∈⁅i⁆′ _ _ j∈⁅q⁆)
