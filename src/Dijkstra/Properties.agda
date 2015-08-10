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

-- The set of visited vertices is never empty
seen-nonempty : (ctd : ℕ) {lt : ctd N≤ n} → Nonempty (seen ctd {lt})
seen-nonempty zero      = Sub.⁅i⁆-nonempty i
seen-nonempty (suc ctd) = Sub.∪-nonempty¹ _ _ (seen-nonempty ctd)

-- Any vertex contained in the set of vertices visited in step (suc ctd)
-- was either the head of the queue in step ctd or already in the set of
-- visited vertices in step ctd
seen-preserved : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ {j} → j ∈ seen (suc ctd) {lt} → j ≡ Sorted.head _ (queue ctd) ⊎ j ∈ seen ctd
seen-preserved ctd {lt} {j} j∈vs′ with Sub.∪-∈ j (seen ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈vs′
... | inj₁ j∈seen = inj₂ j∈seen
... | inj₂ j∈⁅q⁆  = inj₁ (Sub.i∈⁅i⁆′ _ _ j∈⁅q⁆)

private

  -- The head of the queue has the smallest estimated distance of any vertex
  -- that has not been visited so far
  q-lemma : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ k → k ∉ seen ctd {≤-step′ lt} →
            let r = estimate ctd {≤-step′ lt}
                q = Sorted.head _ (queue ctd {lt}) in
            r k + r q ≈ r q
  q-lemma ctd {lt} k k∉vs = rq⊴ᴸrk⟶rk+rq≈rq ⟨$⟩ S.head-≤ (∈-lemma k∉vs)
    where
      r = estimate ctd {≤-step′ lt}

      module S = Sorted (estimateOrder r)
      open DecTotalOrder (estimateOrder r)
        using () renaming (_≤_ to _≤ᵉ_)

      q = S.head (queue ctd {lt})

      ∈-lemma : ∀ {k} → k ∉ seen ctd {≤-step′ lt} → k S.∈ queue ctd {lt}
      ∈-lemma {k} k∉vs = queue⇒queue′ ctd {lt} (λ qs → k S.∈ qs) (∈-lemma′ k∉vs)
        where
          ∈-lemma′ : ∀ {k} → k ∉ seen ctd {≤-step′ lt} → k S.∈ queue′ ctd {≤-step′ lt}
          ∈-lemma′ k∉vs = S.fromVec-∈¹ (Sub.toVec-∈¹ (Sub.∁-∈′ k∉vs))

      open Equivalence (equivalentᴸ (r q) (r k)) renaming (from to rq⊴ᴸrk⟶rk+rq≈rq)

  -- If a vertex has not been visited in step (suc ctd) then it has not
  -- been visited in step ctd
  not-seen : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ k → k ∉ seen (suc ctd) {lt} →
             k ∉ seen ctd {≤-step′ lt}
  not-seen ctd {lt} k k∉vs′ k∈vs = k∉vs′ (Sub.∪-∈′ k _ _ k∈vs)

-- Once a node has been visited its estimate is optimal
pcorrect-lemma : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ j k →
                 let vs = seen ctd {≤-step′ lt}
                     r = estimate ctd {≤-step′ lt} in
                 j ∈ vs → k ∉ vs → r j + r k ≈ r j
pcorrect-lemma zero j k j∈vs k∉vs =
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

pcorrect-lemma (suc ctd) {lt} j k j∈vs′ k∉vs′ with Sub.∪-∈ {suc n} j (seen ctd) ⁅ Sorted.head _ (queue ctd) ⁆ j∈vs′

... | inj₁ j∈vs =
  begin
    r′ j + r′ k
      ≡⟨⟩
    (r j + r q * A[ q , j ]) + (r k + r q * A[ q , k ])
      ≈⟨ +-cong (+-comm _ _) refl ⟩
    (r q * A[ q , j ] + r j) + (r k + r q * A[ q , k ])
      ≈⟨ +-assoc _ _ _ ⟩
    r q * A[ q , j ] + (r j + (r k + r q * A[ q , k ]))
      ≈⟨ +-cong refl (sym (+-assoc _ _ _)) ⟩
    r q * A[ q , j ] + ((r j + r k) + r q * A[ q , k ])
      ≈⟨ +-cong refl (+-cong (pcorrect-lemma ctd {≤-step′ lt} j k j∈vs (not-seen ctd k k∉vs′)) refl) ⟩
    r q * A[ q , j ] + (r j + r q * A[ q , k ])
      ≈⟨ +-cong refl (+-cong (sym (pcorrect-lemma ctd {≤-step′ lt} j q j∈vs (q∉seen ctd))) refl) ⟩
    r q * A[ q , j ] + ((r j + r q) + r q * A[ q , k ])
      ≈⟨ +-cong refl (+-assoc _ _ _) ⟩
    r q * A[ q , j ] + (r j + (r q + r q * A[ q , k ]))
      ≈⟨ +-cong refl (+-cong refl (+-absorbs-* _ _)) ⟩
    r q * A[ q , j ] + (r j + r q)
      ≈⟨ +-cong refl (pcorrect-lemma ctd {≤-step′ lt} j q j∈vs (q∉seen ctd)) ⟩
    r q * A[ q , j ] + r j
      ≈⟨ +-comm _ _ ⟩
    r j + r q * A[ q , j ]
      ≡⟨⟩
    r′ j
  ∎
  where
    r  = estimate ctd {≤-step′ (≤-step′ lt)}
    r′ = estimate (suc ctd) {≤-step′ lt}
    q  = Sorted.head _ (queue ctd {≤-step′ lt})

... | inj₂ j∈⁅q⁆ =
  begin
    r′ j + r′ k
      ≡⟨⟩
    (r j + r q * A[ q , j ]) + (r k + r q * A[ q , k ])
      ≡⟨ P.cong₂ _+_ (P.cong₂ _+_ (P.cong r j≡q) P.refl) P.refl ⟩
    (r q + r q * A[ q , j ]) + (r k + r q * A[ q , k ])
      ≈⟨ +-cong (+-absorbs-* _ _) refl ⟩
    r q + (r k + r q * A[ q , k ])
      ≈⟨ sym (+-assoc _ _ _) ⟩
    (r q + r k) + r q * A[ q , k ]
      ≈⟨ +-cong (+-comm _ _) refl ⟩
    (r k + r q) + r q * A[ q , k ]
      ≈⟨ +-assoc _ _ _ ⟩
    r k + (r q + r q * A[ q , k ])
      ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
    r k + r q
      ≈⟨ q-lemma ctd {≤-step′ lt} k (not-seen ctd k k∉vs′) ⟩
    r q
      ≈⟨ sym (+-absorbs-* _ _) ⟩
    r q + r q * A[ q , j ]
      ≡⟨ P.cong₂ _+_ (P.cong r (P.sym j≡q)) P.refl ⟩
    r j + r q * A[ q , j ]
      ≡⟨⟩
    r′ j
  ∎
  where
    r  = estimate ctd {≤-step′ (≤-step′ lt)}
    r′ = estimate (suc ctd) {≤-step′ lt}
    q  = Sorted.head _ (queue ctd {≤-step′ lt})
    j≡q : j ≡ q
    j≡q = Sub.i∈⁅i⁆′ {suc n} q j j∈⁅q⁆

-- The distance estimate of a vertex stays the same once it has been visited
estimate-lemma : (ctd : ℕ) {lt : suc ctd N≤ n} → ∀ k → k ∈ seen ctd {≤-step′ lt} →
                 estimate (suc ctd) {lt} k ≈ estimate ctd {≤-step′ lt} k
estimate-lemma ctd {lt} k k∈vs =
  begin
    r′ k
      ≡⟨⟩
    r k + r q * A[ q , k ]
      ≈⟨ +-cong (sym (pcorrect-lemma ctd {lt} k q k∈vs (q∉seen ctd))) refl ⟩
    (r k + r q) + r q * A[ q , k ]
      ≈⟨ +-assoc _ _ _ ⟩
    r k + (r q + r q * A[ q , k ])
      ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
    r k + r q
      ≈⟨ pcorrect-lemma ctd {lt} k q k∈vs (q∉seen ctd) ⟩
    r k
  ∎
  where
    r  = estimate ctd {≤-step′ lt}
    r′ = estimate (suc ctd) {lt}
    q  = Sorted.head _ (queue ctd {lt})
