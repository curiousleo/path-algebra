------------------------------------------------------------------------
-- Dijkstra correctness proof
--
-- Definition of an abstract version of Dijkstra's algorithm
------------------------------------------------------------------------

open import Algebra.Path.Structure
open import Data.Matrix.Adjacency

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)

module Dijkstra.Algorithm
    {c ℓ} (alg : PathAlgebra c ℓ)
    {n} (i : Fin (suc n)) (adj : Adj alg (suc n))
    where

open import Algebra.Path.Properties

open import Data.Fin.Subset
import Data.Fin.Subset.Extra as Sub
open import Data.Nat.MoreProperties using (≤-step′; sm∸n)
open import Data.Nat.Properties using (≤-step)
open import Data.Matrix
import Data.Vec as V
import Data.Vec.Sorted as Sorted

open import Function using (_$_)

open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (DecTotalOrder)
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

-- Bring the algebra's operators, constants and properties into scope
open PathAlgebra alg renaming (Carrier to Weight)
open RequiresPathAlgebra alg using (decTotalOrderᴸ)

-- This decidable total order is used to sort vertices by their
-- current estimate
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)

-- Shorthand for adjacency matrix lookup
A[_,_] : Fin (suc n) → Fin (suc n) → Weight
A[ i , j ] = Adj.matrix adj [ i , j ]

mutual

  -- Compares vertices by their current estimates
  order : (step : ℕ) {s≤n : step ≤ n} → DecTotalOrder _ _ _
  order step {s≤n} = estimateOrder $ estimate step {s≤n}

  -- Computes the estimated distance of j from i (the start vertex)
  estimate : (step : ℕ) {s≤n : step ≤ n} → Fin (suc n) → Weight
  estimate zero             j = A[ i , j ]
  estimate (suc step) {s≤n} j = r j + r q * A[ q , j ]
    where
      q = Sorted.head (order step {≤-step′ s≤n}) (queue step {s≤n})
      r = estimate step {≤-step′ s≤n}

  -- The set of visited vertices
  seen : (step : ℕ) {s≤n : step ≤ n} → Subset (suc n)
  seen zero             = ⁅ i ⁆
  seen (suc step) {s≤n} =
    seen step {≤-step′ s≤n} ∪
    ⁅ Sorted.head (order step {≤-step′ s≤n}) (queue step {s≤n}) ⁆

  -- The priority queue of yet unseen vertices. Its head has the lowest
  -- current distance estimate from the start vertex of all unseen vertices
  queue′ : (step : ℕ) {s≤n : step ≤ n} → Sorted.SortedVec _ (Sub.size $ ∁ $ seen step {s≤n})
  queue′ step {s≤n} = Sorted.fromVec (order step {s≤n}) $ Sub.toVec $ ∁ $ seen step

  -- Same queue, only the length index is rewritten to make it obvious that
  -- the queue contains at least one element (i.e. we can take the head)
  queue : (step : ℕ) {s≤n : suc step ≤ n} → Sorted.SortedVec _ (suc (n ∸ (suc step)))
  queue step {step<n} = P.subst (Sorted.SortedVec (order step {≤-step′ step<n})) (queue-size step {step<n}) (queue′ step)

  -- Any property of (queue step) is a property of (queue′ step)
  queue⇒queue′ : (step : ℕ) {s≤n : suc step ≤ n} → ∀ {p} (P : ∀ {n} →
                 Sorted.SortedVec _ n → Set p) → P (queue′ step) → P (queue step {s≤n})
  queue⇒queue′ step {s≤n} P Pqueue = super-subst P (≡-to-≅ (queue-size step {s≤n})) (H.sym H-lemma) Pqueue
    where
      open import Relation.Binary.HeterogeneousEquality as H
      open Sorted (order step {≤-step′ s≤n})

      super-subst : ∀ {m n p} → {xs : SortedVec m} → {ys : SortedVec n} →
                    (P : ∀ {n} → SortedVec n → Set p) → m H.≅ n → xs H.≅ ys → P xs → P ys
      super-subst P H.refl H.refl Pxs = Pxs

      H-lemma : queue step ≅ queue′ step
      H-lemma = ≡-subst-removable SortedVec (queue-size step {s≤n}) (queue′ step)

  -- In step step, (suc step) vertices have been visited
  seen-size : (step : ℕ) {s≤n : step ≤ n} → Sub.size (seen step {s≤n}) ≡ suc step
  seen-size zero             = Sub.size⁅i⁆≡1 i
  seen-size (suc step) {s≤n} =
    begin
      Sub.size (seen step ∪ ⁅ q ⁆)  ≡⟨ P.cong Sub.size (∪-comm (seen step) ⁅ q ⁆) ⟩
      Sub.size (⁅ q ⁆ ∪ seen step)  ≡⟨ Sub.size-suc q (seen step) (q∉seen step) ⟩
      suc (Sub.size (seen step))    ≡⟨ P.cong suc (seen-size step) ⟩
      suc (suc step)
    ∎
    where
      open P.≡-Reasoning
      open Sub.Properties (suc n)
      q = Sorted.head (order step {≤-step′ s≤n}) (queue step {s≤n})

  -- In step step, the size of the queue is (n ∸ step)
  queue-size : (step : ℕ) {s≤n : suc step ≤ n} → Sub.size (∁ (seen step {≤-step′ s≤n})) ≡ suc (n ∸ suc step)
  queue-size step {s≤n} =
    begin
      Sub.size (∁ (seen step))      ≡⟨ Sub.∁-size (seen step) ⟩
      suc n ∸ Sub.size (seen step)  ≡⟨ P.cong₂ _∸_ P.refl (seen-size step) ⟩
      suc n ∸ suc step              ≡⟨ sm∸n n (suc step) s≤n ⟩
      suc (n ∸ suc step)
    ∎
    where
      open P.≡-Reasoning

  -- The head of the queue has not yet been visited
  q∉seen : (step : ℕ) {s≤n : suc step ≤ n} → Sorted.head _ (queue step {s≤n}) ∉ seen step {≤-step′ s≤n}
  q∉seen step {s≤n} q∈vs = q∉q∷qs (S.here qs q≼qs)
    where
      module S = Sorted (order step {≤-step′ s≤n})

      q = S.head (queue step {s≤n})
      qs = S.tail (queue step {s≤n})
      q≼qs = S.≼-proof (queue step {s≤n})

      q∉queue′ : ¬ (q S.∈ (queue′ step))
      q∉queue′ = S.fromVec-∉¹ (Sub.toVec-∉¹ (Sub.∁-∈ q∈vs))

      q∉queue : ¬ (q S.∈ (queue step {s≤n}))
      q∉queue = queue⇒queue′ step {s≤n} (λ qs → ¬ (q S.∈ qs)) q∉queue′

      q∉q∷qs : ¬ (q S.∈ (q S.∷ qs ⟨ q≼qs ⟩))
      q∉q∷qs = P.subst (λ qs → ¬ (q S.∈ qs)) S.destruct q∉queue
