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
  order : (ctd : ℕ) {lt : ctd ≤ n} → DecTotalOrder _ _ _
  order ctd {lt} = estimateOrder $ estimate ctd {lt}

  -- Computes the estimated distance of j from i (the start vertex)
  estimate : (ctd : ℕ) {lt : ctd ≤ n} → Fin (suc n) → Weight
  estimate zero              j = A[ i , j ]
  estimate (suc ctd) {ctd≤n} j = r j + r q * A[ q , j ]
    where
      q = Sorted.head (order ctd {≤-step′ ctd≤n}) (queue ctd {ctd≤n})
      r = estimate ctd {≤-step′ ctd≤n}

  -- The set of visited vertices
  seen : (ctd : ℕ) {lt : ctd ≤ n} → Subset (suc n)
  seen zero              = ⁅ i ⁆
  seen (suc ctd) {ctd≤n} =
    seen ctd {≤-step′ ctd≤n} ∪
    ⁅ Sorted.head (order ctd {≤-step′ ctd≤n}) (queue ctd {ctd≤n}) ⁆

  -- The priority queue of yet unseen vertices. Its head has the lowest
  -- current distance estimate from the start vertex of all unseen vertices
  queue′ : (ctd : ℕ) {lt : ctd ≤ n} → Sorted.SortedVec _ (Sub.size $ ∁ $ seen ctd {lt})
  queue′ ctd {lt} = Sorted.fromVec (order ctd {lt}) $ Sub.toVec $ ∁ $ seen ctd

  -- Same queue, only the length index is rewritten to make it obvious that
  -- the queue contains at least one element (i.e. we can take the head)
  queue : (ctd : ℕ) {lt : suc ctd ≤ n} → Sorted.SortedVec _ (suc (n ∸ (suc ctd)))
  queue ctd {ctd<n} = P.subst (Sorted.SortedVec (order ctd {≤-step′ ctd<n})) (queue-size ctd {ctd<n}) (queue′ ctd)

  -- Any property of (queue ctd) is a property of (queue′ ctd)
  queue⇒queue′ : (ctd : ℕ) {lt : suc ctd ≤ n} → ∀ {p} (P : ∀ {n} →
                 Sorted.SortedVec _ n → Set p) → P (queue′ ctd) → P (queue ctd {lt})
  queue⇒queue′ ctd {lt} P Pqueue = super-subst P (≡-to-≅ (queue-size ctd {lt})) (H.sym H-lemma) Pqueue
    where
      open import Relation.Binary.HeterogeneousEquality as H
      open Sorted (order ctd {≤-step′ lt})

      super-subst : ∀ {m n p} → {xs : SortedVec m} → {ys : SortedVec n} → (P : ∀ {n} → SortedVec n → Set p) →
                    m H.≅ n → xs H.≅ ys → P xs → P ys
      super-subst P H.refl H.refl Pxs = Pxs

      H-lemma : queue ctd ≅ queue′ ctd
      H-lemma = ≡-subst-removable SortedVec (queue-size ctd {lt}) (queue′ ctd)

  -- In step ctd, (suc ctd) vertices have been visited
  seen-size : (ctd : ℕ) {lt : ctd ≤ n} → Sub.size (seen ctd {lt}) ≡ suc ctd
  seen-size zero           = Sub.size⁅i⁆≡1 i
  seen-size (suc ctd) {lt} =
    begin
      Sub.size (seen ctd ∪ ⁅ q ⁆)  ≡⟨ P.cong Sub.size (∪-comm (seen ctd) ⁅ q ⁆) ⟩
      Sub.size (⁅ q ⁆ ∪ seen ctd)  ≡⟨ Sub.size-suc q (seen ctd) (q∉seen ctd) ⟩
      suc (Sub.size (seen ctd))    ≡⟨ P.cong suc (seen-size ctd) ⟩
      suc (suc ctd)
    ∎
    where
      open P.≡-Reasoning
      open Sub.Properties (suc n)
      q = Sorted.head (order ctd {≤-step′ lt}) (queue ctd {lt})

  -- In step ctd, the size of the queue is (n ∸ ctd)
  queue-size : (ctd : ℕ) {lt : suc ctd ≤ n} → Sub.size (∁ (seen ctd {≤-step′ lt})) ≡ suc (n ∸ suc ctd)
  queue-size ctd {lt} =
    begin
      Sub.size (∁ (seen ctd))      ≡⟨ Sub.∁-size (seen ctd) ⟩
      suc n ∸ Sub.size (seen ctd)  ≡⟨ P.cong₂ _∸_ P.refl (seen-size ctd) ⟩
      suc n ∸ suc ctd              ≡⟨ sm∸n n (suc ctd) lt ⟩
      suc (n ∸ suc ctd)
    ∎
    where
      open P.≡-Reasoning

  -- The head of the queue has not yet been visited
  q∉seen : (ctd : ℕ) {lt : suc ctd ≤ n} → Sorted.head _ (queue ctd {lt}) ∉ seen ctd {≤-step′ lt}
  q∉seen ctd {lt} q∈vs = q∉q∷qs (S.here qs q≼qs)
    where
      module S = Sorted (order ctd {≤-step′ lt})

      q = S.head (queue ctd {lt})
      qs = S.tail (queue ctd {lt})
      q≼qs = S.≼-proof (queue ctd {lt})

      q∉queue′ : ¬ (q S.∈ (queue′ ctd))
      q∉queue′ = S.fromVec-∉¹ (Sub.toVec-∉¹ (Sub.∁-∈ q∈vs))

      q∉queue : ¬ (q S.∈ (queue ctd {lt}))
      q∉queue = queue⇒queue′ ctd {lt} (λ qs → ¬ (q S.∈ qs)) q∉queue′

      q∉q∷qs : ¬ (q S.∈ (q S.∷ qs ⟨ q≼qs ⟩))
      q∉q∷qs = P.subst (λ qs → ¬ (q S.∈ qs)) S.destruct q∉queue
