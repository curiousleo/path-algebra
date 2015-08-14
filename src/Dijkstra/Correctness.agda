------------------------------------------------------------------------
-- Dijkstra correctness proof
--
-- This file contains the proof that the abstract version of Dijkstra's
-- algorithm from Dijkstra.Algorithm computes the right-local solution
-- of one matrix row
------------------------------------------------------------------------

open import Algebra.Path.Structure
import Data.Matrix.Adjacency as Adj

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
  using (ℕ; zero; suc; z≤n)
  renaming (_≤_ to _N≤_)

module Dijkstra.Correctness
    {c ℓ} (alg : PathAlgebra c ℓ)
    {n} (i : Fin (suc n)) (adj : Adj.Adj alg (suc n))
    where

open import Algebra.Path.Properties
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
open PathAlgebra alg renaming (Carrier to Weight)
open RequiresPathAlgebra alg
open DecTotalOrder decTotalOrderᴸ using (_≤_)
open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
open import Dijkstra.Bigop +-commutativeMonoid
open EqR setoid

-- Partial right-local solution. This definition is suited for an
-- inductive proof (step by step)
pRLS : (step : ℕ) {s≤n : step N≤ n} → Pred (Fin (suc n)) _
pRLS step {s≤n} j = let r = estimate step {s≤n} in
  r j ≈ I[ i , j ] + (⨁[ k ← seen step {s≤n} ] r k * A[ k , j ])

-- Right-local solution. The aim is to prove that this holds for step = n
RLS : (step : ℕ) {s≤n : step N≤ n} → Pred (Fin (suc n)) _
RLS step {s≤n} j = let r = estimate step {s≤n} in
  r j ≈ I[ i , j ] + (⨁[ k ← ⊤ ] r k * A[ k , j ])

-- Inductive proof that Dijkstra's algorithm computes the partial
-- right-local solution
pcorrect : (step : ℕ) {s≤n : step N≤ n} → ∀ j → pRLS step {s≤n} j
pcorrect zero {s≤n} j with i FP.≟ j
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
    0#                 + A[ i , j ]        ≡⟨ P.cong₂ _+_ (P.sym diag) P.refl ⟩
    diagonal 0# 1# i j + A[ i , j ]        ≡⟨ P.cong₂ _+_ (P.sym l∘t) P.refl ⟩
    I[ i , j ]         + A[ i , j ]        ≈⟨ +-cong refl (sym (*-identityˡ _)) ⟩
    I[ i , j ]         + 1# * A[ i , j ]   ≈⟨ +-cong refl (*-cong (sym (Adj.diag adj i)) refl) ⟩
    I[ i , j ]         + r i * A[ i , j ]  ≈⟨ +-cong refl (sym fold) ⟩
    I[ i , j ]         + (⨁[ k ← ⁅ i ⁆ ] r k * A[ k , j ])
  ∎
  where
    r = estimate zero {z≤n}

    diag = diagonal-nondiag i j ¬i≡j
    l∘t = lookup∘tabulate {f = diagonal 0# 1#} i j
    fold = fold-⁅i⁆ (λ k → r k * A[ k , j ]) i

pcorrect (suc step) {s≤n} j =
  begin
    r′ j
  ≡⟨⟩
    r j + r q * A[ q , j ]
  ≈⟨ +-cong (pcorrect step {≤-step′ s≤n} j) refl ⟩
    (I[ i , j ] + (⨁[ k ← vs ] r k * A[ k , j ])) + r q * A[ q , j ]
  ≈⟨ +-assoc _ _ _ ⟩
    I[ i , j ] + ((⨁[ k ← vs ] r k * A[ k , j ]) + r q * A[ q , j ])
  ≈⟨ +-cong refl (+-cong fold (*-cong (sym (+-absorbs-* _ _)) refl)) ⟩
    I[ i , j ] + ((⨁[ k ← vs ] r′ k * A[ k , j ]) + r′ q * A[ q , j ])
  ≈⟨ +-cong refl (+-cong refl (sym (fold-⁅i⁆ f′ q))) ⟩
    I[ i , j ] + ((⨁[ k ← vs ] r′ k * A[ k , j ]) + (⨁[ k ← ⁅ q ⁆ ] r′ k * A[ k , j ]))
  ≈⟨ +-cong refl (sym (fold-∪ +-idempotent f′ (seen step) ⁅ q ⁆)) ⟩
    I[ i , j ] + (⨁[ k ← vs ∪ ⁅ q ⁆ ] r′ k * A[ k , j ])
  ≡⟨⟩
    I[ i , j ] + (⨁[ k ← seen (suc step) {s≤n} ] r′ k * A[ k , j ])
  ∎
  where
    r′ = estimate (suc step) {s≤n}
    r  = estimate step {≤-step′ s≤n}
    q  = Sorted.head _ (queue step {s≤n})
    f  = λ k → r k * A[ k , j ]
    f′ = λ k → r′ k * A[ k , j ]
    vs = seen step {≤-step′ s≤n}

    lemma : ∀ k → k ∈ vs → f k ≈ f′ k
    lemma k k∈vs = *-cong (sym (estimate-lemma step k k∈vs)) refl

    fold = fold-cong f f′ vs (λ k k∈vs → lemma k k∈vs)

-- Dijkstra's algorithm computes the right-local solution. This follows
-- directly from the inductive partial correctness proof above (pcorrect).
correct : ∀ j → RLS n {≤-refl} j
correct j = pRLS→RLS (pcorrect n j)
  where
    pRLS→RLS : ∀ {j} → pRLS n {≤-refl} j → RLS n {≤-refl} j
    pRLS→RLS {j} p =
      begin
        r j                                                        ≈⟨ p ⟩
        I[ i , j ] + (⨁[ k ← seen n {≤-refl} ] r k * A[ k , j ])  ≡⟨ lemma ⟩
        I[ i , j ] + (⨁[ k ← ⊤ ] r k * A[ k , j ])
      ∎
      where
        r = estimate n {≤-refl}

        seen-lemma = Sub.n→⊤ (seen n) (seen-size n)
        lemma = P.cong₂ _+_ P.refl (P.cong₂ ⨁-syntax P.refl seen-lemma)
