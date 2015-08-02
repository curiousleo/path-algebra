module Data.Matrix where

open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ)
import Data.Vec as V
open V using (Vec)
import Data.Vec.Properties as VP
open import Function using (_∘_)
open import Function.Equivalence as Equiv using (_⇔_)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P
open P using (_≡_; _≢_)
open P.≡-Reasoning
import Relation.Binary.Vec.Pointwise as VP

infix 8 _[_,_]

------------------------------------------------------------------------
-- The type of r × c matrices over carrier type A

Matrix : ∀ {a} (A : Set a) → ℕ → ℕ → Set a
Matrix A r c = Vec (Vec A c) r

------------------------------------------------------------------------
-- Looking up values in a matrix

row : ∀ {r c a} {A : Set a} → Fin r → Matrix A r c → Vec A c
row = V.lookup

lookup : ∀ {r c a} {A : Set a} → Fin r → Fin c → Matrix A r c → A
lookup i j m = V.lookup j (row i m)

_[_,_] : ∀ {r c a} {A : Set a} → Matrix A r c → Fin r → Fin c → A
m [ i , j ] = lookup i j m

------------------------------------------------------------------------
-- Creating and manipulating matrices

tabulate : ∀ {r c a} {A : Set a} → (Fin r → Fin c → A) → Matrix A r c
tabulate f = V.tabulate (λ r → V.tabulate (λ c → f r c))

transpose : ∀ {r c a} {A : Set a} → Matrix A r c → Matrix A c r
transpose m = tabulate (λ c r → lookup r c m)

diagonal : ∀ {a m n} {A : Set a} → A → A → Fin m → Fin n → A
diagonal 0# 1# zero    zero    = 1#
diagonal 0# 1# zero    (suc c) = 0#
diagonal 0# 1# (suc r) zero    = 0#
diagonal 0# 1# (suc r) (suc c) = diagonal 0# 1# r c

------------------------------------------------------------------------
-- Tabulate is an inverse of (flip lookup)

lookup∘tabulate : ∀ {a n} {A : Set a} {f : Fin n → Fin n → A} r c →
                  lookup r c (tabulate f) ≡ f r c
lookup∘tabulate {f = f} r c = begin
  V.lookup c (V.lookup r (V.tabulate (V.tabulate ∘ f)))
    ≡⟨ P.cong (V.lookup c) (VP.lookup∘tabulate (V.tabulate ∘ f) r) ⟩
  V.lookup c (V.tabulate (f r))
    ≡⟨ VP.lookup∘tabulate (f r) c ⟩
  f r c ∎

------------------------------------------------------------------------
-- Pointwise lifting of a relation

Pointwise : ∀ {s t ℓ} {S : Set s} {T : Set t} (_∼_ : REL S T ℓ)
            {m n} → Matrix S m n → Matrix T m n → Set ℓ
Pointwise _~_ A B = ∀ r c → (A [ r , c ]) ~ (B [ r , c ])

------------------------------------------------------------------------
-- If _~_ is an equivalence then Pointwise _~_ is, too

PW-isEquivalence : ∀ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} {m n} →
                  IsEquivalence _~_ → IsEquivalence (Pointwise _~_ {m = m} {n})
PW-isEquivalence {_~_ = ~} eq = record { refl = PW-refl ; sym = PW-sym ; trans = PW-trans }
  where
    open IsEquivalence eq

    PW-refl : Reflexive (Pointwise ~)
    PW-refl = (λ r c → refl)

    PW-sym : Symmetric (Pointwise ~)
    PW-sym eq = (λ r c → sym (eq r c))

    PW-trans : Transitive (Pointwise ~)
    PW-trans eq₁ eq₂ = (λ r c → trans (eq₁ r c) (eq₂ r c))

------------------------------------------------------------------------
-- Sanity check: Pointwise is equivalent to lifting twice with
-- VP.Pointwise, the pointwise lifting of relations into vectors

private

  VP-equivalent : ∀ {ℓ} {S T : Set ℓ} {_~_ : REL S T ℓ} {m n}
                  {A : Matrix S m n} {B : Matrix T m n} →
                  VP.Pointwise (VP.Pointwise _~_) A B ⇔ Pointwise _~_ A B
  VP-equivalent {_~_ = _~_} {A = A} {B} = Equiv.equivalence to from
    where
      to : VP.Pointwise (VP.Pointwise _~_) A B → Pointwise _~_ A B
      to (VP.ext eq) = cong
        where
          cong : ∀ r c → (A [ r , c ]) ~ (B [ r , c ])
          cong r c with eq r
          cong r c | VP.ext eq′ = eq′ c

      from : Pointwise _~_ A B → VP.Pointwise (VP.Pointwise _~_) A B
      from eq = VP.ext (λ r → VP.ext (eq r))

------------------------------------------------------------------------
-- Diagonal creates a diagonal

diagonal-diag : ∀ {a n} {A : Set a} {0# : A} {1# : A} → (i : Fin n) → diagonal 0# 1# i i ≡ 1#
diagonal-diag zero    = P.refl
diagonal-diag (suc i) = diagonal-diag i

diagonal-nondiag : ∀ {a n} {A : Set a} {0# : A} {1# : A} (i j : Fin n) → i ≢ j → diagonal 0# 1# i j ≡ 0#
diagonal-nondiag zero zero i≢j = ⊥-elim (i≢j P.refl)
diagonal-nondiag zero (suc j) i≢j = P.refl
diagonal-nondiag (suc i) zero i≢j = P.refl
diagonal-nondiag (suc i) (suc j) si≢sj = diagonal-nondiag i j (≢-suc si≢sj)
  where
    ≢-suc : ∀ {n} {i j : Fin n} → suc i ≢ suc j → i ≢ j
    ≢-suc si≢sj i≡j = ⊥-elim (si≢sj (P.cong suc i≡j))
