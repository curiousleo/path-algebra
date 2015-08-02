module Data.Nat.InfinityExtension where

open import Data.Nat
  using (ℕ; zero; suc)
import Data.Nat as Nat
open import Data.Sum

open import Relation.Binary.PropositionalEquality


-- Natural numbers extended with a `point at infinity'
data ℕ∞ : Set where
  ↑ : ℕ → ℕ∞
  ∞ : ℕ∞

_⊓_ : ℕ∞ → ℕ∞ → ℕ∞
_⊓_ (↑ m) (↑ n) = ↑ (m Nat.⊓ n)
_⊓_ (↑ m) ∞     = ↑ m
_⊓_ ∞     n     = n

_⊔_ : ℕ∞ → ℕ∞ → ℕ∞
↑ m ⊔ ↑ n = ↑ (m Nat.⊔ n)
↑ m ⊔ ∞   = ∞
∞   ⊔ n   = ∞

_+_ : ℕ∞ → ℕ∞ → ℕ∞
↑ m + ↑ n = ↑ (m Nat.+ n)
↑ m + ∞   = ∞
∞   + n   = ∞

_*_ : ℕ∞ → ℕ∞ → ℕ∞
↑ m * ↑ n = ↑ (m Nat.* n)
↑ m * ∞   = ∞
∞   * n   = ∞
