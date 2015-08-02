module Data.Nat.InfinityExtension.Properties where

open import Data.Empty
open import Data.Nat
  using (ℕ; zero; suc)
import Data.Nat as Nat
open import Data.Nat.InfinityExtension
import Data.Nat.MoreProperties as NP
open import Data.Nat.Properties using (strictTotalOrder)

open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Algebra.FunctionProperties (_≡_ {A = ℕ∞})
open import Algebra.MoreFunctionProperties (_≡_ {A = ℕ∞})

open StrictTotalOrder strictTotalOrder hiding (trans)

↑-injective : ∀ {a b} → ↑ a ≡ ↑ b → a ≡ b
↑-injective refl = refl

_≟∞_ : Decidable (_≡_ {A = ℕ∞})
↑ a ≟∞ ↑ b with a ≟ b
... | yes a≡b rewrite a≡b = yes refl
... | no ¬a≡b = no (λ ↑a≡↑b → ¬a≡b (↑-injective ↑a≡↑b))
↑ a ≟∞ ∞   = no (λ ())
∞   ≟∞ ↑ b = no (λ ())
∞   ≟∞ ∞   = yes refl

⊓-zeroˡ : LeftZero (↑ 0) _⊓_
⊓-zeroˡ (↑ m) = refl
⊓-zeroˡ ∞     = refl

⊓-zeroʳ : RightZero (↑ 0) _⊓_
⊓-zeroʳ (↑ zero)    = refl
⊓-zeroʳ (↑ (suc m)) = refl
⊓-zeroʳ ∞           = refl

⊓-zero : Zero (↑ 0) _⊓_
⊓-zero = ⊓-zeroˡ , ⊓-zeroʳ

+-identity : LeftIdentity (↑ 0) _+_
+-identity (↑ m) = refl
+-identity ∞     = refl

⊓-identityˡ : LeftIdentity ∞ _⊓_
⊓-identityˡ (↑ m) = refl
⊓-identityˡ ∞     = refl

⊓-comm : Commutative _⊓_
⊓-comm (↑ m) (↑ n) rewrite NP.⊓-comm m n = refl
⊓-comm (↑ m) ∞     = refl
⊓-comm ∞     (↑ n) = refl
⊓-comm ∞     ∞     = refl

⊓-selective : Selective _⊓_
⊓-selective (↑ m) (↑ n) with NP.⊓-selective m n
... | inj₁ p rewrite p = inj₁ refl
... | inj₂ p rewrite p = inj₂ refl
⊓-selective (↑ m) ∞     = inj₁ refl
⊓-selective ∞     (↑ n) = inj₂ refl
⊓-selective ∞     ∞     = inj₁ refl

⊓-assoc : Associative _⊓_
⊓-assoc (↑ m) (↑ n) (↑ o) rewrite NP.⊓-assoc m n o = refl
⊓-assoc (↑ m) (↑ n) ∞     = refl
⊓-assoc (↑ m) ∞     (↑ o) = refl
⊓-assoc (↑ m) ∞     ∞     = refl
⊓-assoc ∞     (↑ n) (↑ o) = refl
⊓-assoc ∞     (↑ n) ∞     = refl
⊓-assoc ∞     ∞     (↑ o) = refl
⊓-assoc ∞     ∞     ∞     = refl

⊓-absorbs-+ : _⊓_ Absorbs _+_
⊓-absorbs-+ (↑ m) (↑ n) rewrite NP.⊓-absorbs-+ m n = cong ↑ refl
⊓-absorbs-+ (↑ m) ∞     = refl
⊓-absorbs-+ ∞     n     = refl
