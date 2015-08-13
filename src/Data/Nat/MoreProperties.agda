module Data.Nat.MoreProperties where

open import Data.Nat
open import Data.Nat.Properties using (≤-step; 0∸n≡0)
open import Data.Nat.Properties.Simple
open import Data.Sum

open import Function

open import Relation.Binary.PropositionalEquality

open import Algebra.FunctionProperties (_≡_ {A = ℕ})
open import Algebra.MoreFunctionProperties (_≡_ {A = ℕ})

⊓-comm : Commutative _⊓_
⊓-comm zero    zero    = refl
⊓-comm zero    (suc n) = refl
⊓-comm (suc m) zero    = refl
⊓-comm (suc m) (suc n) = cong ℕ.suc $ ⊓-comm m n

⊔-comm : Commutative _⊔_
⊔-comm zero    zero    = refl
⊔-comm zero    (suc n) = refl
⊔-comm (suc m) zero    = refl
⊔-comm (suc m) (suc n) = cong ℕ.suc $ ⊔-comm m n

⊓-assoc : Associative _⊓_
⊓-assoc zero    n       o       = refl
⊓-assoc (suc m) zero    o       = refl
⊓-assoc (suc m) (suc n) zero    = refl
⊓-assoc (suc m) (suc n) (suc o) = cong ℕ.suc $ ⊓-assoc m n o

⊔-assoc : Associative _⊔_
⊔-assoc zero    n       o       = refl
⊔-assoc (suc m) zero    o       = refl
⊔-assoc (suc m) (suc n) zero    = refl
⊔-assoc (suc m) (suc n) (suc o) = cong suc $ ⊔-assoc m n o

⊓-selective : Selective _⊓_
⊓-selective zero    n       = inj₁ refl
⊓-selective (suc m) zero    = inj₂ refl
⊓-selective (suc m) (suc n) with ⊓-selective m n
... | inj₁ p rewrite p = inj₁ refl
... | inj₂ p rewrite p = inj₂ refl

⊓-idempotent : Idempotent _⊓_
⊓-idempotent m with ⊓-selective m m
... | inj₁ p = p
... | inj₂ p = p

⊓-absorbs-+ : _⊓_ Absorbs _+_
⊓-absorbs-+ zero    n        = refl
⊓-absorbs-+ (suc m) zero
  rewrite +-right-identity m = cong suc $ ⊓-idempotent m
⊓-absorbs-+ (suc m) (suc n)  = cong suc $ ⊓-absorbs-+ m (suc n)

⊓-absorbs-⊔ : _⊓_ Absorbs _⊔_
⊓-absorbs-⊔ zero    n       = refl
⊓-absorbs-⊔ (suc m) zero    = cong suc (⊓-idempotent m)
⊓-absorbs-⊔ (suc m) (suc n) = cong suc (⊓-absorbs-⊔ m n)

⊔-identityˡ : LeftIdentity 0 _⊔_
⊔-identityˡ zero    = refl
⊔-identityˡ (suc m) = refl

-- More basic properties

suc-inj : ∀ {m n} → suc m ≤ suc n → m ≤ n
suc-inj {zero}  {n}     leq       = z≤n
suc-inj {suc m} {zero}  (s≤s ())
suc-inj {suc m} {suc n} (s≤s leq) = leq

sn∸n≡1 : ∀ n → suc n ∸ n ≡ 1
sn∸n≡1 zero    = refl
sn∸n≡1 (suc n) = sn∸n≡1 n

sm∸n : ∀ m n → n ≤ m → suc m ∸ n ≡ suc (m ∸ n)
sm∸n zero    .zero   z≤n       = refl
sm∸n (suc m) zero    n≤m       = refl
sm∸n (suc m) (suc n) (s≤s n≤m) = sm∸n m n n≤m

∸-assoc : ∀ m n o → n ≤ m → o ≤ n → m ∸ (n ∸ o) ≡ (m ∸ n) + o
∸-assoc zero    .zero   .zero   z≤n       z≤n       = refl
∸-assoc (suc m) zero    .zero   z≤n       z≤n       = cong suc (+-comm zero m)
∸-assoc (suc m) (suc n) zero    (s≤s n≤m) z≤n       = +-comm zero (m ∸ n)
∸-assoc (suc m) (suc n) (suc o) (s≤s n≤m) (s≤s o≤n) =
  start
    suc m ∸ (n ∸ o)    ≣⟨ sm∸n m (n ∸ o) (∸-≤-steps n m o n≤m) ⟩
    suc (m ∸ (n ∸ o))  ≣⟨ cong suc (∸-assoc m n o n≤m o≤n) ⟩
    suc ((m ∸ n) + o)  ≣⟨ sym (+-suc (m ∸ n) o) ⟩
    (m ∸ n) + suc o
  □
  where
    open ≡-Reasoning using () renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _□)

    ∸-≤-steps : ∀ m n o → m ≤ n → m ∸ o ≤ n
    ∸-≤-steps zero    n       o       m≤n rewrite 0∸n≡0 o = z≤n
    ∸-≤-steps (suc m) n       zero    m≤n = m≤n
    ∸-≤-steps (suc m) (suc n) (suc o) (s≤s m≤n) = ≤-step (∸-≤-steps m n o m≤n)

≤-step′ : ∀ {m n} → suc m ≤ n → m ≤ n
≤-step′ (s≤s leq) = ≤-step leq

≤-irrelevant : ∀ {m n} (leq : m ≤ n) (leq′ : m ≤ n) → leq ≡ leq′
≤-irrelevant z≤n       z≤n        = refl
≤-irrelevant (s≤s leq) (s≤s leq′) = cong s≤s (≤-irrelevant leq leq′)
