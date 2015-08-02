module Data.Fin.Subset.Extra where

open import Algebra
import Algebra.Properties.BooleanAlgebra as BA
open import Algebra.Structures

open import Data.Bool.Base hiding (true; false)
open import Data.Bool.Properties using () renaming (booleanAlgebra to Bool-booleanAlgebra)
open import Data.Empty using (⊥-elim)
open import Data.Fin hiding (_≤_)
open import Data.Fin.Subset renaming (booleanAlgebra to Subset-booleanAlgebra)
open import Data.List.Base as L hiding (length)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
import Data.Vec as V
open V using (Vec; []; _∷_; here; there)

open import Function using (_$_; _∘_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module Bool-BA = BA Bool-booleanAlgebra
open IsCommutativeSemiring Bool-BA.∨-∧-isCommutativeSemiring
  using ()
  renaming (+-identity to ∨-identity)

module Properties (n : ℕ) where
  open BA (Subset-booleanAlgebra n) using (∨-∧-isCommutativeSemiring)
  open IsCommutativeSemiring ∨-∧-isCommutativeSemiring public
    using ()
    renaming ( +-identity to ∪-identity
             ; +-comm to ∪-comm
             )

size : {n : ℕ} → Subset n → ℕ
size []             = 0
size (inside  ∷ xs) = suc (size xs)
size (outside ∷ xs) =      size xs

toVec : {n : ℕ} → (sub : Subset n) → Vec (Fin n) (size sub)
toVec []              = []
toVec (inside  ∷ sub) = zero ∷ V.map suc (toVec sub)
toVec (outside ∷ sub) =        V.map suc (toVec sub)

toList : {n : ℕ} → Subset n → List (Fin n)
toList []              = []
toList (inside  ∷ sub) = zero ∷ L.map suc (toList sub)
toList (outside ∷ sub) =        L.map suc (toList sub)

private
  length : ∀ {a} {A : Set a} {n} → Vec A n → ℕ
  length {n = n} _ = n

size-lemma : {n : ℕ} (sub : Subset n) → size sub ≡ length (toVec sub)
size-lemma []              = refl
size-lemma (inside  ∷ sub) = cong suc (size-lemma sub)
size-lemma (outside ∷ sub) = size-lemma sub

size⊥≡0 : ∀ {n} → size {n} ⊥ ≡ 0
size⊥≡0 {zero}  = refl
size⊥≡0 {suc n} = size⊥≡0 {n}

size⁅i⁆≡1 : ∀ {n} (i : Fin n) → size ⁅ i ⁆ ≡ 1
size⁅i⁆≡1 {suc n} zero = cong suc (size⊥≡0 {n})
size⁅i⁆≡1 (suc i) = size⁅i⁆≡1 i

size≤n : {n : ℕ} → (sub : Subset n) → size sub ≤ n
size≤n V.[] = z≤n
size≤n (inside V.∷ sub) = s≤s (size≤n sub)
size≤n (outside V.∷ sub) = ≤-step (size≤n sub)

private

  suc-inj : ∀ {i j} → ℕ.suc i ≡ suc j → i ≡ j
  suc-inj refl = refl

n→⊤ : {n : ℕ} → (sub : Subset n) → size sub ≡ n → sub ≡ ⊤
n→⊤ []              eq = refl
n→⊤ (inside  ∷ sub) eq = cong (_∷_ inside) (n→⊤ sub (suc-inj eq))
n→⊤ {suc n} (outside ∷ sub) eq = ⊥-elim (≤-contr eq (size≤n sub))
  where
    ≤-contr : ∀ {i j} → i ≡ suc j → ¬ i ≤ j
    ≤-contr {zero}  {j}     () leq
    ≤-contr {suc i} {zero}  eq ()
    ≤-contr {suc i} {suc j} eq (s≤s leq) = ≤-contr (suc-inj eq) leq

∈⊤ : {n : ℕ} → ∀ i → i ∈ (⊤ {n})
∈⊤ zero    = here
∈⊤ (suc i) = there (∈⊤ i)

∁-size : {n : ℕ} → (sub : Subset n) → size (∁ sub) ≡ n ∸ size sub
∁-size V.[]                      = refl
∁-size {suc n} (inside  V.∷ sub) = ∁-size sub
∁-size {suc n} (outside V.∷ sub) = trans (cong suc (∁-size sub)) (sym (+-∸-assoc 1 {n} {size sub} (size≤n sub)))

toList⊥ : {n : ℕ} → toList (⊥ {n}) ≡ []
toList⊥ {zero}  = refl
toList⊥ {suc n} = cong (L.map suc) toList⊥

toList⁅i⁆ : {n : ℕ} (i : Fin n) → toList ⁅ i ⁆ ≡ i ∷ []
toList⁅i⁆ {zero}  ()
toList⁅i⁆ {suc n} zero                        = cong₂ _∷_ refl toList⊥
toList⁅i⁆ {suc n} (suc i) rewrite toList⁅i⁆ i = refl

⁅i⁆-nonempty : {n : ℕ} (i : Fin n) → Nonempty ⁅ i ⁆
⁅i⁆-nonempty zero    = zero , here
⁅i⁆-nonempty (suc i) =
  let i , i∈⁅i⁆ = ⁅i⁆-nonempty i
  in suc i , there i∈⁅i⁆

∈∪ : {n : ℕ} (i : Fin n) (xs ys : Subset n) → i ∈ xs → i ∈ xs ∪ ys
∈∪ zero    (inside  ∷ xs) (y ∷ ys) here         = here
∈∪ zero    (outside ∷ xs) ys       ()
∈∪ (suc i) (x ∷ xs)       (y ∷ ys) (there i∈xs) = there (∈∪ i xs ys i∈xs)

∪-nonempty¹ : {n : ℕ} (xs ys : Subset n) → Nonempty xs → Nonempty (xs ∪ ys)
∪-nonempty¹ []             ys       (i , ())
∪-nonempty¹ (inside  ∷ xs) (y ∷ ys) (i , i∈xs)           = zero , here
∪-nonempty¹ (outside ∷ xs) (x ∷ ys) (zero , ())
∪-nonempty¹ (outside ∷ xs) (x ∷ ys) (suc i , there i∈xs) =
  let i , i∈xs = ∪-nonempty¹ xs ys (i , i∈xs)
  in suc i , there i∈xs

∪-nonempty² : {n : ℕ} (xs ys : Subset n) → Nonempty ys → Nonempty (xs ∪ ys)
∪-nonempty² {n} xs ys nonempty-ys = subst Nonempty (∪-comm ys xs) (∪-nonempty¹ ys xs nonempty-ys)
  where
    open Properties n

_∈?_ : ∀ {n} (i : Fin n) (xs : Subset n) → Dec (i ∈ xs)
zero ∈? (inside  ∷ xs) = yes here
zero ∈? (outside ∷ xs) = no (λ ())
suc i ∈? (x ∷ xs) with i ∈? xs
... | yes i∈xs = yes (there i∈xs)
... | no ¬i∈xs = no contradiction
  where
    contradiction : ¬ (suc i ∈ x ∷ xs)
    contradiction (there i∈xs) = ¬i∈xs i∈xs

size-suc : ∀ {n} (i : Fin n) (xs : Subset n) → i ∉ xs → size (⁅ i ⁆ ∪ xs) ≡ suc (size xs)
size-suc () [] i∉xs
size-suc zero (inside ∷ xs) i∉xs = ⊥-elim (i∉xs here)
size-suc {suc n} zero (outside ∷ xs) i∉xs =
  let open Properties n in cong (λ x → suc (size x)) (proj₁ ∪-identity xs)
size-suc (suc i) (inside  ∷ xs) si∉x∷xs = cong suc (size-suc i xs (si∉x∷xs ∘ there))
size-suc (suc i) (outside ∷ xs) si∉x∷xs = size-suc i xs (si∉x∷xs ∘ there)

∁-∈ : {n : ℕ} {i : Fin n} {xs : Subset n} → i ∈ xs → i ∉ (∁ xs)
∁-∈ {i = zero}  {.inside ∷ xs} here ()
∁-∈ {i = suc i} {x       ∷ xs} (there i∈xs) (there i∈∁xs) = ∁-∈ i∈xs i∈∁xs

∁-∈′ : {n : ℕ} {i : Fin n} {xs : Subset n} → i ∉ xs → i ∈ (∁ xs)
∁-∈′ {i = zero}  {inside  ∷ xs} i∉xs = ⊥-elim (i∉xs here)
∁-∈′ {i = zero}  {outside ∷ xs} i∉xs = here
∁-∈′ {i = suc i} {x ∷ xs}       i∉xs = there (∁-∈′ (i∉xs ∘ there))

∪-∈ : {n : ℕ} (i : Fin n) (xs ys : Subset n) → i ∈ xs ∪ ys → i ∈ xs ⊎ i ∈ ys
∪-∈ zero (inside  ∷ xs) (y ∷ ys) here = inj₁ here
∪-∈ zero (outside ∷ xs) (inside ∷ ys) here = inj₂ here
∪-∈ zero (outside ∷ xs) (outside ∷ ys) ()
∪-∈ (suc i) (x ∷ xs) (y ∷ ys) (there i∈) with ∪-∈ i xs ys i∈
∪-∈ (suc i) (x ∷ xs) (y ∷ ys) (there i∈) | inj₁ i∈xs = inj₁ (there i∈xs)
∪-∈ (suc i) (x ∷ xs) (y ∷ ys) (there i∈) | inj₂ i∈ys = inj₂ (there i∈ys)

∪-∈′ : {n : ℕ} (i : Fin n) (xs ys : Subset n) → i ∈ xs → i ∈ xs ∪ ys
∪-∈′ zero    (.inside ∷ xs) (y ∷ ys) here         = here
∪-∈′ (suc i) (x ∷ xs)       (y ∷ ys) (there i∈xs) = there (∪-∈′ i xs ys i∈xs)

private

  ∈-cong : {m n : ℕ} {i : Fin n} {xs : Vec (Fin n) m} → i V.∈ xs → Data.Fin.suc i V.∈ V.map suc xs
  ∈-cong here         = here
  ∈-cong (there i∈xs) = there (∈-cong i∈xs)

  toVec-∈-lemma¹ : {n : ℕ} (i : Fin n) (xs : Vec Bool n) → i ∈ xs → Data.Fin.suc i V.∈ V.map suc (toVec xs)
  toVec-∈-lemma¹ zero    (.inside ∷ xs) here         = here
  toVec-∈-lemma¹ (suc i) (inside  ∷ xs) (there i∈xs) = ∈-cong (there (toVec-∈-lemma¹ i xs i∈xs))
  toVec-∈-lemma¹ (suc i) (outside ∷ xs) (there i∈xs) = ∈-cong (toVec-∈-lemma¹ i xs i∈xs)

toVec-∈¹ : {n : ℕ} {i : Fin n} {xs : Subset n} → i ∈ xs → i V.∈ (toVec xs)
toVec-∈¹ {i = zero}  {.inside ∷ xs} here         = here
toVec-∈¹ {i = suc i} {inside  ∷ xs} (there i∈xs) = there (toVec-∈-lemma¹ i xs i∈xs)
toVec-∈¹ {i = suc i} {outside ∷ xs} (there i∈xs) = toVec-∈-lemma¹ i xs i∈xs

i∈⁅i⁆ : {n : ℕ} (i : Fin n) → i ∈ ⁅ i ⁆
i∈⁅i⁆ zero = here
i∈⁅i⁆ (suc i) = there (i∈⁅i⁆ i)

i∉⊥ : {n : ℕ} (i : Fin n) → i ∉ ⊥
i∉⊥ zero ()
i∉⊥ (suc i) (there i∈⊥) = i∉⊥ i i∈⊥

i∈⁅i⁆′ : {n : ℕ} (i j : Fin n) → j ∈ ⁅ i ⁆ → j ≡ i
i∈⁅i⁆′ zero zero j∈⁅i⁆ = refl
i∈⁅i⁆′ zero (suc j) (there j∈⁅i⁆) = ⊥-elim (i∉⊥ j j∈⁅i⁆)
i∈⁅i⁆′ (suc i) zero ()
i∈⁅i⁆′ (suc i) (suc j) (there j∈⁅i⁆) = cong suc (i∈⁅i⁆′ i j j∈⁅i⁆)

nonempty : {n : ℕ} → (sub : Subset n) → Dec (Nonempty sub)
nonempty [] = no (λ nonempty-[] → contradiction nonempty-[])
  where
    contradiction : ¬ Nonempty []
    contradiction (_ , ())
nonempty (inside ∷ xs) = yes (zero , here)
nonempty (outside ∷ xs) with nonempty xs
... | yes (i , i∈xs) = yes (suc i , there i∈xs)
... | no ¬nonempty-xs = no (contradiction ¬nonempty-xs)
  where
    contradiction : ¬ Nonempty xs → ¬ Nonempty (outside ∷ xs)
    contradiction ¬nonempty-xs (zero , ())
    contradiction ¬nonempty-xs (suc i , there i∈xs) = ¬nonempty-xs (i , i∈xs)

empty→⊥ : {n : ℕ} → (sub : Subset n) → ¬ Nonempty sub → sub ≡ ⊥ {n}
empty→⊥ [] empty = refl
empty→⊥ (inside ∷ sub) empty = ⊥-elim (empty (zero , here))
empty→⊥ (outside ∷ sub) empty = cong (_∷_ outside) (empty→⊥ sub empty-sub)
  where
    empty-sub : ¬ Nonempty sub
    empty-sub (i , i∈sub) = empty (suc i , there i∈sub)

private
  toVec-∉¹-lemma₁ : ∀ {m n} (i : Fin m) (xs : Vec (Fin m) n) → Fin.suc i V.∈ V.map suc xs → i V.∈ xs
  toVec-∉¹-lemma₁ i [] ()
  toVec-∉¹-lemma₁ i (.i ∷ xs) here = here
  toVec-∉¹-lemma₁ i (x ∷ xs) (there si∈sxs) = there (toVec-∉¹-lemma₁ i xs si∈sxs)

  toVec-∉¹-lemma₂ : ∀ {n} (i : Fin n) {x} (xs : Subset n) → suc i ∉ x ∷ xs → i ∉ xs
  toVec-∉¹-lemma₂ i [] si∉x∷xs ()
  toVec-∉¹-lemma₂ i (x ∷ xs) si∉x∷xs i∈x∷xs = si∉x∷xs (there i∈x∷xs)

toVec-∉¹ : {n : ℕ} {i : Fin n} {xs : Subset n} → i ∉ xs → ¬ i V.∈ (toVec xs)
toVec-∉¹            {xs = []}      i∉xs ()
toVec-∉¹ {i = zero} {inside  ∷ xs} i∉xs i∈toVec-xs = i∉xs here
toVec-∉¹ {i = zero} {outside ∷ xs} i∉xs i∈toVec-xs = zero∉map-suc (toVec xs) i∈toVec-xs
  where
    zero∉map-suc : ∀ {m n} (xs : Vec (Fin m) n) → ¬ zero V.∈ V.map Fin.suc xs
    zero∉map-suc [] ()
    zero∉map-suc (x ∷ xs) (there z∈s) = zero∉map-suc xs z∈s
toVec-∉¹ {i = suc i} {inside  ∷ xs} i∉xs (there i∈toVec-xs) = toVec-∉¹ (toVec-∉¹-lemma₂ i xs i∉xs) (toVec-∉¹-lemma₁ i (toVec xs) i∈toVec-xs)
toVec-∉¹ {i = suc i} {outside ∷ xs} i∉xs i∈toVec-xs = toVec-∉¹ (toVec-∉¹-lemma₂ i xs i∉xs) (toVec-∉¹-lemma₁ i (toVec xs) i∈toVec-xs)
