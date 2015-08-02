open import Algebra

module Dijkstra.Bigop
    {c ℓ} (cmon : CommutativeMonoid c ℓ)
    where

open import Data.Fin hiding (fold; fold′)
open import Data.Fin.Subset
open import Data.Fin.Subset.Extra using (empty→⊥) renaming (nonempty to nonempty-dec)
open import Data.Nat hiding (fold)
open import Data.Product hiding (map; zip)
open import Data.Vec hiding (_∈_)

open import Function using (_∘_; id)

open import Relation.Nullary using (yes; no)

open CommutativeMonoid cmon

fold′ : ∀ {n} → (Fin n → Carrier) → Subset n → Carrier
fold′ f []             = ε
fold′ f (inside  ∷ xs) = f zero ∙ fold′ (f ∘ suc) xs
fold′ f (outside ∷ xs) =          fold′ (f ∘ suc) xs

infix 6 ⨁-syntax

⨁-syntax = fold′
syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v ] e

open import Algebra.FunctionProperties _≈_

open import Data.Empty using (⊥-elim)

open import Relation.Binary.EqReasoning setoid
import Relation.Binary.PropositionalEquality as P
open P using (_≡_)

fold-⊥ : ∀ {n} f → fold′ f (⊥ {n}) ≈ ε
fold-⊥ {zero}  f = refl
fold-⊥ {suc n} f = fold-⊥ (f ∘ suc)

fold-∪ : ∀ {n} (idp : Idempotent _∙_) f (xs : Subset n) (ys : Subset n) → fold′ f (xs ∪ ys) ≈ fold′ f xs ∙ fold′ f ys
fold-∪ idp f []             []       = sym (proj₁ identity _)
fold-∪ idp f (inside ∷ xs) (inside  ∷ ys) =
  begin
    f zero ∙ fold′ (f ∘ suc) (xs ∪ ys)
      ≈⟨ ∙-cong (sym (idp _)) (fold-∪ idp (f ∘ suc) xs ys) ⟩
    (f zero ∙ f zero) ∙ (fold′ (f ∘ suc) xs ∙ fold′ (f ∘ suc) ys)
      ≈⟨ assoc _ _ _ ⟩
    f zero ∙ (f zero ∙ (fold′ (f ∘ suc) xs ∙ fold′ (f ∘ suc) ys))
      ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
    f zero ∙ ((f zero ∙ fold′ (f ∘ suc) xs) ∙ fold′ (f ∘ suc) ys)
      ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
    f zero ∙ ((fold′ (f ∘ suc) xs ∙ f zero) ∙ fold′ (f ∘ suc) ys)
      ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
    f zero ∙ (fold′ (f ∘ suc) xs ∙ (f zero ∙ fold′ (f ∘ suc) ys))
      ≈⟨ sym (assoc _ _ _) ⟩
    (f zero ∙ fold′ (f ∘ suc) xs) ∙ (f zero ∙ fold′ (f ∘ suc) ys)
  ∎
fold-∪ idp f (inside ∷ xs) (outside ∷ ys) =
  begin
    f zero ∙ fold′ (f ∘ suc) (xs ∪ ys)
      ≈⟨ ∙-cong refl (fold-∪ idp (f ∘ suc) xs ys) ⟩
    f zero ∙ (fold′ (f ∘ suc) xs ∙ fold′ (f ∘ suc) ys)
      ≈⟨ sym (assoc _ _ _) ⟩
    (f zero ∙ fold′ (f ∘ suc) xs) ∙ fold′ (f ∘ suc) ys
  ∎
fold-∪ idp f (outside ∷ xs) (inside  ∷ ys) =
  begin
    f zero ∙ fold′ (f ∘ suc) (xs ∪ ys)
      ≈⟨ ∙-cong refl (fold-∪ idp (f ∘ suc) xs ys) ⟩
    f zero ∙ (fold′ (f ∘ suc) xs ∙ fold′ (f ∘ suc) ys)
      ≈⟨ sym (assoc _ _ _) ⟩
    (f zero ∙ fold′ (f ∘ suc) xs) ∙ fold′ (f ∘ suc) ys
      ≈⟨ ∙-cong (comm _ _) refl ⟩
    (fold′ (f ∘ suc) xs ∙ f zero) ∙ fold′ (f ∘ suc) ys
      ≈⟨ assoc _ _ _ ⟩
    fold′ (f ∘ suc) xs ∙ (f zero ∙ fold′ (f ∘ suc) ys)
  ∎
fold-∪ idp f (outside ∷ xs) (outside ∷ ys) = fold-∪ idp (f ∘ suc) xs ys

fold-⁅i⁆ : ∀ {n} f (i : Fin n) → fold′ f ⁅ i ⁆ ≈ f i
fold-⁅i⁆ f zero =
  begin
    f zero ∙ fold′ (f ∘ suc) ⊥  ≈⟨ ∙-cong refl (fold-⊥ (f ∘ suc)) ⟩
    f zero ∙ ε                  ≈⟨ proj₂ identity _ ⟩
    f zero
  ∎
fold-⁅i⁆ f (suc i) = fold-⁅i⁆ (f ∘ suc) i

fold-cong-lemma : ∀ {n} (f g : Fin (suc n) → Carrier) x (xs : Subset n) →
                  (∀ i → i ∈ (x ∷ xs) → f i ≈ g i) → (∀ i → i ∈ xs → f (suc i) ≈ g (suc i))
fold-cong-lemma f g x [] eq i ()
fold-cong-lemma f g x (inside ∷ ys) eq i i∈y∷ys = eq (suc i) (there i∈y∷ys)
fold-cong-lemma f g x (outside ∷ ys) eq zero ()
fold-cong-lemma f g x (outside ∷ ys) eq (suc i) (there i∈y∷ys) = fold-cong-lemma (f ∘ suc) (g ∘ suc) outside ys (λ i x → eq (suc i) (there x)) i i∈y∷ys

fold-cong : ∀ {n} f g (xs : Subset n) → (∀ i → i ∈ xs → f i ≈ g i) → fold′ f xs ≈ fold′ g xs
fold-cong f g []             eq = refl
fold-cong f g (inside  ∷ xs) eq = ∙-cong (eq zero here) (fold-cong (f ∘ suc) (g ∘ suc) xs (fold-cong-lemma f g inside xs eq))
fold-cong f g (outside ∷ xs) eq = fold-cong (f ∘ suc) (g ∘ suc) xs (fold-cong-lemma f g outside xs eq)

fold-distr : ∀ {n} f x (i : Fin n) → fold′ (λ i → x ∙ f i) ⁅ i ⁆ ≈ x ∙ fold′ f ⁅ i ⁆
fold-distr {suc n} f x zero =
  begin
    (x ∙ f zero) ∙ fold′ ((λ i → x ∙ f i) ∘ suc) ⊥  ≈⟨ ∙-cong refl (fold-⊥ {n} _) ⟩
    (x ∙ f zero) ∙ ε                                ≈⟨ assoc _ _ _ ⟩
    x ∙ (f zero ∙ ε)                                ≈⟨ ∙-cong refl (∙-cong refl (sym (fold-⊥ {n} _))) ⟩
    x ∙ (f zero ∙ fold′ (f ∘ suc) ⊥)
  ∎
fold-distr f x (suc i) = fold-distr (f ∘ suc) x i

fold-empty : ∀ {n} f (xs : Subset n) → Empty xs → fold′ f xs ≈ ε
fold-empty f [] empty = refl
fold-empty f (inside  ∷ xs) empty = ⊥-elim (empty nonempty)
  where
    nonempty : Nonempty (inside ∷ xs)
    nonempty = zero , here
fold-empty f (outside ∷ xs) empty = fold-empty (f ∘ suc) xs (empty′ xs empty)
  where
    empty′ : ∀ {n} (xs : Subset n) → Empty (outside ∷ xs) → Empty xs
    empty′ []             empty (x , ())
    empty′ (inside  ∷ xs) empty nonempty  = ⊥-elim (empty (suc zero , there here))
    empty′ (outside ∷ xs) empty (i , elm) = ⊥-elim (empty (suc i , there  elm))

fold-distr′ : ∀ {n} (idp : Idempotent _∙_) f x (xs : Subset n) → Nonempty xs →
              fold′ (λ i → x ∙ f i) xs ≈ x ∙ fold′ f xs
fold-distr′ idp f x [] (_ , ())
fold-distr′ idp f x (inside ∷ xs) (zero , here) with nonempty-dec xs
... | yes nonempty-xs =
  begin
    (x ∙ f zero) ∙ fold′ (λ i → x ∙ f (suc i)) xs  ≈⟨ ∙-cong (comm _ _) refl ⟩
    (f zero ∙ x) ∙ fold′ (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
    f zero ∙ (x ∙ fold′ (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-distr′ idp (f ∘ suc) x xs nonempty-xs)) ⟩
    f zero ∙ (x ∙ (x ∙ fold′ (f ∘ suc ) xs))       ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
    f zero ∙ ((x ∙ x) ∙ fold′ (f ∘ suc ) xs)       ≈⟨ ∙-cong refl (∙-cong (idp _) refl) ⟩
    f zero ∙ (x ∙ fold′ (f ∘ suc ) xs)             ≈⟨ sym (assoc _ _ _) ⟩
    (f zero ∙ x) ∙ fold′ (f ∘ suc ) xs             ≈⟨ ∙-cong (comm _ _) refl ⟩
    (x ∙ f zero) ∙ fold′ (f ∘ suc ) xs             ≈⟨ assoc _ _ _ ⟩
    x ∙ (f zero ∙ fold′ (f ∘ suc) xs)
  ∎
... | no ¬nonempty-xs =
  begin
    (x ∙ f zero) ∙ fold′ (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
    x ∙ (f zero ∙ fold′ (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-empty (λ i → x ∙ f (suc i)) xs ¬nonempty-xs)) ⟩
    x ∙ (f zero ∙ ε)                               ≈⟨ sym (∙-cong refl (∙-cong refl (fold-empty (f ∘ suc) xs ¬nonempty-xs))) ⟩
    x ∙ (f zero ∙ fold′ (λ i → f (suc i)) xs)
  ∎
fold-distr′ idp f x (inside ∷ xs) (suc i , there i∈xs) =
  begin
    (x ∙ f zero) ∙ fold′ (λ i → x ∙ f (suc i)) xs  ≈⟨ ∙-cong (comm _ _) refl ⟩
    (f zero ∙ x) ∙ fold′ (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
    f zero ∙ (x ∙ fold′ (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-distr′ idp (f ∘ suc) x xs (i , i∈xs))) ⟩
    f zero ∙ (x ∙ (x ∙ fold′ (f ∘ suc ) xs))       ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
    f zero ∙ ((x ∙ x) ∙ fold′ (f ∘ suc ) xs)       ≈⟨ ∙-cong refl (∙-cong (idp _) refl) ⟩
    f zero ∙ (x ∙ fold′ (f ∘ suc ) xs)             ≈⟨ sym (assoc _ _ _) ⟩
    (f zero ∙ x) ∙ fold′ (f ∘ suc ) xs             ≈⟨ ∙-cong (comm _ _) refl ⟩
    (x ∙ f zero) ∙ fold′ (f ∘ suc ) xs             ≈⟨ assoc _ _ _ ⟩
    x ∙ (f zero ∙ fold′ (f ∘ suc) xs)
  ∎
fold-distr′ idp f x (outside ∷ xs) (suc i , there i∈xs) = fold-distr′ idp (f ∘ suc) x xs (i , i∈xs)
