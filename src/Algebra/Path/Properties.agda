------------------------------------------------------------------------
-- Path correctness proof
--
-- Properties of Path algebras
------------------------------------------------------------------------

module Algebra.Path.Properties where

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Function

open import Relation.Binary

open import Algebra.FunctionProperties as FunctionProperties using (Op₂)
import Algebra.MoreFunctionProperties as MoreFunctionProperties

open import Relation.Nullary

open import Algebra.Path.Structure

open import Function.Equality using (module Π)
open import Function.Equivalence using (_⇔_; equivalence; module Equivalence)

open Π using (_⟨$⟩_)

rightCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
rightCanonicalOrder _≈_ _∙_ a b = ∃ λ c → b ≈ (a ∙ c)

leftCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
leftCanonicalOrder _≈_ _∙_ a b = ∃ λ c → a ≈ (b ∙ c)

module RequiresCommutativeMonoid
       {c ℓ} (cmon : CommutativeMonoid c ℓ) where

  open CommutativeMonoid cmon
  open FunctionProperties _≈_
  open MoreFunctionProperties _≈_
  open import Relation.Binary.EqReasoning setoid

  infix 4 _⊴ᴸ_ _⊴ᴿ_ _⊲ᴸ_ _⊲ᴿ_

  _⊴ᴸ_ _⊴ᴿ_ _⊲ᴸ_ _⊲ᴿ_ : Rel Carrier _

  _⊴ᴸ_ = leftCanonicalOrder _≈_ _∙_
  _⊴ᴿ_ = rightCanonicalOrder _≈_ _∙_

  a ⊲ᴸ b = a ⊴ᴸ b × ¬ a ≈ b
  a ⊲ᴿ b = a ⊴ᴿ b × ¬ a ≈ b

  ⊴ᴸ-transitive : Transitive _⊴ᴸ_
  ⊴ᴸ-transitive {a} {b} {c} (x , a≈b∙x) (y , b≈c∙y) = x ∙ y , eq
    where
      eq =
        begin
          a            ≈⟨ a≈b∙x ⟩
          b ∙ x        ≈⟨ ∙-cong b≈c∙y refl ⟩
          (c ∙ y) ∙ x  ≈⟨ assoc _ _ _ ⟩
          c ∙ (y ∙ x)  ≈⟨ ∙-cong refl (comm _ _) ⟩
          c ∙ (x ∙ y)
        ∎

  ⊴ᴸ‿¬irrefl : ¬ Irreflexive _≈_ _⊴ᴸ_
  ⊴ᴸ‿¬irrefl irrefl = irrefl (proj₁ identity ε) (ε , refl)

  ⊴ᴸ‿¬tri : ¬ Trichotomous _≈_ _⊴ᴸ_
  ⊴ᴸ‿¬tri tri with tri ε ε
  ... | tri< a ¬b ¬c = ¬b refl
  ... | tri≈ ¬a b ¬c = ¬a (ε , (sym (proj₁ identity ε)))
  ... | tri> ¬a ¬b c = ¬b refl

  isTotalOrderᴸ : Selective _∙_ → IsTotalOrder _≈_ _⊴ᴸ_
  isTotalOrderᴸ selective =
    record
      { isPartialOrder =
        record
          { isPreorder =
            record
              { isEquivalence = isEquivalence
              ; reflexive = ⊴ᴸ-reflexive
              ; trans = ⊴ᴸ-transitive
              }
          ; antisym = ⊴ᴸ-antisym
          }
      ; total = total
    }
    where
      ⊴ᴸ-reflexive : _≈_ ⇒ _⊴ᴸ_
      ⊴ᴸ-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity b) (sym a≈b))

      ⊴ᴸ-antisym : Antisymmetric _≈_ _⊴ᴸ_
      ⊴ᴸ-antisym {a} {b} (x , a≈b∙x) (y , b≈a∙y) with selective a y | selective b x
      ... | _          | inj₁ b∙x≈b = trans a≈b∙x b∙x≈b
      ... | inj₁ a∙y≈a | _          = sym (trans b≈a∙y a∙y≈a)
      ... | inj₂ a∙y≈y | inj₂ b∙x≈x = a≈b
        where
          a≈x = trans a≈b∙x b∙x≈x
          b≈y = trans b≈a∙y a∙y≈y
          a≈b =
            begin
              a ≈⟨ a≈x ⟩
              x ≈⟨ sym b∙x≈x ⟩
              b ∙ x ≈⟨ ∙-cong b≈y refl ⟩
              y ∙ x ≈⟨ comm _ _ ⟩
              x ∙ y ≈⟨ ∙-cong (sym a≈x) refl ⟩
              a ∙ y ≈⟨ a∙y≈y ⟩
              y ≈⟨ sym b≈y ⟩
              b
            ∎

      total : Total _⊴ᴸ_
      total x y with selective x y
      ... | inj₁ ≈x = inj₁ (x , (sym (trans (comm _ _) ≈x)))
      ... | inj₂ ≈y = inj₂ (y , (sym ≈y))

  isTotalOrderᴿ : Selective _∙_ → IsTotalOrder _≈_ _⊴ᴿ_
  isTotalOrderᴿ selective =
    record
      { isPartialOrder =
        record
          { isPreorder =
            record
              { isEquivalence = isEquivalence
              ; reflexive = ⊴ᴿ-reflexive
              ; trans = ⊴ᴿ-transitive
              }
          ; antisym = ⊴ᴿ-antisym
          }
      ; total = total
    }
    where
      ⊴ᴿ-reflexive : _≈_ ⇒ _⊴ᴿ_
      ⊴ᴿ-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity a) a≈b)

      ⊴ᴿ-transitive : Transitive _⊴ᴿ_
      ⊴ᴿ-transitive {a} {b} {c} (x , b≈a∙x) (y , c≈b∙y) =
        x ∙ y , trans c≈b∙y (trans (∙-cong b≈a∙x refl) (assoc _ _ _))

      ⊴ᴿ-antisym : Antisymmetric _≈_ _⊴ᴿ_
      ⊴ᴿ-antisym {a} {b} (x , b≈a∙x) (y , a≈b∙y) with selective a x | selective b y
      ... | _          | inj₁ b∙y≈b = trans a≈b∙y b∙y≈b
      ... | inj₁ a∙x≈a | _          = sym (trans b≈a∙x a∙x≈a)
      ... | inj₂ a∙x≈x | inj₂ b∙y≈y = a≈b
        where
          a≈y = trans a≈b∙y b∙y≈y
          b≈x = trans b≈a∙x a∙x≈x
          a≈b =
            begin
              a      ≈⟨ a≈y ⟩
              y      ≈⟨ sym b∙y≈y ⟩
              b ∙ y  ≈⟨ ∙-cong b≈x refl ⟩
              x ∙ y  ≈⟨ comm _ _ ⟩
              y ∙ x  ≈⟨ ∙-cong (sym a≈y) refl ⟩
              a ∙ x  ≈⟨ sym b≈a∙x ⟩
              b
            ∎

      total : Total _⊴ᴿ_
      total x y with selective x y
      ... | inj₁ ≈x = inj₂ (x , (trans (sym ≈x) (comm _ _)))
      ... | inj₂ ≈y = inj₁ (y , (sym ≈y))

module RequiresPathAlgebra
       {c ℓ} (dijkstra : PathAlgebra c ℓ) where

  open PathAlgebra dijkstra
  open FunctionProperties _≈_
  open MoreFunctionProperties _≈_
  open import Relation.Binary.EqReasoning setoid

  open RequiresCommutativeMonoid +-commutativeMonoid public
  open IsTotalOrder (isTotalOrderᴸ +-selective) using (antisym)

  _≉_ : _ → _ → Set _
  x ≉ y = ¬ (x ≈ y)

  +-idempotent : Idempotent _+_
  +-idempotent = sel⟶idp _+_ +-selective

  equivalentᴸ : ∀ a b → b + a ≈ a ⇔ a ⊴ᴸ b
  equivalentᴸ a b = equivalence to from
    where
      to : b + a ≈ a → a ⊴ᴸ b
      to a≈b+b = a , sym a≈b+b

      from : a ⊴ᴸ b → b + a ≈ a
      from (x , a≈b+x) with +-selective b x
      ... | inj₁ b+x≈b = b+a≈a
        where
          a≈b = trans a≈b+x b+x≈b
          b+a≈a =
            begin
              b + a ≈⟨ +-cong (sym a≈b) refl ⟩
              a + a ≈⟨ +-idempotent a ⟩
              a
            ∎
      ... | inj₂ b+x≈x = b+a≈a
        where
          a≈x = trans a≈b+x b+x≈x
          b+a≈a =
            begin
              b + a ≈⟨ +-cong refl a≈x ⟩
              b + x ≈⟨ sym a≈b+x ⟩
              a
            ∎

  lem₀ : ∀ {a b c} → a ≈ b + c → a ≈ b ⊎ a ≈ c
  lem₀ {a} {b} {c} a≈b+c with +-selective b c
  ... | inj₁ b+c≈b = inj₁ (trans a≈b+c b+c≈b)
  ... | inj₂ b+c≈c = inj₂ (trans a≈b+c b+c≈c)

  equivalentᴸ-¬ : ∀ a b → (¬ b + a ≈ a) ⇔ (¬ a ⊴ᴸ b)
  equivalentᴸ-¬ a b = equivalence to from
    where
      to : ¬ b + a ≈ a → ¬ a ⊴ᴸ b
      to ¬b+a≈a (x , a≈b+x) with lem₀ a≈b+x
      ... | inj₁ a≈b = ¬b+a≈a (trans (+-cong (sym a≈b) refl) (+-idempotent a))
      ... | inj₂ a≈x = ¬b+a≈a (trans (+-cong refl a≈x) (sym a≈b+x))

      from : ¬ a ⊴ᴸ b → ¬ b + a ≈ a
      from ¬a⊴ᴸb b+a≈a = ¬a⊴ᴸb (b+a≈a⟶a⊴ᴸb ⟨$⟩ b+a≈a)
        where
          open Equivalence (equivalentᴸ a b) renaming (to to b+a≈a⟶a⊴ᴸb)

  lem₁ : ∀ {a b} → a ≈ b → ¬ a ⊲ᴸ b
  lem₁ a≈b (_ , ¬a≈b) = ¬a≈b a≈b

  lem₁′ : ∀ {a b} → a ⊲ᴸ b → a ≉ b
  lem₁′ (a⊴ᴸb , a≉b) = a≉b

  lem₂ : ∀ {a b} → a ≈ b → ¬ b ⊲ᴸ a
  lem₂ a≈b (_ , ¬b≈a) = ¬b≈a (sym a≈b)

  lem₂′ : ∀ {a b} → b ⊲ᴸ a → a ≉ b
  lem₂′ (b⊴ᴸa , b≉a) a≈b = b≉a $ sym a≈b

  lem₃ : ∀ {a b} → a ⊲ᴸ b → ¬ b ⊲ᴸ a
  lem₃ {a} {b} (a⊴ᴸb , ¬a≈b) (b⊴ᴸa , ¬b≈a) = ¬a≈b (antisym a⊴ᴸb b⊴ᴸa)

  ⊲ᴸ‿tri : (_≈?_ : Decidable _≈_) → Trichotomous _≈_ _⊲ᴸ_
  ⊲ᴸ‿tri _≈?_ a b with a ≈? b | +-selective b a
  ... | yes a≈b | _          = tri≈ (lem₁ a≈b) a≈b (lem₂ a≈b)
  ... | no ¬a≈b | inj₁ b+a≈b = tri> (lem₃ b⊲ᴸa) ¬a≈b b⊲ᴸa
    where
      open Equivalence (equivalentᴸ b a)
      b⊲ᴸa = (to ⟨$⟩ trans (+-comm _ _) b+a≈b , (λ b≈a → ¬a≈b (sym b≈a)))
  ... | no ¬a≈b | inj₂ b+a≈a = tri< a⊲ᴸb ¬a≈b (lem₃ a⊲ᴸb)
    where
      open Equivalence (equivalentᴸ a b)
      a⊲ᴸb = (to ⟨$⟩ b+a≈a , ¬a≈b)

  ⊴ᴸ-trans : Transitive _⊴ᴸ_
  ⊴ᴸ-trans {a} {b} {c} a⊴ᴸb b⊴ᴸc = c+a≈a⟶a⊴ᴸc ⟨$⟩ c+a≈a
    where
      open Equivalence (equivalentᴸ a b) renaming (from to a⊴ᴸb⟶b+a≈a)
      open Equivalence (equivalentᴸ b c) renaming (from to b⊴ᴸc⟶c+b≈b)
      open Equivalence (equivalentᴸ a c) renaming (to   to c+a≈a⟶a⊴ᴸc)

      b+a≈a = a⊴ᴸb⟶b+a≈a ⟨$⟩ a⊴ᴸb
      c+b≈b = b⊴ᴸc⟶c+b≈b ⟨$⟩ b⊴ᴸc

      c+a≈a =
        begin
          c + a        ≈⟨ +-cong refl (sym b+a≈a) ⟩
          c + (b + a)  ≈⟨ sym $ +-assoc _ _ _ ⟩
          (c + b) + a  ≈⟨ +-cong c+b≈b refl ⟩
          b + a        ≈⟨ b+a≈a ⟩
          a
        ∎

  ⊲ᴸ-trans : Transitive _⊲ᴸ_
  ⊲ᴸ-trans {a} {b} {c} (a⊴ᴸb , ¬a≈b) (b⊴ᴸc , ¬b≈c) = ⊴ᴸ-trans a⊴ᴸb b⊴ᴸc , (λ a≈c → ¬a≈b (a≈b a≈c))
    where
      open Equivalence (equivalentᴸ a b) renaming (from to a⊴ᴸb⟶b+a≈a)
      open Equivalence (equivalentᴸ b c) renaming (from to b⊴ᴸc⟶c+b≈b)
      open Equivalence (equivalentᴸ a c) renaming (to   to c+a≈a⟶a⊴ᴸc)

      b+a≈a = a⊴ᴸb⟶b+a≈a ⟨$⟩ a⊴ᴸb
      c+b≈b = b⊴ᴸc⟶c+b≈b ⟨$⟩ b⊴ᴸc

      a≈b : a ≈ c → a ≈ b
      a≈b a≈c =
        begin
          a            ≈⟨ sym b+a≈a ⟩
          b + a        ≈⟨ +-cong refl a≈c ⟩
          b + c        ≈⟨ +-cong (sym c+b≈b) refl ⟩
          (c + b) + c  ≈⟨ +-assoc _ _ _ ⟩
          c + (b + c)  ≈⟨ +-cong refl (+-comm _ _) ⟩
          c + (c + b)  ≈⟨ +-cong refl c+b≈b ⟩
          c + b        ≈⟨ c+b≈b ⟩
          b
        ∎

  ⊲ᴸ-resp : _⊲ᴸ_ Respects₂ _≈_
  ⊲ᴸ-resp = resp , flip-resp
    where
      resp : ∀ {a} → (_⊲ᴸ_ a) Respects _≈_
      resp {a} {b} {c} b≈c (a⊴ᴸb , ¬a≈b) =
        c+a≈a⟶a⊴ᴸc ⟨$⟩ c+a≈a ,
        (λ a≈c → ¬a≈b (trans a≈c (sym b≈c)))
        where
          open Equivalence (equivalentᴸ a b) renaming (from to a⊴ᴸb⟶b+a≈a)
          open Equivalence (equivalentᴸ a c) renaming (to   to c+a≈a⟶a⊴ᴸc)

          b+a≈a = a⊴ᴸb⟶b+a≈a ⟨$⟩ a⊴ᴸb

          c+a≈a =
            begin
              c + a  ≈⟨ +-cong (sym b≈c) refl ⟩
              b + a  ≈⟨ b+a≈a ⟩
              a
            ∎

      flip-resp : ∀ {b} → flip _⊲ᴸ_ b Respects _≈_
      flip-resp {a} {b} {c} b≈c (b⊴ᴸa , ¬b≈a) =
        a+c≈c⟶c⊴ᴸa ⟨$⟩ a+c≈c ,
        (λ c≈a → ¬b≈a (trans b≈c c≈a))
        where
          open Equivalence (equivalentᴸ b a) renaming (from to b⊴ᴸa⟶a+b≈b)
          open Equivalence (equivalentᴸ c a) renaming (to   to a+c≈c⟶c⊴ᴸa)

          a+b≈b = b⊴ᴸa⟶a+b≈b ⟨$⟩ b⊴ᴸa

          a+c≈c =
            begin
              a + c  ≈⟨ +-cong refl (sym b≈c) ⟩
              a + b  ≈⟨ a+b≈b ⟩
              b      ≈⟨ b≈c ⟩
              c
            ∎

  ⊲ᴸ-isStrictTotalOrder : (_≈?_ : Decidable _≈_) → IsStrictTotalOrder _≈_ _⊲ᴸ_
  ⊲ᴸ-isStrictTotalOrder _≈?_ =
    record
      { isEquivalence = isEquivalence
      ; trans         = ⊲ᴸ-trans
      ; compare       = ⊲ᴸ‿tri _≈?_
      ; <-resp-≈      = ⊲ᴸ-resp
      }

  equivalentᴿ : ∀ a b → a + b ≈ b ⇔ a ⊴ᴿ b
  equivalentᴿ a b = equivalence to from
    where
      to : a + b ≈ b → a ⊴ᴿ b
      to a+b≈b = b , (sym a+b≈b)

      from : a ⊴ᴿ b → a + b ≈ b
      from (x , b≈a+x) with +-selective a x
      ... | inj₁ a+x≈a = a+b≈b
        where
          b≈a = trans b≈a+x a+x≈a
          a+b≈b =
            begin
              a + b  ≈⟨ +-cong (sym b≈a) refl ⟩
              b + b  ≈⟨ +-idempotent b ⟩
              b
            ∎
      ... | inj₂ a+x≈x = a+b≈b
        where
          b≈x = trans b≈a+x a+x≈x
          a+b≈b =
            begin
              a + b  ≈⟨ +-cong refl b≈x ⟩
              a + x  ≈⟨ sym b≈a+x ⟩
              b
            ∎

  *-rightIncreasingᴸ : (a b : Carrier) → a ⊴ᴸ a * b
  *-rightIncreasingᴸ a b = a , lemma
    where
      lemma : a ≈ a * b + a
      lemma =
        sym $ begin
          a * b + a
            ≈⟨ +-comm (a * b) a ⟩
          a + a * b
            ≈⟨ +-absorbs-* a b ⟩
          a
        ∎

  1#-bottomᴸ : ∀ a → 1# ⊴ᴸ a
  1#-bottomᴸ a = 1# , sym (proj₂ +-zero a)

  0#-topᴸ : ∀ a → a ⊴ᴸ 0#
  0#-topᴸ a = a , sym (proj₁ +-identity a)

  +-upperᴸ : ∀ {a b c} → a ⊴ᴸ b → a ⊴ᴸ c → a ⊴ᴸ b + c
  +-upperᴸ {a} {b} {c} (d , a≡b+d) (e , a≡c+e) = d + e , lemma
    where
      lemma : a ≈ b + c + (d + e)
      lemma =
        sym $ begin
          b + c + (d + e)
            ≈⟨ +-cong (+-comm b c) refl ⟩
          c + b + (d + e)
            ≈⟨ +-assoc c b (d + e) ⟩
          c + (b + (d + e))
            ≈⟨ +-cong refl $ sym $ +-assoc b d e ⟩
          c + ((b + d) + e)
            ≈⟨ +-cong refl $ +-cong (sym a≡b+d) refl ⟩
          c + (a + e)
            ≈⟨ +-cong refl $ +-comm a e ⟩
          c + (e + a)
            ≈⟨ sym $ +-assoc c e a ⟩
          (c + e) + a
            ≈⟨ +-cong (sym a≡c+e) refl ⟩
          a + a
            ≈⟨ +-idempotent a ⟩
          a
        ∎

  isDecTotalOrderᴸ : IsDecTotalOrder _≈_ _⊴ᴸ_
  isDecTotalOrderᴸ =
    record {
      isTotalOrder = isTotalOrderᴸ +-selective
      ; _≟_        = _≟_
      ; _≤?_       = _⊴ᴸ?_
      }
    where
      _⊴ᴸ?_ : Decidable _⊴ᴸ_
      a ⊴ᴸ? b with (b + a) ≟ a
      ... | yes b+a≈a = yes (a , sym b+a≈a)
      ... | no ¬b+a≈a = no (¬b+a≈a⟶¬a⊴ᴸb ⟨$⟩ ¬b+a≈a)
        where
          open Equivalence (equivalentᴸ-¬ a b) renaming (to to ¬b+a≈a⟶¬a⊴ᴸb)

  decTotalOrderᴸ : DecTotalOrder _ _ _
  decTotalOrderᴸ =
    record { Carrier = Carrier ; _≈_ = _≈_ ; _≤_ = _⊴ᴸ_ ; isDecTotalOrder = isDecTotalOrderᴸ }
