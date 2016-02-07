In this section we first introduce the left and right canonical orders of commutative monoids and show that both give rise to total orders when selectivity is assumed.

\AgdaHide{
\begin{code}
------------------------------------------------------------------------
-- Path correctness proof
--
-- Properties of Path algebras
------------------------------------------------------------------------

module path-properties where

open import Data.Empty
open import Data.Product
open import Data.Sum hiding ([_,_])

open import Function

open import Relation.Binary

open import Algebra.FunctionProperties as FunctionProperties using (Op₂)
import Algebra.MoreFunctionProperties as MFP

open import Relation.Nullary

open import Algebra.Path.Structure

open import Function.Equality using (module Π)
open import Function.Equivalence using (_⇔_; equivalence; module Equivalence)

open Π using (_⟨$⟩_)

rightCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
rightCanonicalOrder _≈_ _∙_ a b = ∃ λ c → b ≈ (a ∙ c)

leftCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
leftCanonicalOrder _≈_ _∙_ a b = ∃ λ c → a ≈ (b ∙ c)
\end{code}}

\AgdaHide{
\begin{code}
module itp16-requires-commutative-monoid
       {c ℓ} (cmon : CommutativeMonoid c ℓ) where

  open CommutativeMonoid cmon
  open FunctionProperties _≈_
  open MFP _≈_
  open import Relation.Binary.EqReasoning setoid

  infix 4 _⊴ᴸ_ _⊴ᴿ_ _⊲ᴸ_ _⊲ᴿ_

  _⊴ᴸ_ _⊴ᴿ_ _⊲ᴸ_ _⊲ᴿ_ : Rel Carrier _

  _⊴ᴸ_ = leftCanonicalOrder _≈_ _∙_
  _⊴ᴿ_ = rightCanonicalOrder _≈_ _∙_

  a ⊲ᴸ b = a ⊴ᴸ b × ¬ a ≈ b
  a ⊲ᴿ b = a ⊴ᴿ b × ¬ a ≈ b
\end{code}}

\begin{code}
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
\end{code}

%\AgdaHide{
%\begin{code}
%  ⊴ᴸ‿¬irrefl : ¬ Irreflexive _≈_ _⊴ᴸ_
%  ⊴ᴸ‿¬irrefl irrefl = irrefl (proj₁ identity ε) (ε , refl)
%
%  ⊴ᴸ‿¬tri : ¬ Trichotomous _≈_ _⊴ᴸ_
%  ⊴ᴸ‿¬tri tri with tri ε ε
%  ... | tri< a ¬b ¬c = ¬b refl
%  ... | tri≈ ¬a b ¬c = ¬a (ε , (sym (proj₁ identity ε)))
%  ... | tri> ¬a ¬b c = ¬b refl
%\end{code}}

\begin{code}
  isTotalOrderᴸ : Selective _∙_ → IsTotalOrder _≈_ _⊴ᴸ_
\end{code}

\AgdaHide{
\begin{code}
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
\end{code}
}

Next, we show that the left canonical order of a path algebra's addition operator is a decidable total order.

\AgdaHide{
\begin{code}
module itp16-requires-path-algebra
       {c ℓ} (dijkstra : PathAlgebra c ℓ) where

  open PathAlgebra dijkstra
  open FunctionProperties _≈_
  open MFP _≈_
  open import Relation.Binary.EqReasoning setoid

  open itp16-requires-commutative-monoid +-commutativeMonoid public
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
\end{code}}
