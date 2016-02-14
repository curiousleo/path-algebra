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
--  _⊴ᴸ_ = leftCanonicalOrder _≈_ _∙_
--  _⊴ᴿ_ = rightCanonicalOrder _≈_ _∙_
\end{code}}

We define the left and right canonical orders (\AgdaFunction{\_⊴ᴸ\_} and \AgdaFunction{\_⊴ᴿ\_}) as follows:\footnote{The literature variously refers to either of the two definitions as \emph{the} canonical order. Gondran and Minoux, for example, use only the right canonical order \cite[p.~18]{gondran_graphs_2008}.}

% Gondran and Minoux, p.18

\begin{code}
  a ⊴ᴸ b = ∃ λ c → a ≈ (b ∙ c)
  a ⊴ᴿ b = ∃ λ c → b ≈ (a ∙ c)
\end{code}

\AgdaHide{
\begin{code}
  a ⊲ᴸ b = a ⊴ᴸ b × ¬ a ≈ b
  a ⊲ᴿ b = a ⊴ᴿ b × ¬ a ≈ b
\end{code}}

Note that \AgdaFunction{∃} is defined in Agda's standard library as a shortcut for a dependent pair where the type of the first element (\AgdaField{Carrier} in this case) is left implicit.
In the following, we will show some of the properties of left canonical orders. We omit their analogues for right canonical orders.

\begin{code}
  ⊴ᴸ-reflexive : ∀ {a b} → a ≈ b → a ⊴ᴸ b
  ⊴ᴸ-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity b) (sym a≈b))
\end{code}

As noted above, the proof comes in the form of a dependent pair. Its first element is \AgdaField{ε}, the monoid's unit. The second element shows that given \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{b}, the equivalence \AgdaBound{a}~\AgdaField{≈}~\AgdaSymbol{(}\AgdaBound{b}~\AgdaField{∙}~\AgdaField{ε}\AgdaSymbol{)} holds.

By the definition of \AgdaFunction{\_⊴ᴸ\_}, this is equivalent to \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{b}, so the left canonical order is reflexive.

\begin{code}
  ⊴ᴸ-transitive : ∀ {a b c} → a ⊴ᴸ b → b ⊴ᴸ c → a ⊴ᴸ c
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

The transivitiy proof is slightly more involved. Using the algebra's associativity and commutativity laws, we show that \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{c}~\AgdaField{∙}~\AgdaSymbol{(}\AgdaBound{x}~\AgdaField{∙}~\AgdaBound{y}\AgdaSymbol{)} which implies \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{c}. We use the constructs \AgdaFunction{begin\_}, \AgdaFunction{\_≈⟨\_⟩\_} and \AgdaFunction{\_∎} from Agda's equational reasoning library here and in the rest of the paper to structure proofs.

The left canonical order is also total, as the next proof shows. This means that for any \AgdaBound{a} and \AgdaBound{b}, \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{b} or \AgdaBound{b}~\AgdaFunction{⊴ᴸ}~\AgdaBound{a}.
The proof rests on the assumption that \AgdaField{\_∙\_} is selective, i.e.~\AgdaBound{a}~\AgdaField{∙}~\AgdaBound{b} is equivalent to either \AgdaBound{a} or \AgdaBound{b}. It proceeds by a case split on the two possible results of \AgdaBound{a}~\AgdaField{∙}~\AgdaBound{b}.

\begin{code}
  ⊴ᴸ-total : Selective _∙_ → Total _⊴ᴸ_
  ⊴ᴸ-total selective a b with selective a b
  ... | inj₁ a∙b≈a  = inj₁ (a , (sym (trans (comm _ _) a∙b≈a)))
  ... | inj₂ a∙b≈b  = inj₂ (b , (sym a∙b≈b))
\end{code}

The next proof shows that \AgdaFunction{\_⊴ᴸ\_} is antisymmetric, that is, \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{b} and \AgdaBound{b}~\AgdaFunction{⊴ᴸ}~\AgdaBound{a} together imply \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{b}. Again, we assume that \AgdaField{\_∙\_} is selective and proceed by a case split on the results of \AgdaBound{a}~\AgdaField{∙}~\AgdaBound{y} and \AgdaBound{b}~\AgdaField{∙}~\AgdaBound{x}.

\begin{code}
  ⊴ᴸ-antisym : Selective _∙_ → Antisymmetric _≈_ _⊴ᴸ_
  ⊴ᴸ-antisym selective {a} {b} (x , a≈b∙x) (y , b≈a∙y) with selective a y | selective b x
  ... | _           | inj₁ b∙x≈b  = trans a≈b∙x b∙x≈b
  ... | inj₁ a∙y≈a  | _           = sym (trans b≈a∙y a∙y≈a)
  ... | inj₂ a∙y≈y  | inj₂ b∙x≈x  = a≈b
    where
      a≈x = trans a≈b∙x b∙x≈x
      b≈y = trans b≈a∙y a∙y≈y
      a≈b =
        begin
          a      ≈⟨ a≈x ⟩
          x      ≈⟨ sym b∙x≈x ⟩
          b ∙ x  ≈⟨ ∙-cong b≈y refl ⟩
          y ∙ x  ≈⟨ comm _ _ ⟩
          x ∙ y  ≈⟨ ∙-cong (sym a≈x) refl ⟩
          a ∙ y  ≈⟨ a∙y≈y ⟩
          y      ≈⟨ sym b≈y ⟩
          b
        ∎
\end{code}

Taken together, these four properties -- reflexivitiy, transitivity, totality and antisymmetry -- imply that the left canonical order on a selective commutative monoid is a total order.

%leo: also mention non-irreflexivity and non-trichotomy?

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

\AgdaHide{
\begin{code}
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
          ; antisym = ⊴ᴸ-antisym selective
          }
      ; total = ⊴ᴸ-total selective
    }
\end{code}
}

Next, we show that the left canonical order of a path algebra's addition operator is a decidable total order. Given that the left canonical order over a selective commutative monoid is already a total order, we only need to show that in a path algebra, it is also decidable.

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
\end{code}
}

We require two lemmas. The first, \AgdaFunction{+-selective′}, is a direct consequence of selectivity. It says that given \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{b}~\AgdaField{+}~\AgdaBound{c}, one of \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{b} or \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{c} must hold.

\begin{code}
  +-selective′ : ∀ {a b c} → a ≈ b + c → a ≈ b ⊎ a ≈ c
  +-selective′ {a} {b} {c} a≈b+c with +-selective b c
  ... | inj₁ b+c≈b = inj₁ (trans a≈b+c b+c≈b)
  ... | inj₂ b+c≈c = inj₂ (trans a≈b+c b+c≈c)
\end{code}

TODO

\begin{code}
  ≉⇒⋬ᴸ : ∀ {a b} → ¬ b + a ≈ a → ¬ a ⊴ᴸ b
  ≉⇒⋬ᴸ {a} {b} ¬b+a≈a (x , a≈b+x) with +-selective′ a≈b+x
  ... | inj₁ a≈b = ¬b+a≈a (trans (+-cong (sym a≈b) refl) (+-idempotent a))
  ... | inj₂ a≈x = ¬b+a≈a (trans (+-cong refl a≈x) (sym a≈b+x))
\end{code}

TODO

\begin{code}
  _⊴ᴸ?_ : Decidable _⊴ᴸ_
  a ⊴ᴸ? b with (b + a) ≟ a
  ... | yes b+a≈a = yes (a , sym b+a≈a)
  ... | no ¬b+a≈a = no (≉⇒⋬ᴸ ¬b+a≈a)
\end{code}

\AgdaHide{
\begin{code}
  isDecTotalOrderᴸ : IsDecTotalOrder _≈_ _⊴ᴸ_
  isDecTotalOrderᴸ =
    record {
      isTotalOrder = isTotalOrderᴸ +-selective
      ; _≟_        = _≟_
      ; _≤?_       = _⊴ᴸ?_
      }

  decTotalOrderᴸ : DecTotalOrder _ _ _
  decTotalOrderᴸ =
    record { Carrier = Carrier ; _≈_ = _≈_ ; _≤_ = _⊴ᴸ_ ; isDecTotalOrder = isDecTotalOrderᴸ }
\end{code}}
