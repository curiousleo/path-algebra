In this section we introduce the Left and Right Canonical Orders of commutative monoids and show some of their properties, culminating in a proof that the Left and Right Canonical Orders are both total orders whenever the monoid's binary operation is selective.
For reasons of brevity, we only present cases for the Left Canonical Order, leaving aside the obvious analgous proofs and definitions for the Right Canonical Order.
Throughout this section we fix an inhabitant of \AgdaRecord{CommutativeMonoid}, and use \AgdaField{Carrier}, \AgdaField{\_≈\_}, \AgdaField{ε}, and \AgdaField{\_∙\_} to denote the monoid's underlying carrier type, supplied equivalence relation, neutral element, and binary operation, respectively.

Note, the wider algebraic routing literature variously refers to either of the two definitions we will introduce below as \emph{the} Canonical Order; Gondran and Minoux~\cite[p.~18]{gondran_graphs_2008}, for example, exclusively use the Right Canonical Order in their work.
\todo{why do we need both, then?}
%leo: we don't ... the choice is arbitrary and all proofs are analogous.

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

We define the Left and Right Canonical Orders (\AgdaFunction{\_⊴ᴸ\_} and \AgdaFunction{\_⊴ᴿ\_}) as follows:

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

Note that \AgdaFunction{∃} is defined in Agda's standard library as a shorthand for a dependent pair where the type of the first element (\AgdaField{Carrier} in this case) is inferred automatically.
First, both Left and Right Canonical Orders are reflexive:

\begin{code}
  ⊴ᴸ-reflexive : ∀ {a b} → a ≈ b → a ⊴ᴸ b
  ⊴ᴸ-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity b) (sym a≈b))
\end{code}

As noted above, the definition of \AgdaFunction{\_⊴ᴸ\_} is an existential statement, so our proof above consists of a dependent pair with explicit witness and proof.
Here, our witness is \AgdaField{ε}, the monoid's unit, and the second component of the dependent pair is a proof that given \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{b}, the equivalence \AgdaBound{a}~\AgdaField{≈}~\AgdaSymbol{(}\AgdaBound{b}~\AgdaField{∙}~\AgdaField{ε}\AgdaSymbol{)} holds.
By definition this is equivalent to \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{b}.
We also have transitivity of \AgdaFunction{\_⊴ᴸ\_}:

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

The proof of transitivity is slightly more involved.
Using the monoid's associative and commutative laws, we show that \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{c}~\AgdaField{∙}~\AgdaSymbol{(}\AgdaBound{x}~\AgdaField{∙}~\AgdaBound{y}\AgdaSymbol{)} which implies \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{c}.
We use the Agda standard library's equational reasoning constructs---\AgdaFunction{begin\_}, \AgdaFunction{\_≈⟨\_⟩\_} and \AgdaFunction{\_∎}---here and in the rest of the paper to structure proofs.

The Left Canonical Order is also total---that is, for any \AgdaBound{a} and \AgdaBound{b}, \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{b} or \AgdaBound{b}~\AgdaFunction{⊴ᴸ}~\AgdaBound{a}---whenever \AgdaField{\_∙\_} is selective, as we show next.
We remind the reader that \AgdaField{\_∙\_} is \emph{selective} when~\AgdaBound{a}~\AgdaField{∙}~\AgdaBound{b} is equivalent to either \AgdaBound{a} or \AgdaBound{b}.
Accordingly, our proof proceeds by a case split on the two possible results of \AgdaBound{a}~\AgdaField{∙}~\AgdaBound{b}:

\begin{code}
  ⊴ᴸ-total : Selective _∙_ → Total _⊴ᴸ_
  ⊴ᴸ-total selective a b with selective a b
  ... | inj₁ a∙b≈a  = inj₁ (a , (sym (trans (comm _ _) a∙b≈a)))
  ... | inj₂ a∙b≈b  = inj₂ (b , (sym a∙b≈b))
\end{code}

The next proof shows that \AgdaFunction{\_⊴ᴸ\_} is antisymmetric---that is, \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{b} and \AgdaBound{b}~\AgdaFunction{⊴ᴸ}~\AgdaBound{a} together imply \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{b}---again, whenever \AgdaField{\_∙\_} is selective.
Again, we proceed by a case split on the results of \AgdaBound{a}~\AgdaField{∙}~\AgdaBound{y} and \AgdaBound{b}~\AgdaField{∙}~\AgdaBound{x}.

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

Taken together, these four properties---reflexivitiy, transitivity, totality and antisymmetry---imply that the Left Canonical Order on a selective commutative monoid is a total order.
Next, we show that the Left Canonical Order of a path algebra's addition operator is a decidable total order.

From this point on we fix \AgdaFunction{∙-selective}, a proof that the monoid's binary operation is selective, and \AgdaField{\_≟\_}, a proof that the monoid's equivalence relation is decidable.
Any Sobrinho Algebra possesses both of these properties, so assuming them here is `safe' for our purposes.
Further, as selectivity implies idempotence, we also have \AgdaFunction{∙-idempotent}, a proof that the monoid's binary operation is idempotent whenever it is selective.

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

\AgdaHide{
\begin{code}
module itp16-requires-path-algebra
       {c ℓ} (dijkstra : PathAlgebra c ℓ) where

  open PathAlgebra dijkstra
    renaming (_+_ to _∙_; +-selective to ∙-selective; +-cong to ∙-cong)
  open FunctionProperties _≈_
  open MFP _≈_
  open import Relation.Binary.EqReasoning setoid

  open itp16-requires-commutative-monoid +-commutativeMonoid public
  open IsTotalOrder (isTotalOrderᴸ ∙-selective) using (antisym)

  _≉_ : _ → _ → Set _
  x ≉ y = ¬ (x ≈ y)

  ∙-idempotent : Idempotent _∙_
  ∙-idempotent = sel⟶idp _∙_ ∙-selective
\end{code}
}

Before demonstrating decidability, we first require two auxiliary lemmas.
The first lemma, \AgdaFunction{∙-selective′}, is a direct consequence of selectivity.
It states that, given \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{b}~\AgdaField{∙}~\AgdaBound{c}, one of \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{b} or \AgdaBound{a}~\AgdaField{≈}~\AgdaBound{c} must hold:

\begin{code}
  ∙-selective′ : ∀ {a b c} → a ≈ b ∙ c → a ≈ b ⊎ a ≈ c
  ∙-selective′ {a} {b} {c} a≈b∙c with ∙-selective b c
  ... | inj₁ b∙c≈b = inj₁ (trans a≈b∙c b∙c≈b)
  ... | inj₂ b∙c≈c = inj₂ (trans a≈b∙c b∙c≈c)
\end{code}

The second lemma, \AgdaFunction{≉⇒⋬ᴸ}, states that if \AgdaBound{b}~\AgdaField{∙}~\AgdaBound{a}~\AgdaField{≈}~\AgdaBound{a} does \emph{not} hold, then \AgdaBound{a}~\AgdaFunction{⊴ᴸ}~\AgdaBound{b} also does not hold, neither:

\begin{code}
  ≉⇒⋬ᴸ : ∀ {a b} → ¬ b ∙ a ≈ a → ¬ a ⊴ᴸ b
  ≉⇒⋬ᴸ {a} {b} ¬b∙a≈a (x , a≈b∙x) with ∙-selective′ a≈b∙x
  ... | inj₁ a≈b = ¬b∙a≈a (trans (∙-cong (sym a≈b) refl) (∙-idempotent a))
  ... | inj₂ a≈x = ¬b∙a≈a (trans (∙-cong refl a≈x) (sym a≈b∙x))
\end{code}

Using these two lemmas, we may finally prove decidability of the Left Canonical Order.
We proceed by splitting on whether \AgdaBound{b}~\AgdaField{∙}~\AgdaBound{a} is equivalent to \AgdaBound{a}, or not, with the only interesting case being the second, where we make use of both of our auxiliary lemmas above:

\begin{code}
  _⊴ᴸ?_ : Decidable _⊴ᴸ_
  a ⊴ᴸ? b with (b ∙ a) ≟ a
  ... | yes b∙a≈a = yes (a , sym b∙a≈a)
  ... | no ¬b∙a≈a = no (≉⇒⋬ᴸ ¬b∙a≈a)
\end{code}

\AgdaHide{
\begin{code}
  isDecTotalOrderᴸ : IsDecTotalOrder _≈_ _⊴ᴸ_
  isDecTotalOrderᴸ =
    record {
      isTotalOrder = isTotalOrderᴸ ∙-selective
      ; _≟_        = _≟_
      ; _≤?_       = _⊴ᴸ?_
      }

  decTotalOrderᴸ : DecTotalOrder _ _ _
  decTotalOrderᴸ =
    record { Carrier = Carrier ; _≈_ = _≈_ ; _≤_ = _⊴ᴸ_ ; isDecTotalOrder = isDecTotalOrderᴸ }
\end{code}}

We therefore have that the Left and Right Canonical Orders form a decidable total order in an arbitrary commutative monoid whenever the monoid's binary operation is selective and its equivalence relation is decidable.
As Sobrinho Algebras are a superstructure of commutative selective monoids with a decidable equivalence relation, we have that the Left and Right Canonical Orders in an arbitrary Sobrinho Algebra are decidable total orders.
