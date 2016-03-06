We introduce a notion of lightweight `big sum'~\cite{bertot_canonical_2008} that will be used in our algorithm and proof of correctness when calculating path weights.
Though in the rest of the paper they will be used over Sobrinho Algebras, we here define path weight sums over commutative monoids for convenience as they are well supported by the Standard Library, and Sobrinho Algebras subsume commutative monoids.
We explicitly require a proof of idempotency whenever needed.

We use the function \AgdaFunction{fold} to define sums over subsets of finite sets using the underlying monoid's identity element \AgdaField{ε} and binary operator \AgdaField{\_∙\_}:

\AgdaHide{
\begin{code}
open import Algebra using (CommutativeMonoid ; module CommutativeMonoid)

module sums
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
\end{code}
}

\begin{code}
  fold : ∀ {n} → (Fin n → Carrier) → Subset n → Carrier
  fold f []              = ε
  fold f (inside ∷ xs)   = f zero ∙  fold (f ∘ suc) xs
  fold f (outside ∷ xs)  =           fold (f ∘ suc) xs
\end{code}
Intuitively, for a subset of a finite set of size \AgdaBound{n}, the function call \AgdaFunction{fold}~\AgdaBound{f}~\AgdaBound{xs} enumerates all \AgdaBound{n} possible elements of the set, testing each in turn whether it is an element of the subset described by \AgdaBound{xs}, acting on the element if so, ignoring it otherwise.
For convenience we provide a \AgdaKeyword{syntax} declaration for \AgdaFunction{fold}, so that the notation $\AgdaFunction{⨁[}~\AgdaBound{x}~\AgdaFunction{←}~\AgdaBound{v}~\AgdaFunction{]}~\AgdaBound{e}$ denotes the application \AgdaFunction{fold}~(\AgdaSymbol{λ}~\AgdaBound{x}~\AgdaSymbol{→}~\AgdaBound{e})~\AgdaBound{v}.

\AgdaHide{
\begin{code}
  infix 6 ⨁-syntax
\end{code}
\begin{code}
  ⨁-syntax = fold
  syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v ] e
\end{code}}
\AgdaHide{
\begin{code}
  open import Algebra.FunctionProperties _≈_

  open import Data.Empty using (⊥-elim)

  open import Relation.Binary.EqReasoning setoid
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)
\end{code}}

Trivially, we have that folding over an empty set (written \AgdaFunction{⊥}) is equivalent to the neutral element of the monoid, and folding over a singleton set containing an element, written \AgdaFunction{⁅}~\AgdaBound{i}~\AgdaFunction{⁆} for each element \AgdaBound{i}, is equivalent to applying the function \AgdaBound{f} to \AgdaBound{i}.
These facts are expressed as the lemmas \AgdaFunction{fold-⊥} and \AgdaFunction{fold-⁅i⁆}, respectively, which we omit here.
\AgdaHide{
\begin{code}
  fold-⊥ : ∀ {n} f → fold f (⊥ {n}) ≈ ε

  fold-⁅i⁆ : ∀ {n} f (i : Fin n) → fold f ⁅ i ⁆ ≈ f i
\end{code}}
\AgdaHide{
\begin{code}
  fold-⊥ {zero}   f = refl
  fold-⊥ {suc n}  f = fold-⊥ (f ∘ suc)
\end{code}}
\AgdaHide{
\begin{code}
  fold-⁅i⁆ f zero =
    begin
      f zero ∙ fold (f ∘ suc) ⊥  ≈⟨ ∙-cong refl (fold-⊥ (f ∘ suc)) ⟩
      f zero ∙ ε                 ≈⟨ proj₂ identity _ ⟩
      f zero
    ∎
  fold-⁅i⁆ f (suc i) = fold-⁅i⁆ (f ∘ suc) i
\end{code}}
Folding a function \AgdaBound{f} over a union of two subsets, \AgdaBound{xs} and \AgdaBound{ys}, is equivalent to folding over \AgdaBound{xs} and \AgdaBound{ys} separately and combining the two results with the commutative monoid's binary operator, \AgdaField{\_∙\_}, whenever the operator is idempotent, as expressed by the following lemma, \AgdaFunction{fold-∪}:

\begin{code}
  fold-∪ :  ∀ {n} (idp : Idempotent _∙_) f (xs : Subset n) (ys : Subset n) →
            fold f (xs ∪ ys) ≈ fold f xs ∙ fold f ys
\end{code}

The proof proceeds by simultaneous induction on both subsets, combined with equational reasoning.
For each element of the two sets we must consider whether it lies inside or outside of the subsets being described by \AgdaBound{xs} and \AgdaBound{ys}.

\AgdaHide{
\begin{code}
  fold-∪ idp f []             []             = sym (proj₁ identity _)
\end{code}
\begin{code}
  fold-∪ idp f (inside ∷ xs)  (inside ∷ ys)  =
    begin
      f zero ∙ fold (f ∘ suc) (xs ∪ ys)
    ≈⟨ ∙-cong (sym (idp _)) (fold-∪ idp (f ∘ suc) xs ys) ⟩
      (f zero ∙ f zero) ∙ (fold (f ∘ suc) xs ∙ fold (f ∘ suc) ys)
    ≈⟨ assoc _ _ _ ⟩
      f zero ∙ (f zero ∙ (fold (f ∘ suc) xs ∙ fold (f ∘ suc) ys))
    ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
      f zero ∙ ((f zero ∙ fold (f ∘ suc) xs) ∙ fold (f ∘ suc) ys)
    ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
      f zero ∙ ((fold (f ∘ suc) xs ∙ f zero) ∙ fold (f ∘ suc) ys)
    ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
      f zero ∙ (fold (f ∘ suc) xs ∙ (f zero ∙ fold (f ∘ suc) ys))
    ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ fold (f ∘ suc) xs) ∙ (f zero ∙ fold (f ∘ suc) ys)
    ∎
\end{code}}

\AgdaHide{
\begin{code}
  fold-∪ idp f (inside ∷ xs) (outside ∷ ys) =
    begin
      f zero ∙ fold (f ∘ suc) (xs ∪ ys)
    ≈⟨ ∙-cong refl (fold-∪ idp (f ∘ suc) xs ys) ⟩
      f zero ∙ (fold (f ∘ suc) xs ∙ fold (f ∘ suc) ys)
    ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ fold (f ∘ suc) xs) ∙ fold (f ∘ suc) ys
    ∎
  fold-∪ idp f (outside ∷ xs) (inside  ∷ ys) =
    begin
      f zero ∙ fold (f ∘ suc) (xs ∪ ys)
    ≈⟨ ∙-cong refl (fold-∪ idp (f ∘ suc) xs ys) ⟩
      f zero ∙ (fold (f ∘ suc) xs ∙ fold (f ∘ suc) ys)
    ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ fold (f ∘ suc) xs) ∙ fold (f ∘ suc) ys
    ≈⟨ ∙-cong (comm _ _) refl ⟩
      (fold (f ∘ suc) xs ∙ f zero) ∙ fold (f ∘ suc) ys
    ≈⟨ assoc _ _ _ ⟩
      fold (f ∘ suc) xs ∙ (f zero ∙ fold (f ∘ suc) ys)
    ∎
  fold-∪ idp f (outside ∷ xs) (outside ∷ ys) = fold-∪ idp (f ∘ suc) xs ys
\end{code}}

\AgdaHide{
\begin{code}
  fold-cong-lemma : ∀ {n} (f g : Fin (suc n) → Carrier) x (xs : Subset n) →
                    (∀ i → i ∈ (x ∷ xs) → f i ≈ g i) → (∀ i → i ∈ xs → f (suc i) ≈ g (suc i))
\end{code}
\begin{code}
  fold-cong-lemma f g x [] eq i ()
  fold-cong-lemma f g x (inside ∷ ys) eq i i∈y∷ys = eq (suc i) (there i∈y∷ys)
  fold-cong-lemma f g x (outside ∷ ys) eq zero ()
  fold-cong-lemma f g x (outside ∷ ys) eq (suc i) (there i∈y∷ys) = fold-cong-lemma (f ∘ suc) (g ∘ suc) outside ys (λ i x → eq (suc i) (there x)) i i∈y∷ys
\end{code}}

%Here, \AgdaFunction{assoc}, \AgdaFunction{sym}, and \AgdaFunction{∙-cong} are the associativity, symmetry, and congruence with respect to setoid-equivalence properties of the underlying commutative monoid, respectively.
Finally, we have an extensionality property, namely that folding two different functions across the same set results in equivalent values if the functions agree pointwise on all elements in the set.
This is expressed in the lemma \AgdaFunction{fold-cong}:

\begin{code}
  fold-cong :  ∀ {n} f g (xs : Subset n) → (∀ i → i ∈ xs → f i ≈ g i) →
               fold f xs ≈ fold g xs
\end{code}

\AgdaHide{
\begin{code}
  fold-cong f g []             eq = refl
  fold-cong f g (inside  ∷ xs) eq = ∙-cong (eq zero here) (fold-cong (f ∘ suc) (g ∘ suc) xs (fold-cong-lemma f g inside xs eq))
  fold-cong f g (outside ∷ xs) eq = fold-cong (f ∘ suc) (g ∘ suc) xs (fold-cong-lemma f g outside xs eq)
\end{code}}

\noindent
The proof proceeds by induction on $\AgdaBound{xs}$ and is omitted.

\AgdaHide{
\begin{code}
  fold-distr : ∀ {n} f x (i : Fin n) → fold (λ i → x ∙ f i) ⁅ i ⁆ ≈ x ∙ fold f ⁅ i ⁆
\end{code}
\begin{code}
  fold-distr {suc n} f x zero =
    begin
      (x ∙ f zero) ∙ fold ((λ i → x ∙ f i) ∘ suc) ⊥  ≈⟨ ∙-cong refl (fold-⊥ {n} _) ⟩
      (x ∙ f zero) ∙ ε                                ≈⟨ assoc _ _ _ ⟩
      x ∙ (f zero ∙ ε)                                ≈⟨ ∙-cong refl (∙-cong refl (sym (fold-⊥ {n} _))) ⟩
      x ∙ (f zero ∙ fold (f ∘ suc) ⊥)
    ∎
  fold-distr f x (suc i) = fold-distr (f ∘ suc) x i
\end{code}}

\AgdaHide{
\begin{code}
  fold-empty : ∀ {n} f (xs : Subset n) → Empty xs → fold f xs ≈ ε
\end{code}
\begin{code}
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
\end{code}}

\AgdaHide{
\begin{code}
  fold-distr′ : ∀ {n} (idp : Idempotent _∙_) f x (xs : Subset n) → Nonempty xs →
                fold (λ i → x ∙ f i) xs ≈ x ∙ fold f xs
\end{code}
\begin{code}
  fold-distr′ idp f x [] (_ , ())
  fold-distr′ idp f x (inside ∷ xs) (zero , here) with nonempty-dec xs
  ... | yes nonempty-xs =
    begin
      (x ∙ f zero) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ ∙-cong (comm _ _) refl ⟩
      (f zero ∙ x) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
      f zero ∙ (x ∙ fold (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-distr′ idp (f ∘ suc) x xs nonempty-xs)) ⟩
      f zero ∙ (x ∙ (x ∙ fold (f ∘ suc ) xs))       ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
      f zero ∙ ((x ∙ x) ∙ fold (f ∘ suc ) xs)       ≈⟨ ∙-cong refl (∙-cong (idp _) refl) ⟩
      f zero ∙ (x ∙ fold (f ∘ suc ) xs)             ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ x) ∙ fold (f ∘ suc ) xs             ≈⟨ ∙-cong (comm _ _) refl ⟩
      (x ∙ f zero) ∙ fold (f ∘ suc ) xs             ≈⟨ assoc _ _ _ ⟩
      x ∙ (f zero ∙ fold (f ∘ suc) xs)
    ∎
  ... | no ¬nonempty-xs =
    begin
      (x ∙ f zero) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
      x ∙ (f zero ∙ fold (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-empty (λ i → x ∙ f (suc i)) xs ¬nonempty-xs)) ⟩
      x ∙ (f zero ∙ ε)                               ≈⟨ sym (∙-cong refl (∙-cong refl (fold-empty (f ∘ suc) xs ¬nonempty-xs))) ⟩
      x ∙ (f zero ∙ fold (λ i → f (suc i)) xs)
    ∎
  fold-distr′ idp f x (inside ∷ xs) (suc i , there i∈xs) =
    begin
      (x ∙ f zero) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ ∙-cong (comm _ _) refl ⟩
      (f zero ∙ x) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
      f zero ∙ (x ∙ fold (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-distr′ idp (f ∘ suc) x xs (i , i∈xs))) ⟩
      f zero ∙ (x ∙ (x ∙ fold (f ∘ suc ) xs))       ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
      f zero ∙ ((x ∙ x) ∙ fold (f ∘ suc ) xs)       ≈⟨ ∙-cong refl (∙-cong (idp _) refl) ⟩
      f zero ∙ (x ∙ fold (f ∘ suc ) xs)             ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ x) ∙ fold (f ∘ suc ) xs             ≈⟨ ∙-cong (comm _ _) refl ⟩
      (x ∙ f zero) ∙ fold (f ∘ suc ) xs             ≈⟨ assoc _ _ _ ⟩
      x ∙ (f zero ∙ fold (f ∘ suc) xs)
    ∎
  fold-distr′ idp f x (outside ∷ xs) (suc i , there i∈xs) = fold-distr′ idp (f ∘ suc) x xs (i , i∈xs)
\end{code}
}
