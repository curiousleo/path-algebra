We write \AgdaDatatype{Vec}~\AgdaBound{A}~\AgdaBound{n} for the length-indexed list, or vector, containing elements of type \AgdaBound{A} with length \AgdaBound{n}.
We write \AgdaDatatype{Matrix}~\AgdaBound{A}~\AgdaBound{m}~\AgdaBound{n} for the type of $m \times n$-dimensional matrices containing elements of type $A$, implemented as a vector of vectors.
We use finite sets, where \AgdaDatatype{Fin}~\AgdaBound{n} is intuitively the type of natural numbers `of at most $n$', to index into matrices and represent graph nodes in our formalisation.
The type \AgdaDatatype{Fin}~\AgdaBound{n} has a decidable equality for all $n$.
We use the existing standard library definition of \AgdaDatatype{Subset}, which partitions a finite set into elements that lie `inside' and `outside' of the set, to capture the notion of sets of nodes.

Assume an algebraic structure with carrier type \AgdaField{Carrier}, a decidable equality \AgdaField{\_≈\_} and left multiplicative identity \AgdaField{1\#} (structures of this form will be further discussed in Section~\ref{sect.path.algebras.their.properties.and.models}).
We define an $m$-dimensional adjacency matrix over this structure as a record \AgdaRecord{Adj} parameterised by a dimension:

\AgdaHide{
\begin{code}
open import Algebra.Path.Structure

module matrices {c ℓ} (alg : PathAlgebra c ℓ) where
  open import Level using (_⊔_ ; Lift ; lift)

--  open import Data.Fin using (Fin)
  open import Data.Matrix
  open import Data.Nat.Base using (ℕ)

--  import Relation.Binary.PropositionalEquality as P
--  open P using (_≡_)

  open PathAlgebra alg renaming (Carrier to Weight)
\end{code}
}

% TODO: explain universe levels (ie, where do c and ℓ come from?)
\begin{code}
  record Adj (n : ℕ) : Set (c ⊔ ℓ) where
    field
      matrix  : Matrix Weight n n
      diag    : ∀ i → matrix [ i , i ] ≈ 1#
\end{code}

Here, we bundle a field of type \AgdaDatatype{Matrix}~\AgdaField{Carrier}~\AgdaBound{n}~\AgdaBound{n} with a proof that all diagonal elements of this matrix are equivalent to \AgdaField{1\#}.
