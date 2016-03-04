We write \AgdaDatatype{Vec}~\AgdaBound{A}~\AgdaBound{n} for a length-indexed list containing elements of type \AgdaBound{A} with length \AgdaBound{n}.
We write \AgdaDatatype{Matrix}~\AgdaBound{A}~\AgdaBound{m}~\AgdaBound{n} for the type of $m \times n$-dimensional matrices containing elements of type $A$, implemented as a vector of vectors.
We use finite sets, where \AgdaDatatype{Fin}~\AgdaBound{n} is intuitively the type of natural numbers `of at most $n$', to index into matrices and represent graph nodes---this type has a decidable equality for all $n$.
We write \AgdaFunction{Subset}~\AgdaBound{n} for a fixed-length list of length \AgdaBound{n}, which partitions a finite set into elements that lie `inside' and `outside' of the set, to implement sets of nodes.
At each index \AgdaBound{i} of the vector are one of two flags---\AgdaInductiveConstructor{inside} or \AgdaInductiveConstructor{outside}---denotating whether the $i^\mathrm{th}$ element of the finite set in question is inside or outside the described subset, i.e. a partitioning of a finite set into two new sets.

Assume an algebraic structure with carrier type \AgdaField{Carrier}, a decidable equality \AgdaField{\_≈\_} and left multiplicative identity \AgdaField{1\#} (structures of this form will be further discussed in Section~\ref{sect.path.algebras.their.properties.and.models}).
We define an $n$-dimensional adjacency matrix over this structure as a record \AgdaRecord{Adj}~\AgdaSymbol{(}\AgdaBound{n}~\AgdaSymbol{:}~\AgdaRecord{ℕ}\AgdaSymbol{)} parameterised by the dimension, and with two fields: \AgdaField{matrix}, the underlying adjacency matrix of type \AgdaRecord{Matrix}~\AgdaField{Carrier}~\AgdaBound{n}~\AgdaBound{n}, and \AgdaField{diag}, a proof that diagonal elements of \AgdaField{matrix} are all equivalent to \AgdaField{1\#}.


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

\AgdaHide{
% TODO: explain universe levels (ie, where do c and ℓ come from?)
\begin{code}
  record Adj (n : ℕ) : Set (c ⊔ ℓ) where
    field
      matrix  : Matrix Weight n n
      diag    : ∀ i → matrix [ i , i ] ≈ 1#
\end{code}}
