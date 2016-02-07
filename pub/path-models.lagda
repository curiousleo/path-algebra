We now discuss three models---or inhabitants---of the \AgdaRecord{PathAlgebra} record to demonstrate that they exist, that Path Algebras are not categorical (i.e. are not inhabitable by only one structure up to isomorphism), and to use later in Section~\ref{sect.example} where we provide an example execution of our algorithm.

Trivially, the axioms of a \AgdaRecord{PathAlgebra} are satisfied by the unit type, \AgdaDatatype{⊤}.
Defining a degenerate `addition' operation on \AgdaDatatype{⊤}, we inhabit \AgdaRecord{PathAlgebra} by taking the algebra's addition and multiplication to be this operation and its two unit elements to be \AgdaInductiveConstructor{tt}, the unit value.
The axioms of the \AgdaRecord{PathAlgebra} are easily satisfied.

\AgdaHide{
\begin{code}
module path-models where
  open import Data.Unit
  open import Relation.Binary.PropositionalEquality
  open import Algebra.FunctionProperties (_≡_ {A = ⊤})
\end{code}}

More useful models for \AgdaRecord{PathAlgebra} can be obtained as follows.
We first consider the natural numbers with a distinguished element, intuitively taken to be a `point at infinity'.
Define \AgdaDatatype{ℕ∞} as follows:

\AgdaHide{
\begin{code}
module InfinityExtension where

  open import Data.Nat
    using (ℕ; zero; suc)
  import Data.Nat as Nat
  open import Data.Sum

  open import Relation.Binary.PropositionalEquality
\end{code}}

\begin{code}
  data ℕ∞ : Set where
    ↑  : ℕ → ℕ∞
    ∞  : ℕ∞
\end{code}

The natural numbers, \AgdaDatatype{ℕ}, can be embedded into \AgdaDatatype{ℕ∞} in the obvious way, using the constructor \AgdaInductiveConstructor{↑}.
Define addition, multiplication, minimum and maximum functions, \AgdaFunction{\_+\_}, \AgdaFunction{\_*\_}, \AgdaFunction{\_⊓\_}, and \AgdaFunction{\_⊔\_}, respectively, so that \AgdaInductiveConstructor{∞} is fixed as the largest element of \AgdaDatatype{ℕ∞}, and the following properties of addition and multiplication hold for all \AgdaBound{m}:
\begin{gather*}
\AgdaInductiveConstructor{∞}\; \AgdaFunction{+}\; \AgdaBound{m}\; \AgdaDatatype{≡}\; \AgdaInductiveConstructor{∞}\; \AgdaDatatype{≡}\; \AgdaBound{m}\; \AgdaFunction{+}\; \AgdaInductiveConstructor{∞}\; \quad\text{and}\quad \AgdaInductiveConstructor{∞}\; \AgdaFunction{*}\; \AgdaBound{m}\; \AgdaDatatype{≡}\; \AgdaInductiveConstructor{∞}\; \AgdaDatatype{≡}\; \AgdaBound{m}\; \AgdaFunction{*}\; \AgdaInductiveConstructor{∞}
\end{gather*}
In all other cases addition and multiplication behave in the `obvious way'.
Using these definitions we can provide two different models for \AgdaRecord{PathAlgebra}:
\begin{enumerate}
\item
The \emph{shortest path algebra} is obtained as follows.
Take the algebra's addition and multiplication functions to be \AgdaFunction{\_⊓\_} and \AgdaFunction{\_+\_} on \AgdaDatatype{ℕ∞}, respectively.
Take the unit for addition to be \AgdaInductiveConstructor{∞} and the unit for multiplication to be \AgdaInductiveConstructor{↑}~\AgdaInductiveConstructor{0}.
\item
The \emph{widest path algebra} is obtained as follows.
Take the algebra's addition and multiplication functions to be \AgdaFunction{\_⊓\_} and \AgdaFunction{\_⊔\_} on \AgdaDatatype{ℕ∞}, respectively.
Take the unit for addition to be \AgdaInductiveConstructor{∞} and the unit for multiplication to be \AgdaInductiveConstructor{↑}~\AgdaInductiveConstructor{0}.
\end{enumerate}
In both cases, it is routine to check that the axioms for a \AgdaRecord{PathAlgebra} can be satisfied.
As the names suggest, executing our generalised Dijkstra algorithm with adjacency matrix coefficients taken from a shortest path algebra will compute the shortest path through the graph described by the matrix, whilst taking matrix coefficients from a widest path algebra will compute the widest path, or maximum bottleneck capacity.
