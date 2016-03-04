We present three inhabitants of the \AgdaRecord{SobrinhoAlgebra} record to demonstrate both that they exist and are not categorical (i.e. are not inhabitable by only one structure up to isomorphism).
We will also use the inhabitants later in Section~\ref{sect.example} where we provide an example execution of our algorithm.

Trivially, the axioms of a \AgdaRecord{SobrinhoAlgebra} are satisfied by the unit type, \AgdaDatatype{⊤}, defining a degenerate `addition' and `multiplication' operation on \AgdaDatatype{⊤}.
Inhabiting the \AgdaRecord{SobrinhoAlgebra} record is henceforth straightforward.

\AgdaHide{
\begin{code}
module path-models where
  open import Data.Unit
  open import Relation.Binary.PropositionalEquality
  open import Algebra.FunctionProperties (_≡_ {A = ⊤})
\end{code}}

To obtain more useful models, we first consider the natural numbers with a distinguished element, intuitively taken to be a `point at infinity':
%Define \AgdaDatatype{ℕ∞} as follows:
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
The constructor \AgdaInductiveConstructor{↑} can be used to embed the natural numbers into \AgdaDatatype{ℕ∞}.
Define addition, multiplication, minimum and maximum functions, \AgdaFunction{\_{+}\_}, \AgdaFunction{\_{*}\_}, \AgdaFunction{\_{⊓}\_}, and \AgdaFunction{\_{⊔}\_}, respectively, so that \AgdaInductiveConstructor{∞} is fixed as the largest element of \AgdaDatatype{ℕ∞}, and the following properties of addition and multiplication hold for all \AgdaBound{m}: \AgdaInductiveConstructor{∞}~\AgdaFunction{+}~\AgdaBound{m}~\AgdaDatatype{≡}~\AgdaInductiveConstructor{∞}~\AgdaDatatype{≡}~\AgdaBound{m}~\AgdaFunction{+}~\AgdaInductiveConstructor{∞}, and \AgdaInductiveConstructor{∞}~\AgdaFunction{*}~\AgdaBound{m}~\AgdaDatatype{≡}~\AgdaInductiveConstructor{∞}~\AgdaDatatype{≡}~\AgdaBound{m}~\AgdaFunction{*}~\AgdaInductiveConstructor{∞}, behaving in the `obvious way' in all other cases.

Using these definitions we can define the \emph{shortest path} algebra by taking the algebra's addition and multiplication functions to be \AgdaFunction{\_{⊓}\_} and \AgdaFunction{\_{+}\_} on \AgdaDatatype{ℕ∞}, respectively, the unit for addition to be \AgdaInductiveConstructor{∞}, and the unit for multiplication to be \AgdaInductiveConstructor{↑}~\AgdaInductiveConstructor{0}.
We may also define the \emph{widest path} algebra by taking the algebra's addition and multiplication functions to be \AgdaFunction{\_{⊓}\_} and \AgdaFunction{\_{⊔}\_} on \AgdaDatatype{ℕ∞}, respectively, the unit for addition to be \AgdaInductiveConstructor{∞}, and the unit for multiplication to be \AgdaInductiveConstructor{↑}~\AgdaInductiveConstructor{0}.
% As the names suggest, executing our generalised shortest path algorithm with adjacency matrix coefficients taken from a shortest path Sobrinho Algebra will compute the shortest path through the graph described by the matrix, whilst taking matrix coefficients from a widest path Sobrinho Algebra will compute the widest path, or maximum bottleneck capacity.
