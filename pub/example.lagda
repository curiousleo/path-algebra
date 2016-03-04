\AgdaHide{
\begin{code}
module example where

  import Data.Matrix.Adjacency as Adj
  open import Algebra.Path.Structure
  open import Algebra.Path.Model
    renaming (ℕ∞-shortest-path-algebra to alg)
  import Dijkstra.Algorithm as Algo

  open import Data.Fin using (zero; suc)
  open import Data.Nat as Nat
  open import Data.Matrix as M
  open import Data.Nat.InfinityExtension
  open import Data.Vec as V

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality as P using (_≡_)

  open Adj alg
  open PathAlgebra alg renaming (Carrier to Weight)
  open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
\end{code}}

We provide a short demonstration of our shortest path algorithm in action by executing it within Agda, showing that executing our algorithm on an adjacency matrix produces the expected matrix encoding shortest paths.
All matrix coefficients are taken from the shortest path algebra---the algebra over \AgdaDatatype{ℕ∞} with \AgdaFunction{\_⊓\_} as addition and \AgdaFunction{\_+\_} as multiplication---described in Section~\ref{subsect.models}.
We will suggestively refer to the carrier of this algebra as \AgdaFunction{Weight}.
The two matrices are:
\begin{gather*}
\text{Adjacency} =
\begin{pmatrix}
0 & 4 & 1 \\
∞ & 0 & 2 \\
1 & 2 & 0
\end{pmatrix}
\qquad\qquad
\text{Expected} =
\begin{pmatrix}
0 & 3 & 1 \\
3 & 0 & 2 \\
1 & 2 & 0
\end{pmatrix}
\end{gather*}
The fact that the right-hand matrix is correct can easily be established by hand.
We implement both matrices using our matrix library, calling the first matrix \AgdaFunction{adj} and the second \AgdaFunction{rls-expected}.
For convenience we define the following function \AgdaFunction{rls} that computes the entire Right Local Solution for a given adjacency matrix:
\AgdaHide{
\begin{code}
  adj : Adj 3
\end{code}
\begin{code}
  adj = matrix ▦[ diag ]
    where
      matrix : Matrix Weight 3 3
      matrix  =   (↑ 0 ∷ ↑ 4 ∷ ↑ 1 ∷ [])
              ∷   (∞   ∷ ↑ 0 ∷ ↑ 2 ∷ [])
              ∷   (↑ 1 ∷ ↑ 2 ∷ ↑ 0 ∷ [])
              ∷   []
\end{code}
\begin{code}
      diag : ∀ i → matrix [ i , i ] ≈ ↑ 0
      diag zero             = refl
      diag (suc zero)       = refl
      diag (suc (suc zero)) = refl
      diag (suc (suc (suc ())))
\end{code}
\begin{code}
  rls-expected : Matrix Weight 3 3
  rls-expected  =  (↑ 0 ∷ ↑ 3 ∷ ↑ 1 ∷ [])
                ∷  (↑ 3 ∷ ↑ 0 ∷ ↑ 2 ∷ [])
                ∷  (↑ 1 ∷ ↑ 2 ∷ ↑ 0 ∷ [])
                ∷  []
\end{code}}

\begin{code}
  rls : ∀ {n} → Adj (suc n) → Matrix Weight (suc n) (suc n)
  rls adj = M.tabulate (λ i → let open Algo alg i adj in estimate _ {≤-refl})
\end{code}

The Right Local Solution computed by our algorithm and the expected result are pointwise propositionally equal, with the execution time (within Agda) being on the order of seconds:

\begin{code}
  rls-correct : Pointwise _≡_ (rls adj) rls-expected
  rls-correct = λ r c → refl
\end{code}
