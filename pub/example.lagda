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

In this section, we demonstrate using a short example that the algorithm presented in this paper can indeed be used to find shortest paths.

We are interested in the shortest paths for the graph defined by the following adjacency matrix:

\begin{align*}
\text{adjacency matrix} &\begin{pmatrix}
0 & 4 & 1 \\
∞ & 0 & 2 \\
1 & 2 & 0 
\end{pmatrix} \\
\text{expected result} &\begin{pmatrix}
0 & 3 & 1 \\
3 & 0 & 2 \\
1 & 2 & 0
\end{pmatrix}
\end{align*}
The adjancency matrix and the expected result can be written as follows using our Agda matrix library:

\AgdaHide{
\begin{code}
  adj : Adj 3
\end{code}}
\begin{code}
  adj = matrix ▦[ diag ]
    where
      matrix : Matrix Weight 3 3
      matrix  =   (↑ 0 ∷ ↑ 4 ∷ ↑ 1 ∷ [])
              ∷   (∞   ∷ ↑ 0 ∷ ↑ 2 ∷ [])
              ∷   (↑ 1 ∷ ↑ 2 ∷ ↑ 0 ∷ [])
              ∷   []
\end{code}
\AgdaHide{
\begin{code}
      diag : ∀ i → matrix [ i , i ] ≈ ↑ 0
      diag zero             = refl
      diag (suc zero)       = refl
      diag (suc (suc zero)) = refl
      diag (suc (suc (suc ())))
\end{code}}
\begin{code}
  rls-expected : Matrix Weight 3 3
  rls-expected  =  (↑ 0 ∷ ↑ 3 ∷ ↑ 1 ∷ [])
                ∷  (↑ 3 ∷ ↑ 0 ∷ ↑ 2 ∷ [])
                ∷  (↑ 1 ∷ ↑ 2 ∷ ↑ 0 ∷ [])
                ∷  []
\end{code}
We omit the trivial proof \AgdaFunction{diag} that all elements on the diagonal are equivalent to \AgdaNumber{0} for brevity.

For convenience we define the following function \AgdaFunction{rls} (for right-local solution) that computes the entire right-local solution for a given adjacency matrix:

\begin{code}
  rls : ∀ {n} → Adj (suc n) → Matrix Weight (suc n) (suc n)
  rls adj = M.tabulate (λ i → let open Algo alg i adj in estimate _ {≤-refl})
\end{code}
The right-local solution computed by our algorithm and the expected result are easily shown to be pointwise propositionally equal:

\begin{code}
  rls-correct : Pointwise _≡_ (rls adj) rls-expected
  rls-correct = λ r c → refl
\end{code}
