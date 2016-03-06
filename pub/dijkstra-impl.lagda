\AgdaHide{
\begin{code}
open import Algebra.Path.Structure
import Data.Matrix.Adjacency as MAdj

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
  using (ℕ; zero; suc; _∸_; z≤n)
  renaming (_≤_ to _N≤_)

module dijkstra-impl
    {c ℓ} (alg : PathAlgebra c ℓ)
    {n} (i : Fin (suc n)) (adj : MAdj.Adj alg (suc n))
    where

  open import Algebra.Path.Properties

  open import Data.Fin.Subset
  import Data.Fin.Subset.Extra as Sub
  open Sub using (size; toVec)
  open import Data.Nat using (_≤_)
  open import Data.Nat.MoreProperties using (≤-step′; sm∸n)
  open import Data.Nat.Properties using (≤-step)
  open import Data.Matrix
  import Data.Vec as V
  import Data.Vec.Sorted as Sorted renaming (SortedVec to Vec)

  open import Function using (_$_)

  open import Relation.Nullary using (¬_)
  open import Relation.Unary using (Pred)
  open import Relation.Binary using (DecTotalOrder)
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)

  open PathAlgebra alg renaming (Carrier to Weight)
  open RequiresPathAlgebra alg using (decTotalOrderᴸ)

  open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)

  A[_,_] : Fin (suc n) → Fin (suc n) → Weight
  A[ i , j ] = MAdj.Adj.matrix adj [ i , j ]

  mutual
\end{code}} %


Our purely functional implementation in Agda consists of nine mutually recursive definitions, the most important of which are \AgdaFunction{order}, \AgdaFunction{estimate}, \AgdaFunction{seen} and \AgdaFunction{queue}.
Throughout this section we use $i$ to denote the start node of the search, and use the suggestive name \AgdaFunction{Weight} to refer to the carrier set of our Sobrinho Algebra.

At each \AgdaBound{step} of the algorithm graph nodes are totally ordered.
This total order is constructed using the \AgdaFunction{order} function, which is parameterised by the \AgdaBound{step} of the algorithm:
\begin{code}
    order : (step : ℕ) → {s≤n : step ≤ n} → DecTotalOrder _ _ _
    order step {s≤n} = estimateOrder $ estimate step {s≤n}
\end{code}
The function \AgdaFunction{estimateOrder} lifts a mapping from nodes to weights into a decidable total order on nodes.
The function \AgdaFunction{estimate} provides an estimate of the distance from the start node $i$ to every other node in the graph:
\begin{code}
    estimate : (step : ℕ) → {s≤n : step ≤ n} → Fin (suc n) → Weight
    estimate zero                 j = A[ i , j ]
    estimate (suc step) {step≤n}  j = r j + r q * A[ q , j ]
      where
        q  = Sorted.head (order step {≤-step′ step≤n}) (queue step {step≤n})
        r  = estimate step {≤-step′ step≤n}
\end{code}
The base case for the \AgdaFunction{estimate} function is a lookup in the adjacency matrix of the graph.
Note that in the imperative algorithm discussed in Section~\ref{sect.introduction}, the base case is equivalent to a lookup in the identity matrix instead of the adjacency matrix, whereas our base case here therefore corresponds to the \emph{second} iteration of the imperative algorithm.
This is merely a trivial change and the two are equivalent.

Note also that since the addition operation, \AgdaFunction{\_+\_}, of a Sobrinho Algebra is selective, the inductive case of \AgdaFunction{estimate} encodes a \emph{choice} between \AgdaFunction{r}~\AgdaBound{j} and \AgdaFunction{r}~\AgdaFunction{q}~\AgdaFunction{*}~\AgdaFunction{A[}~\AgdaFunction{q}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}.
The former is simply the previous distance estimate to $j$, whilst the latter represents the option of going from the start node to \AgdaFunction{q} via the best known path from the previous step, and then directly from \AgdaFunction{q} to $j$ (where \AgdaFunction{q} is the head of the priority queue of nodes that have not yet been visited).

We keep track of the set of visited nodes at a given \AgdaBound{step} using the function \AgdaFunction{seen}, which is defined as follows:
\begin{code}
    seen : (step : ℕ) → {s≤n : step ≤ n} → Subset (suc n)
    seen zero                 = ⁅ i ⁆
    seen (suc step) {step≤n}  =
      seen step {≤-step′ step≤n} ∪
      ⁅ Sorted.head (order step {≤-step′ step≤n}) (queue step {step≤n}) ⁆
\end{code}
Here, \AgdaFunction{⁅} \AgdaBound{i} \AgdaFunction{⁆} is a singleton set containing only the start node, \AgdaBound{i}.
The inductive case of \AgdaFunction{seen} unions together all visited nodes from previous steps of the algorithm with the next node to be visited.
Once a node has been visited, its distance estimate stays constant and is optimal---this important invariant will be proved and used later in the proof of correctness of the algorithm in the remainder of the paper.

The following is an auxiliary definition needed to define the function \AgdaFunction{queue}, computing the queue of nodes that have not yet been visited by the algorithm:
\begin{code}
    queue′ : (step : ℕ) {s≤n : step ≤ n} → Sorted.Vec _ (size $ ∁ $ seen step {s≤n})
    queue′ step {s≤n} = Sorted.fromVec (order step {s≤n}) $ toVec $ ∁ $ seen step
\end{code}
Here the function \AgdaFunction{∁} is setwise complement, with the expression \AgdaFunction{∁}~\AgdaFunction{\$}~\AgdaFunction{seen}~\AgdaBound{step} \AgdaSymbol{\{}\AgdaBound{s≤n}\AgdaSymbol{\}} corresponding to the set of \emph{unseen} graph nodes.
The function \AgdaFunction{queue′} is a direct definition of the priority queue of unvisited nodes at a given step of the algorithm: we take the complement set of the set of nodes that have been visited thus far and order them using our total order, \AgdaFunction{order}, at the given algorithm step.
Whilst straightforward to understand, unfortunately, this definition is awkward to use in practice due to a problem with the type of \AgdaFunction{queue′}: the priority queue's only use is to provide the node with the smallest estimate that has not yet been visited, which is always at the head of the queue, but to extract the head of a queue, its type must guarantee that it contains at least one element.
This fact is expressed by mandating that the length index of the vector whose head is being examined must be of the form \AgdaInductiveConstructor{suc}~\AgdaBound{n} for some \AgdaBound{n}.
Therefore, in order to provide a queue with a more usable length index, we prove the following lemma which we will use to `massage' the type of \AgdaFunction{queue′} into something more amenable:
\begin{code}
    queue-size :  (step : ℕ) → {s≤n : suc step ≤ n} →
                  size (∁ $ seen step {≤-step′ s≤n}) ≡ suc (n ∸ suc step)
\end{code} % $
\AgdaHide{
\begin{code}
    seen-size : (step : ℕ) {s≤n : step ≤ n} → Sub.size (seen step {s≤n}) ≡ suc step
    seen-size zero             = Sub.size⁅i⁆≡1 i
    seen-size (suc step) {s≤n} =
      begin
        Sub.size (seen step ∪ ⁅ q ⁆)  ≡⟨ P.cong Sub.size (∪-comm (seen step) ⁅ q ⁆) ⟩
        Sub.size (⁅ q ⁆ ∪ seen step)  ≡⟨ Sub.size-suc q (seen step) (q∉seen step) ⟩
        suc (Sub.size (seen step))    ≡⟨ P.cong suc (seen-size step) ⟩
        suc (suc step)
      ∎
      where
        open P.≡-Reasoning
        open Sub.Properties (suc n)
        q = Sorted.head (order step {≤-step′ s≤n}) (queue step {s≤n})

    queue-size step {s≤n} =
      begin
        size (∁ (seen step))      ≡⟨ Sub.∁-size (seen step) ⟩
        suc n ∸ size (seen step)  ≡⟨ P.cong₂ _∸_ P.refl (seen-size step) ⟩
        suc n ∸ suc step          ≡⟨ sm∸n n (suc step) s≤n ⟩
        suc (n ∸ suc step)
      ∎
      where
        open P.≡-Reasoning
\end{code}}

Using \AgdaFunction{queue′} and \AgdaFunction{queue-size}, we can then give the following more useful definition of the priority queue of previously unvisited nodes, with a \AgdaInductiveConstructor{suc} in head position in the vector's length index, with the function \AgdaFunction{queue}:
\begin{code}
    queue : (step : ℕ) → {s<n : suc step ≤ n} → Sorted.Vec _ (suc (n ∸ (suc step)))
\end{code}
\AgdaHide{
\begin{code}
    queue step {s<n} = P.subst (Sorted.Vec (order step {≤-step′ s<n})) (queue-size step {s<n}) (queue′ step)

    queue⇒queue′ : (step : ℕ) {s≤n : suc step ≤ n} → ∀ {p} (P : ∀ {n} →
                   Sorted.Vec _ n → Set p) → P (queue′ step) → P (queue step {s≤n})
    queue⇒queue′ step {s≤n} P Pqueue = super-subst P (≡-to-≅ (queue-size step {s≤n})) (H.sym H-lemma) Pqueue
      where
        open import Relation.Binary.HeterogeneousEquality as H
        open Sorted (order step {≤-step′ s≤n}) renaming (Vec to SortedVec')

        super-subst : ∀ {m n p} → {xs : SortedVec' m} → {ys : SortedVec' n} →
                      (P : ∀ {n} → SortedVec' n → Set p) → m H.≅ n → xs H.≅ ys → P xs → P ys
        super-subst P H.refl H.refl Pxs = Pxs

        H-lemma : queue step ≅ queue′ step
        H-lemma = ≡-subst-removable SortedVec' (queue-size step {s≤n}) (queue′ step)

    q∉seen : (step : ℕ) {s≤n : suc step ≤ n} → Sorted.head _ (queue step {s≤n}) ∉ seen step {≤-step′ s≤n}
    q∉seen step {s≤n} q∈vs = q∉q∷qs (S.here qs q≼qs)
      where
        module S = Sorted (order step {≤-step′ s≤n})

        q = S.head (queue step {s≤n})
        qs = S.tail (queue step {s≤n})
        q≼qs = S.≼-proof (queue step {s≤n})

        q∉queue′ : ¬ (q S.∈ (queue′ step))
        q∉queue′ = S.fromVec-∉¹ (Sub.toVec-∉¹ (Sub.∁-∈ q∈vs))

        q∉queue : ¬ (q S.∈ (queue step {s≤n}))
        q∉queue = queue⇒queue′ step {s≤n} (λ qs → ¬ (q S.∈ qs)) q∉queue′

        q∉q∷qs : ¬ (q S.∈ (q S.∷ qs ⟨ q≼qs ⟩))
        q∉q∷qs = P.subst (λ qs → ¬ (q S.∈ qs)) S.destruct q∉queue

\end{code}
}
