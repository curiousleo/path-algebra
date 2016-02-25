\AgdaHide{
\begin{code}
open import Algebra.Path.Structure
import Data.Matrix.Adjacency as MAdj

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
  using (ℕ; zero; suc; _∸_; z≤n)
  renaming (_≤_ to _N≤_)

module dijkstra-correct
    {c ℓ} (alg : PathAlgebra c ℓ)
    {n} (i : Fin (suc n)) (adj : MAdj.Adj alg (suc n))
    where

  open import Algebra.Path.Properties
  open import Dijkstra.Algorithm alg i adj
  open import Dijkstra.Properties alg i adj

  open import Data.Fin.Properties as FP using (_≟_)
  open import Data.Fin.Subset
  import Data.Fin.Subset.Extra as Sub
  open import Data.Matrix
  open import Data.Nat.MoreProperties using (≤-step′)
  open import Data.Nat.Properties using (≤-step)
  open import Data.Product using (proj₁)
  open import Data.Sum using (inj₁; inj₂)
  import Data.Vec as V
  import Data.Vec.Sorted as Sorted

  open import Relation.Nullary using (¬_; yes; no)
  open import Relation.Unary using (Pred)
  open import Relation.Binary using (module DecTotalOrder)
  import Relation.Binary.EqReasoning as EqR
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_; _≢_)
  open P.≡-Reasoning
    using ()
    renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _■)

  open MAdj alg
  open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl)
  open PathAlgebra alg renaming (Carrier to Weight)
  open RequiresPathAlgebra alg
  open DecTotalOrder decTotalOrderᴸ using (_≤_)
  open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)
  open import Dijkstra.Bigop +-commutativeMonoid
  open EqR setoid

  -- Partial right-local solution. This definition is suited for an
  -- inductive proof (step by step)
\end{code}
}

In this Section we prove that our algorithm computes a Right Local Solution to the matrix fixpoint equation of~\cref{subsect.algorithm}.
Throughout this Section, we fix \AgdaBound{alg}, an arbitrary inhabitant of \AgdaRecord{SobrinhoAlgebra}, and \AgdaBound{adj}, an arbitrary $n \times n$ adjacency matrix describing a graph.
Ultimately we aim to show the following statement of correctness:
\begin{equation}
\label{eqn.correctness.correct}
\AgdaFunction{correct}~\AgdaSymbol{:}~\AgdaSymbol{∀}~\AgdaBound{j}~\AgdaSymbol{→}~\AgdaFunction{RLS}~\AgdaBound{n}~\AgdaSymbol{\{}\AgdaFunction{≤-refl}\AgdaSymbol{\}}~\AgdaBound{j}
\end{equation}
That is, our algorithm is correct if, after \AgdaBound{n} iterations of the algorithm on the adjacency matrix \AgdaBound{adj}, a Right Local Solution to the matrix fixpoint equation has been found.
Above, we make use of \AgdaFunction{RLS}, a predicate over graph nodes and steps of the algorithm, which captures the notion of a Right Local Solution.
An estimate $r_j^{(n)}$ for node $j$ at step $n$ is a \emph{Right Local Solution} iff the equation
\begin{displaymath}
r_j^{(n)} ≈ I_{i,j} + \bigoplus_{k ∈ V} r_k^{(n)} * A_{k,j}
\end{displaymath}
% leo: at this point it must be clear to the reader how this corresponds to solving the shortest path problem.
holds, where $V$ is the set of all nodes in the graph described by \AgdaBound{adj} (expressed as \AgdaFunction{⊤} in Agda).
Concretely, in Agda we define this as follows:
\AgdaHide{
\begin{code}
  RLS : (step : ℕ) {s≤n : step N≤ n} → Pred (Fin (suc n)) _
\end{code}
}
\begin{code}
  RLS step {s≤n} j =
    let r = estimate step {s≤n} in
      r j ≈ I[ i , j ] + (⨁[ k ← ⊤ ] r k * A[ k , j ])
\end{code}

To prove Property~\ref{eqn.correctness.correct} above, we define an auxiliary, weaker predicate, capturing the notion of a \emph{Partial Right Local Solution}.
In particular, the estimate $r_j^{(n)}$ for node $j$ at step $n$ is a Partial Right Local Solution iff the equation
\begin{displaymath}
r_j^{(n)} ≈ I_{i,j} + \bigoplus_{k ∈ S_n} r_k^{(n)} * A_{k,j}
\end{displaymath}
holds, where $S_n$ is the set of visited nodes at step $n$.
We express this in Agda as follows:
\AgdaHide{
\begin{code}
  pRLS : (step : ℕ) {s≤n : step N≤ n} → Pred (Fin (suc n)) _
\end{code}
}
\begin{code}
  pRLS step {s≤n} j =
    let r = estimate step {s≤n} in
      r j ≈ I[ i , j ] + (⨁[ k ← seen step {s≤n} ] r k * A[ k , j ])
\end{code}

This definition of a Partial Right Local Solution, as captured by \AgdaFunction{pRLS}, is central to our proof of correctness, as we will prove by induction on the number of algorithm steps taken that the predicate \AgdaFunction{pRLS} holds for any \AgdaBound{step} and \AgdaBound{j}.
We then show that \AgdaFunction{pRLS}~\AgdaBound{n}~\AgdaBound{j}, and the fact that at step \AgdaBound{n} the algorithm has visited all graph nodes, implies \AgdaFunction{RLS}~\AgdaBound{n}~\AgdaBound{j}.
Correctness, as defined above, will follow.
The following lemma
\begin{code}
  pcorrect : (step : ℕ) {s≤n : step N≤ n} → ∀ j → pRLS step {s≤n} j
\end{code}
implements the central argument of our correctness proof, as previously described.
We step through its proof, which proceeds by induction on \AgdaBound{step}, the number of steps of the algorithm so far completed.

\paragraph{Base case.}
In the base case (\AgdaBound{step}~\AgdaSymbol{=}~\AgdaInductiveConstructor{zero}), we perform a case split on whether the node \AgdaBound{j} is equal to the start node, \AgdaBound{i}.
For the base case we use the following shorthands to conserve space:

\begin{itemize}
\item
\AgdaFunction{r}~\AgdaSymbol{=}~\AgdaFunction{estimate}~\AgdaInductiveConstructor{zero}~\AgdaSymbol{\{}\AgdaBound{z≤n}\AgdaSymbol{\}}~\AgdaSymbol{:}~\AgdaFunction{Fin}~\AgdaSymbol{(}\AgdaInductiveConstructor{suc}~\AgdaBound{n}\AgdaSymbol{)}~\AgdaSymbol{→}~\AgdaFunction{Weight}. For any node \AgdaBound{j}, \AgdaFunction{r}~\AgdaBound{j} stands for the initial distance estimate from the start node to \AgdaBound{j}.
\item
\AgdaFunction{diag-lemma}~\AgdaSymbol{:}~\AgdaFunction{I[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}~\AgdaInductiveConstructor{≡}~\AgdaField{0\#}
% for \AgdaFunction{diagonal-nondiag}~\AgdaBound{i}~\AgdaBound{j}~\AgdaBound{¬i≡j}
proves that elements of the identity matrix that are not on the diagonal are equal to the Sobrinho Algebra's unit for \AgdaFunction{\_+\_}.
\item
\AgdaBound{l∘t} for \AgdaFunction{lookup∘tabulate}~\AgdaSymbol{\{}\AgdaBound{f}~\AgdaSymbol{=}~\AgdaFunction{diagonal}~\AgdaField{0\#}~\AgdaField{1\#}\AgdaSymbol{\}}~\AgdaBound{i}~\AgdaBound{j} is an instance of the proof that looking up the element at row \AgdaBound{r} and column \AgdaBound{c} of a matrix generated using \AgdaFunction{tabulate}~\AgdaBound{f} is propositionally equal to \AgdaBound{f}~\AgdaBound{r}~\AgdaBound{c}.
\item
\AgdaFunction{I[i,j]≡0} for \AgdaFunction{P.trans}~\AgdaBound{l∘t}~\AgdaFunction{diag-lemma} shows that looking up an element of the identity matrix of the Sobrinho Algebra over \(ℕ∪\{∞\}\) is propositionally equal to \AgdaNumber{0}.
\item
\AgdaFunction{fold}~\AgdaSymbol{:}~\AgdaFunction{⨁[}~\AgdaBound{k}~\AgdaFunction{→}~\AgdaFunction{r}~\AgdaBound{k}~\AgdaField{*}~\AgdaFunction{A[}~\AgdaBound{k}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}~\AgdaFunction{]}~\AgdaFunction{⁅}~\AgdaBound{i}~\AgdaFunction{⁆}~\AgdaField{≈}~\AgdaFunction{r}~\AgdaBound{i}~\AgdaField{*}~\AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}
%for \AgdaFunction{fold-⁅i⁆}~(\AgdaSymbol{λ}~\AgdaBound{k}~\AgdaSymbol{→}~\AgdaFunction{estimate}~\AgdaInductiveConstructor{zero}~\AgdaSymbol{\{}\AgdaBound{z≤n}\AgdaSymbol{\}}~\AgdaBound{k}~\AgdaFunction{*}~\AgdaFunction{A[}~\AgdaBound{k}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]})~\AgdaBound{i}
proves a particular case of the fact that a fold over a singleton set is just the inner expression of the fold with the only element of the singleton set as the bound variable.
\end{itemize}

\todo{ensure that all lemmas referenced here have been explained earlier in the paper.}

%       r = estimate zero {z≤n}
%      diag-lemma = diagonal-nondiag i j ¬i≡j
%      l∘t = lookup∘tabulate {f = diagonal 0# 1#} i j
%      I[i,j]≡0 = P.trans l∘t diag-lemma
%      fold = fold-⁅i⁆ (λ k → estimate zero {z≤n} k * A[ k , j ]) i

First, assume that $i = j$.
By definition, we have \AgdaFunction{estimate}~\AgdaInductiveConstructor{zero}~\AgdaBound{j} is \AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}, which equals \AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{i}~\AgdaFunction{]}, by assumption.
This, in turn, is equivalent to \AgdaFunction{1\#} by the adjacency matrix diagonal property.
The result follows by the identity matrix' diagonal property and the fact that \AgdaFunction{1\#} is a zero element for \AgdaFunction{\_+\_}:
\begin{code}
  pcorrect zero {s≤n} j with i FP.≟ j
  ... | yes i≡j =
    begin
      r j              ≡⟨⟩
      A[ i , j ]       ≡⟨ P.cong₂ A[_,_] (P.refl {x = i}) j≡i ⟩
      A[ i , i ]       ≈⟨ Adj.diag adj i ⟩
      1#               ≈⟨ sym (proj₁ +-zero _) ⟩
      1#          + _  ≈⟨ +-cong (sym (Adj.diag I j)) refl ⟩
      I[ j , j ]  + _  ≡⟨ P.cong₂ _+_ (P.cong₂ I[_,_] j≡i (P.refl {x = j})) P.refl ⟩
      I[ i , j ]  + _
    ∎
\end{code}
\AgdaHide{
\begin{code}
    where
      r = estimate zero {z≤n}
      j≡i = P.sym i≡j
\end{code}
}

Next, assume that $i \not= j$.
We expand the definition of \AgdaFunction{estimate} and use the identity property of \AgdaFunction{\_+\_} to show that \AgdaFunction{estimate}~\AgdaInductiveConstructor{zero}~\AgdaBound{j} is equivalent to \AgdaFunction{0\#}~\AgdaFunction{+}~\AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}.
The left-hand side (\AgdaFunction{0\#}) is equal to \AgdaFunction{I[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]} by the definition of the identity matrix and the assumption \(i ≠ j\).
Further, the right-hand side (\AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}) can be massaged into \(\bigoplus_{k ∈ \{i\}} r_k * A_{k,j}\) using the left-identity property of \AgdaFunction{*} and the adjacency matrix diagonal property, as follows:
\begin{code}
  ... | no ¬i≡j =
    begin
      r j                             ≡⟨⟩
      A[ i , j ]                      ≈⟨ sym (proj₁ +-identity _) ⟩
      0#          + A[ i , j ]        ≡⟨ P.cong₂ _+_ (P.sym I[i,j]≡0) P.refl ⟩
      I[ i , j ]  + A[ i , j ]        ≈⟨ +-cong refl (sym (*-identityˡ _)) ⟩
      I[ i , j ]  + 1# * A[ i , j ]   ≈⟨ +-cong refl (*-cong (sym (Adj.diag adj i)) refl) ⟩
      I[ i , j ]  + r i * A[ i , j ]  ≈⟨ +-cong refl (sym fold) ⟩
      I[ i , j ]  + (⨁[ k ← ⁅ i ⁆ ] r k * A[ k , j ])
    ∎
\end{code}
\AgdaHide{
\begin{code}
    where
      r = estimate zero {z≤n}

      diag-lemma = diagonal-nondiag i j ¬i≡j
      l∘t = lookup∘tabulate {f = diagonal 0# 1#} i j
      I[i,j]≡0 = P.trans l∘t diag-lemma

      fold = fold-⁅i⁆ (λ k → estimate zero {z≤n} k * A[ k , j ]) i
\end{code}}

\paragraph{Induction step.}
Next, we have the induction step case (\AgdaBound{step} = \AgdaInductiveConstructor{suc}~\AgdaBound{step}) of the partial correctness proof.
We make use of the following shorthands to conserve space:

\begin{itemize}
\item
\AgdaFunction{r} for \AgdaFunction{estimate}~\AgdaBound{step}~\AgdaSymbol{\{}\AgdaInductiveConstructor{≤-step′}~\AgdaBound{s≤n}\AgdaSymbol{\}}, so \AgdaFunction{r}~\AgdaBound{j} stands for the distance estimate from the start node to node \AgdaBound{j} at step \AgdaInductiveConstructor{suc}~\AgdaBound{step}.
\item
\AgdaFunction{r′} for \AgdaFunction{estimate}~(\AgdaInductiveConstructor{suc}~\AgdaBound{step})~\AgdaSymbol{\{}\AgdaBound{s≤n}\AgdaSymbol{\}}, so \AgdaFunction{r}~\AgdaBound{j} stands for the distance estimate to node \AgdaBound{j} at step \AgdaBound{step}.
\item
\AgdaBound{q} for \AgdaFunction{Sorted.head}~\_~(\AgdaFunction{queue}~\AgdaBound{step}~\AgdaSymbol{\{}\AgdaBound{s≤n}\AgdaSymbol{\}}), i.e.~the node whose current estimated distance from the start node is the smallest of all nodes that have not yet been visited.
\item
\AgdaFunction{f} for \AgdaSymbol{λ}~\AgdaBound{k}~\AgdaSymbol{→}~\AgdaBound{r}~\AgdaBound{k}~\AgdaFunction{*}~\AgdaFunction{A[}~\AgdaBound{k}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}.
\item
\AgdaFunction{f′} for \AgdaSymbol{λ}~\AgdaBound{k}~\AgdaSymbol{→}~\AgdaBound{r′}~\AgdaBound{k}~\AgdaFunction{*}~\AgdaFunction{A[}~\AgdaBound{k}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}.
\item
\AgdaBound{vs} for \AgdaFunction{seen}~\AgdaBound{step}~\AgdaSymbol{\{}\AgdaInductiveConstructor{≤-step′}~\AgdaBound{s≤n}\AgdaSymbol{\}}, the list of nodes that have been visited at step \AgdaBound{step}.
\item
\AgdaBound{fold} for \AgdaFunction{fold-cong}~\AgdaFunction{f}~\AgdaFunction{f′}~\AgdaBound{vs}~(\AgdaSymbol{λ}~\AgdaBound{k}~\AgdaBound{k∈vs}~\AgdaSymbol{→}~\AgdaFunction{lemma}~\AgdaBound{k}~\AgdaBound{k∈vs}) is a special case of the theorem that given \AgdaBound{f}~\AgdaBound{i}~\AgdaField{≈}~\AgdaBound{f′}~\AgdaBound{i} for all \AgdaBound{i}~\AgdaFunction{∈}~\AgdaBound{xs} it follows that the fold over \AgdaBound{xs} using \AgdaBound{f} is equivalent to the fold over \AgdaBound{xs} using \AgdaBound{f′} as the fold expresssion.
\end{itemize}

\todo{ensure all lemmas are already explained above}.

Note, in the definition of \AgdaBound{fold}, we make use of a small \AgdaFunction{lemma}, with type \AgdaSymbol{∀}~\AgdaBound{k}~\AgdaSymbol{→}~\AgdaBound{k}~\AgdaFunction{∈}~\AgdaBound{vs}~\AgdaSymbol{→}~\AgdaBound{f}~\AgdaBound{k}~\AgdaFunction{≈}~\AgdaBound{f′}~\AgdaBound{k}, which shows that \AgdaBound{f} and \AgdaBound{f′} agree on all visited graph vertices.

Below, to aid the reader, we present the formal proof, using Agda's equational reasoning mechanism, with explicative comments describing each equational reasoning step:
\begin{code}
  pcorrect (suc step) {s≤n} j =
    begin
      r′ j
      {- Definition of `estimate' -}
        ≡⟨⟩
      r j + r q * A[ q , j ]
      {- Induction Hypothesis -}
        ≈⟨ +-cong (pcorrect step {≤-step′ s≤n} j) refl ⟩
      (I[ i , j ] + (⨁[ k ← vs ] r k * A[ k , j ])) + r q * A[ q , j ]
      {- Associativity of _+_ -}
        ≈⟨ +-assoc _ _ _ ⟩
      I[ i , j ] + ((⨁[ k ← vs ] r k * A[ k , j ]) + r q * A[ q , j ])
      {- Absorptivity -}
        ≈⟨ +-cong refl (+-cong fold (*-cong (sym (+-absorbs-* _ _)) refl)) ⟩
      I[ i , j ] + ((⨁[ k ← vs ] r′ k * A[ k , j ]) + r′ q * A[ q , j ])
      {- Singleton Fold -}
        ≈⟨ +-cong refl (+-cong refl (sym (fold-⁅i⁆ f′ q))) ⟩
      I[ i , j ] + ((⨁[ k ← vs ] r′ k * A[ k , j ]) + (⨁[ k ← ⁅ q ⁆ ] r′ k * A[ k , j ]))
      {- Commutativity and Associativity of _+_ -}
        ≈⟨ +-cong refl (sym (fold-∪ +-idempotent f′ (seen step) ⁅ q ⁆)) ⟩
      I[ i , j ] + (⨁[ k ← vs ∪ ⁅ q ⁆ ] r′ k * A[ k , j ])
      {- Definition of `seen` -}
        ≡⟨⟩
      I[ i , j ] + (⨁[ k ← seen (suc step) {s≤n} ] r′ k * A[ k , j ])
    ∎
\end{code}

\AgdaHide{
\begin{code}
    where
      r′ = estimate (suc step) {s≤n}
      r  = estimate step {≤-step′ s≤n}
      q  = Sorted.head _ (queue step {s≤n})
      f  = λ k → r k * A[ k , j ]
      f′ = λ k → r′ k * A[ k , j ]
      vs = seen step {≤-step′ s≤n}

      lemma : ∀ k → k ∈ vs → f k ≈ f′ k
      lemma k k∈vs = *-cong (sym (estimate-lemma step k k∈vs)) refl

      fold = fold-cong f f′ vs (λ k k∈vs → lemma k k∈vs)
\end{code}}

%\begin{align*}
%r′_j
%&≡ r_j + r_q * A_{q,j} && \text{Definition of \AgdaFunction{estimate}} \\
%&≈ \left(I_{i,j} + \left(\bigoplus_{k ∈ S_n} r_k * A_{k,j}\right)\right) + r_q * A_{q,j} && \text{Induction Hypothesis} \\
%&≈ I_{i,j} + \left(\left(\bigoplus_{k ∈ S_n} r_k * A_{k,j}\right) + r_q * A_{q,j}\right) && \text{Associativity} \\
%&≈ I_{i,j} + \left(\left(\bigoplus_{k ∈ S_n} r′_k * A_{k,j}\right) + r′_q * A_{q,j}\right) && \text{Absorptivity} \\
%&≈ I_{i,j} + \left(\left(\bigoplus_{k ∈ S_n} r′_k * A_{k,j}\right) + \left(\bigoplus_{k ∈ \{ q \}} r′_k * A_{k,j}\right)\right) && \text{Singleton fold} \\
%&≈ I_{i,j} + \bigoplus_{k ∈ S_n ∪ \{ q \}} r′_k * A_{k,j} && \text{Commutativity and Associativity} \\
%&≡ I_{i,j} + \bigoplus_{k ∈ S_{n+1}} r′_k * A_{k,j} && \text{Definition of \AgdaFunction{seen}}
%\end{align*}

This completes the proof of \AgdaFunction{pcorrect}.
Now, we can show that after $n$ iterations all $n$ of the graph's nodes have been visited, so \AgdaFunction{seen}~\AgdaBound{n}~\AgdaDatatype{≡}~\AgdaFunction{⊤}.
We omit the straightforward proof of this fact, which we refer to as \AgdaFunction{lemma} in the following proof that a Partial Right Local Solution after \(n\) steps is the same as a Right Local Solution:

\begin{code}
  correct : ∀ j → RLS n {≤-refl} j
  correct j =
    begin
      r j                                                       ≈⟨ pcorrect n j ⟩
      I[ i , j ] + (⨁[ k ← seen n {≤-refl} ] r k * A[ k , j ])  ≡⟨ lemma ⟩
      I[ i , j ] + (⨁[ k ← ⊤ ] r k * A[ k , j ])
    ∎
\end{code}
\AgdaHide{
\begin{code}
    where
      r = estimate n {≤-refl}

      seen≡⊤ = Sub.n→⊤ (seen n) (seen-size n)
      lemma = P.cong₂ _+_ P.refl (P.cong₂ ⨁-syntax P.refl seen≡⊤)
\end{code}
}
Above, we use the following shorthands to conserve space: \AgdaBound{r} for \AgdaFunction{estimate}~\AgdaBound{n}~\AgdaSymbol{\{}\AgdaInductiveConstructor{≤-refl}\AgdaSymbol{\}}, \AgdaBound{seen≡⊤} for \AgdaFunction{Sub.n→⊤}~(\AgdaFunction{seen}~\AgdaBound{n})~(\AgdaFunction{seen-size}~\AgdaBound{n}), and \AgdaBound{lemma} for \AgdaFunction{P.cong₂}~\AgdaFunction{\_+\_}~\AgdaInductiveConstructor{P.refl}~(\AgdaFunction{P.cong₂}~\AgdaFunction{⨁-syntax}~\AgdaInductiveConstructor{P.refl}~\AgdaBound{seen≡⊤}).
These are, respectively: \todo{explain what these are, and any lemmas they depend on.}
With this, we have Property~\ref{eqn.correctness.correct}, and have the correctness proof of the algorithm.
