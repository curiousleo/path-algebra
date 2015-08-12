\documentclass{llncs}

\usepackage{agda}
\usepackage{amsmath}
\usepackage[british]{babel}
\usepackage{cite}
\usepackage[colorlinks]{hyperref}
\usepackage{microtype}

\bibliographystyle{splncs03}

\DeclareUnicodeCharacter{8799}{\ensuremath{\overset{?}{\vphantom{o}\smash{=}}}}
\DeclareUnicodeCharacter{8759}{\ensuremath{::}}

\begin{document}

\AgdaHide{
\begin{code}
module itp16 where

open import Function     -- stdlib configured?
open import Data.Matrix  -- project set up correctly?
\end{code}
}

\title{Dijkstra's Algorithm: Verified}
\titlerunning{Dijkstra's Algorithm}
\author{Leonhard Markert \and Timothy Griffin \and Dominic P.~Mulligan}
%\authorrunning{Leonhard Markert et al.}
\institute{%
Computer Laboratory, University of Cambridge,\\
15 JJ Thomson Avenue, Cambridge CB3 0FD, UK,\\
\email{leo.markert@cantab.net}\\
\email{timothy.griffin@cl.cam.ac.uk}\\
\email{dominic.p.mulligan@googlemail.com}}

\maketitle

\begin{abstract}
The abstract should summarize the contents of the paper
using at least 70 and at most 150 words. It will be set in 9-point
font size and be inset 1.0 cm from the right and left margins.
There will be two blank lines before and after the Abstract. \dots
\keywords{Dijkstra's algorithm, shortest paths, internet routing, interactive theorem proving, Agda}
\end{abstract}

\section{Introduction}
\label{sect.introduction}

\subsection{Shortest Paths and Equilibrium Routing}
\label{subsect.shortest.paths.and.equilibrium.routing}

\subsection{Contributions}
\label{subsect.contributions}

\subsection{Agda}
\label{subsect.agda}

Agda~\cite{norell_dependently_2009}

\subsection{Map of Paper}
\label{subsect.map.of.paper}

\section{Formalising Dijkstra's Algorithm}
\label{sect.formalising.dijkstra.algorithm}

\subsection{Basic Definitions}
\label{subsect.basic.definitions}

\begin{description}
\item[Adjacency matrices.] Agda's standard library defines \AgdaDatatype{Vec}~\AgdaBound{A}~\AgdaBound{n}, the type of lists of fixed length \(n\) and elements of type \AgdaBound{A}. We represent an \(m × n\) matrix as a vector containing \(m\) row vectors of length \(n\). As for vectors, the dimensions of a matrix are used as type-level indices: \AgdaDatatype{Matrix}~\AgdaBound{A}~\AgdaBound{m}~\AgdaBound{n} is the type of \(m × n\) matrices with element type \AgdaBound{A}.

An adjacency matrix is a square matrix of edge weights whose diagonal elements are equivalent to the identity of the edge weight operator, \AgdaFunction{\_*\_}. A~square matrix is simply a matrix whose row and column indices are equal. An adjacency matrix is thus represented as a matrix of type \AgdaDatatype{Matrix}~\AgdaField{Weight}~\AgdaBound{n}~\AgdaBound{n} paired with a proof that the result of looking up any element on its diagonal evaluates to a value that is equivalent to \AgdaField{1\#}.
\item[Nodes.] The type of finite sets of size \(n\) is called \AgdaDatatype{Fin}~\AgdaBound{n} in the standard library. Given a graph with \(n\) nodes (represented by an \(n × n\) adjacency matrix), we give its nodes the type \AgdaDatatype{Fin}~\AgdaBound{n}. This results in a number of desirable properties:

\begin{enumerate}
  \item \AgdaDatatype{Fin}~\AgdaBound{n} has exactly \(n\) inhabitants, which allows us to quantify over all nodes by abstracting over an argument of this type.
  \item It is trivial to list all nodes.
  \item Nodes have a decidable equality.
\end{enumerate}

\end{description}

% Representation of algebraic structures as records
% Setoid, Equivalence

% Subset, Bigop, EstimateOrder

\subsection{Sorted Vectors}
\label{subsect.sorted.vectors}

Throughout this Section we fix and open a decidable total order, \AgdaRecord{DecTotalOrder}.
We write \AgdaField{Carrier} for the carrier set of the ordering, write \AgdaField{≤} for the ordering relation and write \AgdaField{≤?} for the proof that the ordering relation is decidable.
Assuming this, we define a type of sorted vectors, or lists indexed by their length:

\AgdaHide{
\begin{code}
open import Relation.Binary

module Sorted
  {a ℓ₁ ℓ₂}
  (totalOrder : DecTotalOrder a ℓ₁ ℓ₂)
  where

  open import Level

  open import Data.Empty
  open import Data.Fin
    using (Fin; zero; suc)
  open import Data.Nat
    using (ℕ; zero; suc; _+_)
  open import Data.Nat.Properties.Simple
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
    hiding (_≤_; _≤?_; total; _≟_)
  import Data.Vec as V
  open V
    using (Vec; foldr)
    renaming ([] to []′; _∷_ to _∷′_; _++_ to _++′_)
  
  open import Function

  open import Relation.Binary.PropositionalEquality
    hiding (isEquivalence; [_])

  open import Relation.Nullary

  open DecTotalOrder totalOrder
    renaming (trans to ≤-trans; refl to ≤-refl)
\end{code}}

\begin{code}
  mutual
    data SortedVec : ℕ → Set (ℓ₂ ⊔ a) where
      []     : SortedVec 0
      _∷_⟨_⟩ : ∀ {n} → (y : Carrier) → (ys : SortedVec n) →
        (y≼ys : y ≼ ys) → SortedVec (ℕ.suc n)

    _≼_ : ∀ {n} → Carrier → SortedVec n → Set ℓ₂
    x ≼ []               = Lift ⊤
    x ≼ (y ∷ ys ⟨ prf ⟩) = (x ≤ y) × (x ≼ ys)
\end{code}

When compared to a standard vector type, our `cons' constructor, \AgdaInductiveConstructor{\_∷\_⟨\_⟩}, takes an additional proof that the head element \emph{dominates} the tail of the list.
The domination relation, \AgdaFunction{\_≼\_}, is defined mutually with the declaration of our sorted vector type, by induction-recursion~\cite{dybjer_general_2000}.
The relation is decidable and quasi-transitive in the sense that if $x$ dominates $xs$ and $y$ is less than $x$ according to our total order then $y$ also dominates $xs$:

\begin{code}
  ≼-trans : ∀ {n y x} → (xs : SortedVec n) → x ≼ xs → y ≤ x → y ≼ xs
\end{code}
\AgdaHide{
\begin{code}
  ≼-trans []               xsDomx         y≤x = lift tt
  ≼-trans (z ∷ zs ⟨ prf ⟩) (x≤z , zsDomx) y≤x = ≤-trans y≤x x≤z , ≼-trans zs zsDomx y≤x
\end{code}}

\AgdaHide{
\begin{code}
  ¬x≤y→y≤x : ∀ {x y} → ¬ (x ≤ y) → y ≤ x
  ¬x≤y→y≤x {x} {y} prf with total x y
  ... | inj₁ p = ⊥-elim ∘ prf $ p
  ... | inj₂ p = p

  head : ∀ {n} → SortedVec (ℕ.suc n) → Carrier
  head (x ∷ xs ⟨ prf ⟩) = x
\end{code}}

The insertion of an element into an existing sorted vector is defined by mutual recursion.
\AgdaFunction{insert} places the inserted element in the correct position in the vector, according to our total order, and `bumps up' the length index by one.
The \AgdaFunction{≼-insert}, mutually defined with \AgdaFunction{insert}, constructs the required proof:

\begin{code}
  mutual
    insert : ∀ {n} → Carrier → SortedVec n → SortedVec (ℕ.suc n)
    insert x []               = x ∷ [] ⟨ lift tt ⟩
    insert x (y ∷ ys ⟨ prf ⟩) with x ≤? y
    ... | yes lt = x ∷ y ∷ ys ⟨ prf ⟩ ⟨ lt , ≼-trans ys prf lt ⟩
    ... | no ¬lt = y ∷ insert x ys ⟨ ≼-insert ys (¬x≤y→y≤x ¬lt) prf ⟩

    ≼-insert : ∀ {n x y} → (ys : SortedVec n) → y ≤ x →
      y ≼ ys → y ≼ (insert x ys)
    ≼-insert {zero} {x} []                y≤x dom = y≤x , lift tt
    ≼-insert {suc n} {x} (z ∷ zs ⟨ prf ⟩) y≤x (y≤z , zsDomy) with x ≤? z
    ... | yes lt = y≤x , y≤z , zsDomy
    ... | no ¬lt = y≤z , ≼-insert zs y≤x zsDomy
\end{code}

Here, \AgdaFunction{¬x≤y→y≤x} is a proof that $x \not\le y$ implies $y \le x$ in a total order.
Appending two sorted vectors, $\AgdaFunction{_++_}$, can be defined by repeatedly inserting elements from the first vector into the second.

Membership of sorted vectors, \AgdaDataType{\_∈\_}, is defined using the usual two constructor inductive relation, complicated slightly by the need to quantify over domination proofs:

\begin{code}
  data _∈_ (x : Carrier) : ∀ {n} → SortedVec n → Set (ℓ₁ ⊔ a ⊔ ℓ₂) where
    here  : ∀ {n} → (xs : SortedVec n) → ∀ prf → x ∈ (x ∷ xs ⟨ prf ⟩)
    there : ∀ {n} → (y : Carrier) → (ys : SortedVec n) →
      ∀ prf → x ∈ ys → x ∈ (y ∷ ys ⟨ prf ⟩)
\end{code}

Using this definition, we may show that the head of the vector is indeed the smallest element contained therein, that is, any other element in a sorted vector is ordered less than the head:

\begin{code}
  head-≤ : ∀ {m} {x} {xs : SortedVec (ℕ.suc m)} → x ∈ xs → head xs ≤ x
  head-≤ (here    []             y≼ys) = ≤-refl
  head-≤ (here    (y ∷ ys ⟨ _ ⟩) _   ) = ≤-refl
  head-≤ (there z []             _         ()    )
  head-≤ (there z (y ∷ ys ⟨ _ ⟩) (z≤y , _) x∈y∷ys) =
    ≤-trans z≤y (head-≤ x∈y∷ys)
\end{code}
The proof proceeds by analysing the cases under which $x \in xs$.


\subsection{Dijkstra Algebras and Their Models}
\label{subsect.dijkstra.algebras.and.their.models}

\subsection{Towards Correctness}
\label{subsect.towards.correctness}

\section{Conclusions}
\label{sect.conclusions}

\subsection{Related Work}
\label{subsect.related.work}

\subsection{Future Work}
\label{subsect.future.work}

\bibliography{path-algebra}

\end{document}
