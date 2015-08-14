\documentclass{llncs}

\usepackage{agda}
\usepackage{amsmath}
\usepackage[british]{babel}
\usepackage{booktabs}
\usepackage{cite}
\usepackage{cleveref}
\usepackage{csquotes}
\usepackage{graphics}
\usepackage[colorlinks]{hyperref}
\usepackage{microtype}
\usepackage{textgreek}

\setlength{\tabcolsep}{6pt}

\bibliographystyle{splncs03}

\DeclareUnicodeCharacter{8799}{\ensuremath{\overset{?}{\vphantom{o}\smash{=}}}}
\DeclareUnicodeCharacter{8759}{\ensuremath{::}}
\DeclareUnicodeCharacter{7522}{\ensuremath{{}_{i}}}
\DeclareUnicodeCharacter{7524}{\ensuremath{{}_{u}}}

\begin{document}

\AgdaHide{
\begin{code}
module itp16 where

open import Algebra.Path.Structure
open import Data.Matrix.Adjacency

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _∸_)
\end{code}
}

\title{Dijkstra's Algorithm: Verified}
\titlerunning{Dijkstra's Algorithm}
\author{Leonhard Markert \and Timothy G.~Griffin \and Dominic P.~Mulligan}
%\authorrunning{Leonhard Markert et al.}
\institute{%
Computer Laboratory, University of Cambridge}

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

Agda~\cite{norell_dependently_2009} is a dependently-typed functional programming language \emph{cum} proof assistant for higher-order intuitionistic logic.
In contrast to similar systems, such as Coq~\cite{bertot_short_2008} and Matita~\cite{asperti_matita_2011}, proof terms are constructed by hand via a process of type-directed refinement, rather than construction through tactic-oriented meta-programming.

Agda has a uniform syntax that should be familiar to Haskell programmers and users of other dependently-typed proof assistants.
One syntactic novelty is a flexible system of user-declared Unicode mixfix identifiers~\cite{danielsson_parsing_2011} with `holes' in an identifier being denoted by underscores.

We write \AgdaSymbol{(}\AgdaBound{x}~\AgdaSymbol{:}~\AgdaBound{A}\AgdaSymbol{)}~\AgdaSymbol{→}~\AgdaBound{B} for the dependent function space where \AgdaBound{x} may occur in \AgdaBound{B}, and write \AgdaBound{A}~\AgdaSymbol{→}~\AgdaBound{B} when \AgdaBound{x} does not occur in \AgdaBound{B} as is usual.
We enclose arguments to be inferred by unification in braces, as in \AgdaSymbol{\{}\AgdaBound{x}~\AgdaSymbol{:}~\AgdaBound{A}\AgdaSymbol{\}}~\AgdaSymbol{→}~\AgdaBound{B}, sometimes making use of the shorthand \AgdaSymbol{∀}~\AgdaBound{x}~\AgdaSymbol{→}~\AgdaBound{B} when types can be inferred.
We write \AgdaDatatype{Σ}~\AgdaBound{A}~\AgdaBound{B} for the dependent sum type whose first projection has type \AgdaBound{A}, and write \AgdaBound{A}~\AgdaDatatype{×}~\AgdaBound{B} when the second projection does not depend on the first, as is usual.
Dependent sums are constructed using the comma constructor: \AgdaBound{x}~\AgdaInductiveConstructor{,}~\AgdaBound{y}.
We sometimes write \AgdaFunction{∃}~\AgdaBound{x}~\AgdaSymbol{→}~\AgdaBound{P} for the dependent sum type when the type of the first projection can be inferred.
Lastly, we write \AgdaBound{A}~\AgdaDatatype{⊎}~\AgdaBound{B} for the disjoint union type with constructors \AgdaInductiveConstructor{inj₁} and \AgdaInductiveConstructor{inj₂}.

Agda is a predicative type theory with an infinite universe hierarchy, \AgdaPrimitiveType{Setᵢ}, with \AgdaPrimitiveType{Set}---the type of small types---being identified with \AgdaPrimitiveType{Set₀}, the base universe in Agda's hierarchy.
Universe polymorphism is used extensively throughout this development, with explicit quantification over universe levels.

\subsection{Map of Paper}
\label{subsect.map.of.paper}

In Section~\ref{sect.basic.definitions} we cover some definitions needed to define Dijkstra's algorithm and its correctness proof.
In Section~\ref{sect.sorted.vectors} we discuss a type of sorted vectors used to maintain a priority queue of yet-unseen graph nodes in the algorithm.
In Section~\ref{sect.path.algebras.their.properties.and.models} we discuss `path algebras', a variety of algebraic structure central to our proof of correctness, also providing three models of path algebras to demonstrate that models exist and that path algebras are not categorical.
In Section~\ref{sect.correctness} we discuss the main body of the correctness proof leading up to our main theorem: Dijkstra's algorithm computes a right-local solution.
In Section~\ref{sect.example} we demonstrate the algorithm in action with an example execution inside Agda.
In Section~\ref{sect.conclusions} we conclude.

\section{Basic Definitions}
\label{sect.basic.definitions}

\subsubsection{Adjacency matrices.}
Agda's standard library defines \AgdaDatatype{Vec}~\AgdaBound{A}~\AgdaBound{n}, the type of lists of fixed length \(n\) and elements of type \AgdaBound{A}. We represent an \(m × n\) matrix as a vector containing \(m\) row vectors of length \(n\). As for vectors, the dimensions of a matrix are used as type-level indices: \AgdaDatatype{Matrix}~\AgdaBound{A}~\AgdaBound{m}~\AgdaBound{n} is the type of \(m × n\) matrices with element type \AgdaBound{A}.

An adjacency matrix is a square matrix of edge weights whose diagonal elements are equivalent to the identity of the edge weight operator, \AgdaFunction{\_*\_}. A~square matrix is simply a matrix whose row and column indices are equal. An adjacency matrix is thus represented as a matrix of type \AgdaDatatype{Matrix}~\AgdaField{Weight}~\AgdaBound{n}~\AgdaBound{n} paired with a proof that the result of looking up any element on its diagonal evaluates to a value that is equivalent to \AgdaField{1\#}.

\subsubsection{Nodes.}
The type of finite sets of size \(n\) is called \AgdaDatatype{Fin}~\AgdaBound{n} in the standard library. Given a graph with \(n\) nodes (represented by an \(n × n\) adjacency matrix), we give its nodes the type \AgdaDatatype{Fin}~\AgdaBound{n}. This results in a number of desirable properties:

\begin{enumerate}
  \item \AgdaDatatype{Fin}~\AgdaBound{n} has exactly \(n\) inhabitants, which allows us to quantify over all nodes by abstracting over an argument of this type.
  \item It is trivial to list all nodes.
  \item Nodes have a decidable equality.
\end{enumerate}

\subsubsection{Sets of nodes.} Since nodes are represented as values of type \AgdaDatatype{Fin}~\AgdaBound{n}, we can re-use the definition of \AgdaDatatype{Subset}~\AgdaBound{n} included in the standard library to represent sets of nodes.

\subsection{Path weight sums}
\label{subsect.path.weight.sums}

\enquote{Sum} here refers to an iteration of an operator over some collection of indices like \(\bigoplus_{x ∈ X} f(x)\) \cite{bertot_canonical_2008}. The properties of the path weight operator \AgdaFunction{\_+\_} include associativity, commutative and idempotence. In combination, these properties allow us to make strong claims about the behaviour of edge weight sums.

% Representation of algebraic structures as records
% Setoid, Equivalence

% Subset, Bigop, EstimateOrder

\section{Sorted Vectors}
\label{sect.sorted.vectors}

% Need to mention AVL trees in standard library

A key consideration in Dijkstra's algorithm is: `which node do we consider next'?
We now define a type of sorted vectors that will be used later in Section~\ref{sect.correctness} to maintain a simple priority queue of yet-unseen graph nodes.
We prefer working with a linear sorted data structure, compared to a balanced binary tree such as Agda's existing implementation of \textsc{avl} trees in \AgdaModule{Data.AVL}, to simplify proofs.
Using a length-indexed data structure also allows us to assert statically the non-emptiness of our priority queue.

Throughout this Section we fix and open a decidable total order, \AgdaRecord{DecTotalOrder}.
We write \AgdaField{Carrier}, \AgdaField{≤} and \AgdaField{≤?} for the ordering's carrier set, ordering relation, and proof that the ordering relation is decidable, respectively.
Assuming this, we define a type of sorted vectors, or sorted lists indexed by their length:

\AgdaHide{
\begin{code}
open import Relation.Binary

module it16-Sorted
  {a ℓ₁ ℓ₂}
  (totalOrder : DecTotalOrder a ℓ₁ ℓ₂)
  where

  open import Level

  open import Data.Empty
  open import Data.Nat using (_+_)
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
      []      : SortedVec 0
      _∷_⟨_⟩  : ∀ {n} →  (y : Carrier) → (ys : SortedVec n) →
                         (y≼ys : y ≼ ys) → SortedVec (ℕ.suc n)

    _≼_ : ∀ {n} → Carrier → SortedVec n → Set ℓ₂
    x ≼ []                = Lift ⊤
    x ≼ (y ∷ ys ⟨ prf ⟩)  = (x ≤ y) × (x ≼ ys)
\end{code}

Compared to a standard vector, our `cons' constructor, \AgdaInductiveConstructor{\_∷\_⟨\_⟩}, takes an additional proof that the head element \emph{dominates} the tail of the list.
The domination relation, \AgdaFunction{\_≼\_}, is defined mutually with the declaration of our sorted vector type via induction-recursion~\cite{dybjer_general_2000} making it impossible to construct a vector that is not sorted.
The relation is decidable and also quasi-transitive in the sense that if $x$ dominates $xs$ and $y$ is less than $x$ according to our total order then $y$ also dominates $xs$.
We state the lemma here, but omit the trivial proof by induction on $xs$, for brevity:

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
% $

The insertion of an element into an existing sorted vector is defined by mutual recursion between two functions \AgdaFunction{insert} and \AgdaFunction{≼-insert}.
The function \AgdaFunction{insert} places the inserted element in the correct position in the vector, `bumping up' the length index, whilst \AgdaFunction{≼-insert} constructs the required domination proof for the new element:

\begin{code}
  mutual
    insert : ∀ {n} → Carrier → SortedVec n → SortedVec (ℕ.suc n)
    insert x []               = x ∷ [] ⟨ lift tt ⟩
    insert x (y ∷ ys ⟨ prf ⟩) with x ≤? y
    ... | yes lt  = x ∷ y ∷ ys ⟨ prf ⟩ ⟨ lt , ≼-trans ys prf lt ⟩
    ... | no ¬lt  = y ∷ insert x ys ⟨ ≼-insert ys (¬x≤y→y≤x ¬lt) prf ⟩

    ≼-insert :  ∀ {n x y} → (ys : SortedVec n) → y ≤ x →
                y ≼ ys → y ≼ (insert x ys)
    ≼-insert {zero}   {x}  []                y≤x  dom = y≤x , lift tt
    ≼-insert {suc n}  {x}  (z ∷ zs ⟨ prf ⟩)  y≤x  (y≤z , zsDomy) with x ≤? z
    ... | yes lt  = y≤x , y≤z , zsDomy
    ... | no ¬lt  = y≤z , ≼-insert zs y≤x zsDomy
\end{code}

Here, \AgdaFunction{¬x≤y→y≤x} is a proof that $x \not\le y$ implies $y \le x$ in a total order.
We use \AgdaFunction{≼-trans} to construct the domination proof in the `cons' case of \AgdaFunction{insert}.

Appending two vectors, \AgdaFunction{\_++\_}, can be defined easily by repeatedly inserting elements from the first vector into the second.
Append is given the usual precise type signature:

\begin{code}
  _++_ : ∀ {m n} → SortedVec m → SortedVec n → SortedVec (m + n)
\end{code}

\AgdaHide{
\begin{code}
  []                ++ ys = ys
  (x ∷ xs ⟨ x≼xs ⟩) ++ ys = insert x (xs ++ ys)
\end{code}}

Vector membership, \AgdaDatatype{\_∈\_}, is defined using an inductive relation, only complicated slightly by the need to quantify over explicit domination proofs:

\begin{code}
  data _∈_ (x : Carrier) : ∀ {n} → SortedVec n → Set (ℓ₁ ⊔ a ⊔ ℓ₂) where
    here   : ∀ {n} →  (xs : SortedVec n) → ∀ prf → x ∈ (x ∷ xs ⟨ prf ⟩)
    there  : ∀ {n} →  (y : Carrier) → (ys : SortedVec n) →
                      ∀ prf → x ∈ ys → x ∈ (y ∷ ys ⟨ prf ⟩)
\end{code}

Using this definition, we may show that the head of a vector is indeed the smallest element contained therein:

\begin{code}
  head-≤ : ∀ {m} {x} {xs : SortedVec (ℕ.suc m)} → x ∈ xs → head xs ≤ x
\end{code}

\AgdaHide{
\begin{code}
  head-≤ (here     []             _  )                  = ≤-refl
  head-≤ (here     (_ ∷ _ ⟨ _ ⟩)  _  )                  = ≤-refl
  head-≤ (there _  []             _          ()      )
  head-≤ (there _  (_ ∷ _ ⟨ _ ⟩)  (z≤y , _)  x∈y∷ys  )  =
    ≤-trans z≤y (head-≤ x∈y∷ys)
\end{code}}

The proof proceeds by analysing the cases under which $x \in xs$, and affirms the suitability of \AgdaDatatype{SortedVec} as a priority queue implementation.

\section{Path Algebras, Their Properties And Models}
\label{sect.path.algebras.their.properties.and.models}

Algebraic structures called path algebras are at the heart of our formalisation of Dijkstra's algorithm.
We introduce path algebras here, prove various lemmas about them, and later provide three models proving their non-triviality and non-categoricity in Subsection~\ref{subsect.models}.

\AgdaHide{
\begin{code}
open import Level using (_⊔_)
open import Relation.Binary

module MoreFunctionProperties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

  open import Algebra.FunctionProperties _≈_

  open import Data.Sum
\end{code}}

\noindent
We start by defining a \emph{selective} binary operation as follows:

\begin{code}
  Selective : Op₂ A → Set _
  Selective _∙_ = ∀ x y → ((x ∙ y) ≈ x) ⊎ ((x ∙ y) ≈ y)
\end{code}

\subsection{Properties}
\label{subsect.properties}

\begin{table}[h]
\centering
\begin{tabular}{c l l}
& \emph{Semiring} & \emph{Path algebra} \\
\midrule
\AgdaFunction{+} & associative & associative \\
                 & commutative & commutative \\
                 & identity \AgdaField{0\#} & identity \AgdaField{0\#} \\
                 & ---                      & selective \\
                 & ---                      & zero \AgdaField{1\#} \\
\midrule
\AgdaFunction{*} & associative & --- \\
                 & identity \AgdaField{1\#} & left-identity \AgdaField{1\#} \\
                 & zero \AgdaField{0\#}     & --- \\
\midrule
                 & \AgdaFunction{*} distributes over \AgdaFunction{+} &
                   \AgdaFunction{+} absorbs \AgdaFunction{*} \\
\bottomrule
\end{tabular}
\label{tab.path.algebra}
\vspace{6pt}
\caption{Comparing the algebraic properties of a semiring and a path algebra.}
\end{table}

\subsection{Models}
\label{subsect.models}

We now discuss three models (or inhabitants) of the \AgdaRecord{PathAlgebra} record to demonstrate that they exist, that path algebras are not canonical (i.e. are not inhabitable by only one structure up to isomorphism), and to use later in Section~\ref{sect.example} where we provide an example execution of our algorithm.

Trivially, the axioms of a \AgdaRecord{PathAlgebra} are satisfied by the unit type, \AgdaDatatype{⊤}.
Defining a degenerate `addition' operation on \AgdaDatatype{⊤}, we inhabit \AgdaRecord{PathAlgebra} by taking the algebra's addition and multiplication to be this operation and its two unit elements to be \AgdaInductiveConstructor{tt}, the unit value.
The axioms of the \AgdaRecord{PathAlgebra} are easily satisfied.

\AgdaHide{
\begin{code}
module Models where
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
    ∞ : ℕ∞
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
Take the algebra's addition and multiplication functions to be \AgdaFunction{\_⊓\_} and and \AgdaFunction{\_⊔\_} on \AgdaDatatype{ℕ∞}, respectively.
Take the unit for addition to be \AgdaInductiveConstructor{∞} and the unit for multiplication to be \AgdaInductiveConstructor{↑}~\AgdaInductiveConstructor{0}.
\end{enumerate}
In both cases, it is routine to check that the axioms for a \AgdaRecord{PathAlgebra} can be satisfied.
As the names suggest, executing our generalised Dijkstra algorithm with adjacency matrix coefficients taken from a shortest path algebra will compute the shortest path through the graph described by the matrix, whilst taking matrix coefficients from a widest path algebra will compute the widest path.

\section{Dijkstra's Algorithm}
\label{sect.dijkstras.algorithm}

\AgdaHide{
\begin{code}
module itp16-Algorithm
    {c ℓ} (alg : PathAlgebra c ℓ)
    {n} (i : Fin (suc n)) (adj : Adj alg (suc n))
    where

  open import Algebra.Path.Properties

  open import Data.Fin.Subset
  import Data.Fin.Subset.Extra as Sub
  open import Data.Nat using (_≤_)
  open import Data.Nat.MoreProperties using (≤-step′; sm∸n)
  open import Data.Nat.Properties using (≤-step)
  open import Data.Matrix
  import Data.Vec as V
  import Data.Vec.Sorted as Sorted

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
  A[ i , j ] = Adj.matrix adj [ i , j ]

  mutual
\end{code}
}

In this section, we introduce a generalised variant of Dijkstra's algorithm and its implementation in Agda.

Dijkstra's algorithm in its standard form finds the shortest distance from some start node \(i\) to each other node \(j\) in a graph given that no edge has a negative weight. Dynerowicz and Griffin found that a more general variant of Dijkstra's algorithm finds one row of the matrix \(R\) solving the the fixpoint equation \[R = I ⊕ (R ⊗ A)\] for some adjacency matrix \(A\) \cite{dynerowicz_forwarding_2013}. \Cref{fig.algorithm} shows the algorithm as it is presented in \cite{dynerowicz_forwarding_2013}.

Our implementation of this algorithm in Agda consists of nine mutually recursive definitions, the most important of which are \AgdaFunction{order}, \AgdaFunction{estimate}, \AgdaFunction{seen} and \AgdaFunction{queue}.

\subsubsection{\AgdaFunction{order}} Lala.

\begin{code}
    order : (ctd : ℕ) {lt : ctd ≤ n} → DecTotalOrder _ _ _
    order ctd {lt} = estimateOrder $ estimate ctd {lt}
\end{code}

\begin{code}
    estimate : (ctd : ℕ) {lt : ctd ≤ n} → Fin (suc n) → Weight
    estimate zero              j = A[ i , j ]
    estimate (suc ctd) {ctd≤n} j = r j + r q * A[ q , j ]
      where
        q = Sorted.head (order ctd {≤-step′ ctd≤n}) (queue ctd {ctd≤n})
        r = estimate ctd {≤-step′ ctd≤n}
\end{code}

\AgdaHide{
\begin{code}
    seen : (ctd : ℕ) {lt : ctd ≤ n} → Subset (suc n)
    seen zero              = ⁅ i ⁆
    seen (suc ctd) {ctd≤n} =
      seen ctd {≤-step′ ctd≤n} ∪
      ⁅ Sorted.head (order ctd {≤-step′ ctd≤n}) (queue ctd {ctd≤n}) ⁆

    queue′ : (ctd : ℕ) {lt : ctd ≤ n} → Sorted.SortedVec _ (Sub.size $ ∁ $ seen ctd {lt})
    queue′ ctd {lt} = Sorted.fromVec (order ctd {lt}) $ Sub.toVec $ ∁ $ seen ctd

    queue : (ctd : ℕ) {lt : suc ctd ≤ n} → Sorted.SortedVec _ (suc (n ∸ (suc ctd)))
    queue ctd {ctd<n} = P.subst (Sorted.SortedVec (order ctd {≤-step′ ctd<n})) (queue-size ctd {ctd<n}) (queue′ ctd)

    queue⇒queue′ : (ctd : ℕ) {lt : suc ctd ≤ n} → ∀ {p} (P : ∀ {n} →
                   Sorted.SortedVec _ n → Set p) → P (queue′ ctd) → P (queue ctd {lt})
    queue⇒queue′ ctd {lt} P Pqueue = super-subst P (≡-to-≅ (queue-size ctd {lt})) (H.sym H-lemma) Pqueue
      where
        open import Relation.Binary.HeterogeneousEquality as H
        open Sorted (order ctd {≤-step′ lt})

        super-subst : ∀ {m n p} → {xs : SortedVec m} → {ys : SortedVec n} → (P : ∀ {n} → SortedVec n → Set p) →
                      m H.≅ n → xs H.≅ ys → P xs → P ys
        super-subst P H.refl H.refl Pxs = Pxs

        H-lemma : queue ctd ≅ queue′ ctd
        H-lemma = ≡-subst-removable SortedVec (queue-size ctd {lt}) (queue′ ctd)

    seen-size : (ctd : ℕ) {lt : ctd ≤ n} → Sub.size (seen ctd {lt}) ≡ suc ctd
    seen-size zero           = Sub.size⁅i⁆≡1 i
    seen-size (suc ctd) {lt} =
      begin
        Sub.size (seen ctd ∪ ⁅ q ⁆)  ≡⟨ P.cong Sub.size (∪-comm (seen ctd) ⁅ q ⁆) ⟩
        Sub.size (⁅ q ⁆ ∪ seen ctd)  ≡⟨ Sub.size-suc q (seen ctd) (q∉seen ctd) ⟩
        suc (Sub.size (seen ctd))    ≡⟨ P.cong suc (seen-size ctd) ⟩
        suc (suc ctd)
      ∎
      where
        open P.≡-Reasoning
        open Sub.Properties (suc n)
        q = Sorted.head (order ctd {≤-step′ lt}) (queue ctd {lt})

    queue-size : (ctd : ℕ) {lt : suc ctd ≤ n} → Sub.size (∁ (seen ctd {≤-step′ lt})) ≡ suc (n ∸ suc ctd)
    queue-size ctd {lt} =
      begin
        Sub.size (∁ (seen ctd))      ≡⟨ Sub.∁-size (seen ctd) ⟩
        suc n ∸ Sub.size (seen ctd)  ≡⟨ P.cong₂ _∸_ P.refl (seen-size ctd) ⟩
        suc n ∸ suc ctd              ≡⟨ sm∸n n (suc ctd) lt ⟩
        suc (n ∸ suc ctd)
      ∎
      where
        open P.≡-Reasoning

    q∉seen : (ctd : ℕ) {lt : suc ctd ≤ n} → Sorted.head _ (queue ctd {lt}) ∉ seen ctd {≤-step′ lt}
    q∉seen ctd {lt} q∈vs = q∉q∷qs (S.here qs q≼qs)
      where
        module S = Sorted (order ctd {≤-step′ lt})

        q = S.head (queue ctd {lt})
        qs = S.tail (queue ctd {lt})
        q≼qs = S.≼-proof (queue ctd {lt})

        q∉queue′ : ¬ (q S.∈ (queue′ ctd))
        q∉queue′ = S.fromVec-∉¹ (Sub.toVec-∉¹ (Sub.∁-∈ q∈vs))

        q∉queue : ¬ (q S.∈ (queue ctd {lt}))
        q∉queue = queue⇒queue′ ctd {lt} (λ qs → ¬ (q S.∈ qs)) q∉queue′

        q∉q∷qs : ¬ (q S.∈ (q S.∷ qs ⟨ q≼qs ⟩))
        q∉q∷qs = P.subst (λ qs → ¬ (q S.∈ qs)) S.destruct q∉queue
\end{code}
}

% dpm: temporarily removed as it was messing up formatting
%\begin{figure}[h]
%\includegraphics{algorithm.pdf}
%\caption{Imperative generalised Dijkstra's algorithm \cite[p.~9]{dynerowicz_forwarding_2013}}
%\label{fig.algorithm}
%\end{figure}

\section{Correctness}
\label{sect.correctness}

\section{Example}
\label{sect.example}

\section{Conclusions}
\label{sect.conclusions}

\paragraph{Related Work}

\paragraph{Future Work}

\paragraph{Resources}

The Dijkstra formalisation and all supporting files are available anonymously from a public \texttt{git} repository~\cite{markert_dijkstra_2015}.
Documentation for type checking the formalisation is available in the repository.
The formalisation consists of approximately 2,400 lines of Agda and was developed using Agda~2.4.2.1 and~2.4.2.2 and Standard Library version~0.9.

\bibliography{path-algebra}

\end{document}
