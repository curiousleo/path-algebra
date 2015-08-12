\documentclass{llncs}

\usepackage{agda}
\usepackage{amsmath}
\usepackage[british]{babel}
\usepackage{booktabs}
\usepackage{cite}
\usepackage{csquotes}
\usepackage[colorlinks]{hyperref}
\usepackage{microtype}

\setlength{\tabcolsep}{6pt}

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

\subsection{Sorted Vectors}
\label{subsect.sorted.vectors}

% Need to mention AVL trees in standard library

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
\end{code}

\subsection{Path Algebras and Their Models}
\label{subsect.path.algebras.and.their.models}

We refer to the weakest algebraic structure for which we could prove the correctness of Dijkstra's algorithm as a \emph{path algebra}. For clarity, we introduce it here by comparing it to a \emph{semiring}.

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
