\documentclass{llncs}

\usepackage{agda}
\usepackage[british]{babel}
\usepackage{cite}
\usepackage[colorlinks]{hyperref}
\usepackage{microtype}

\bibliographystyle{splncs03}

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
\keywords{Dijkstra's algorithm, shortest paths, internet routing, interactive theorem proving}
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

\subsection{Sorted Vectors}
\label{subsect.sorted.vectors}

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
