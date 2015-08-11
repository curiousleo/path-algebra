\documentclass{llncs}

\usepackage{agda}
\usepackage[british]{babel}
\usepackage{cite}
\usepackage{microtype}

\begin{document}

\title{Dijkstra's algorithm: verified}
\titlerunning{Dijkstra's algorithm}
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

\subsection{Shortest paths and equilibrium routing}
\label{subsect.shortest.paths.and.equilibrium.routing}

\subsection{Contributions}
\label{subsect.contributions}

\subsection{Agda}
\label{subsect.agda}

\subsection{Map of paper}
\label{subsect.map.of.paper}

\section{Formalising Dijkstra's algorithm}
\label{sect.formalising.dijkstra.algorithm}

\subsection{Basic definitions}
\label{subsect.basic.definitions}

\subsection{Sorted vectors}
\label{subsect.sorted.vectors}

\begin{code}
data Test : Set where
  test : Test
\end{code}

\subsection{Dijkstra algebras and their models}
\label{subsect.dijkstra.algebras.and.their.models}

\subsection{Towards correctness}
\label{subsect.towards.correctness}

\section{Conclusions}
\label{sect.conclusions}

\subsection{Related work}
\label{subsect.related.work}

\subsection{Future work}
\label{subsect.future.work}

%\bibliography{path-algebra}

\end{document}
