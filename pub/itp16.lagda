\documentclass{llncs}

\usepackage{agda}
\usepackage{amsmath}
\usepackage[british]{babel}
\usepackage{booktabs}
\usepackage{cite}
\usepackage{color}
\usepackage{csquotes}
\usepackage{graphics}
\usepackage[colorlinks]{hyperref}
\usepackage[noabbrev,capitalise]{cleveref}
\usepackage{microtype}
\usepackage{stmaryrd}
\usepackage{textgreek}

\setlength{\tabcolsep}{6pt}

\bibliographystyle{splncs03}

\DeclareUnicodeCharacter{ 8261}{\ensuremath{\llbracket}} % ⟦ (really ⁅)
\DeclareUnicodeCharacter{ 8262}{\ensuremath{\rrbracket}} % ⟧ (really ⁆)
\DeclareUnicodeCharacter{ 8718}{\ensuremath{\square}} % □ (really ∎)
\DeclareUnicodeCharacter{ 8760}{\ensuremath{\overset{\cdot}{\vphantom{.}\smash{-}}}} % -} ∸
\DeclareUnicodeCharacter{ 8799}{\ensuremath{\overset{?}{\vphantom{o}\smash{=}}}} % ≟
\DeclareUnicodeCharacter{ 8759}{\ensuremath{::}} % ∷
\DeclareUnicodeCharacter{10753}{\ensuremath{\bigoplus}}
\DeclareUnicodeCharacter{  737}{\ensuremath{{}^{l}}} % ˡ
\DeclareUnicodeCharacter{ 7522}{\ensuremath{{}_{i}}} % ᵢ
\DeclareUnicodeCharacter{11388}{\ensuremath{{}_{j}}} % ⱼ
\DeclareUnicodeCharacter{ 7524}{\ensuremath{{}_{u}}} % ᵤ
\DeclareUnicodeCharacter{ 7480}{\ensuremath{\ell}} % ℓ

\newcommand{\todo}[1]{{\color{red}{\ensuremath{\texttt{[TODO: #1]}}}}}

\begin{document}

\AgdaHide{
\begin{code}
module itp16 where

open import Algebra.Path.Structure
import Data.Matrix.Adjacency as MAdj

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
  using (ℕ; zero; suc; _∸_; z≤n)
  renaming (_≤_ to _N≤_)
\end{code}
}

\title{On the Correctness of a Generalised Shortest Path Algorithm}
\titlerunning{Generalised Shortest Path Algorithm}
\author{Leonhard D.~Markert \and Timothy G.~Griffin \and Dominic P.~Mulligan}
\authorrunning{Leonhard Markert et al.}
\institute{Computer Laboratory, University of Cambridge}

\maketitle

\begin{abstract}
We present an implementation and proof of correctness of a shortest path graph algorithm in Agda.
The shortest path algorithm computes locally optimal shortest paths, in contrast to algorithms like Floyd-Warshall and Dijkstra which both compute globally optimal paths.
Shortest path algorithms of this form are applied in Internet routing.

Following Dynerowicz and Griffin, our proof of correctness is algebraic in character.
In particular, given an adjacency matrix with coefficients taken from the carrier set of a Path Algebra---a semiring-like algebraic structure---our algorithm computes one row of the right-local solution to a matrix fixpoint equation.
Our implementation and proof of correctness make essential use of dependent types and some of Agda's more cutting-edge features, such as induction-recursion.

% The abstract should summarize the contents of the paper
% using at least 70 and at most 150 words. It will be set in 9-point

\keywords{Dijkstra's algorithm, shortest paths, internet routing, interactive theorem proving, Agda}
\end{abstract}

\section{Introduction}
\label{sect.introduction}

\paragraph{Contributions and map of paper}

\subsection{Agda}
\label{subsect.agda}

Agda~\cite{norell_dependently_2009} is a dependently-typed functional programming language \emph{cum} proof assistant for higher-order intuitionistic logic.
In contrast to similar systems, such as Coq~\cite{bertot_short_2008} and Matita~\cite{asperti_matita_2011}, proof terms are constructed by hand via a process of type-directed refinement, rather than being constructed via tactic-assisted metaprogramming.

Agda has a uniform syntax that should be familiar to Haskell programmers and users of other dependently-typed proof assistants.
One syntactic novelty is a flexible system of user-declared Unicode mixfix identifiers~\cite{danielsson_parsing_2011} with `holes' in an identifier being denoted by underscores.

We write \AgdaSymbol{(}\AgdaBound{x}~\AgdaSymbol{:}~\AgdaBound{A}\AgdaSymbol{)}~\AgdaSymbol{→}~\AgdaBound{B} for the dependent function space where \AgdaBound{x} may occur in \AgdaBound{B}, and write \AgdaBound{A}~\AgdaSymbol{→}~\AgdaBound{B} when \AgdaBound{x} does not occur in \AgdaBound{B} as is usual.
We enclose arguments to be inferred in braces, as in \AgdaSymbol{\{}\AgdaBound{x}~\AgdaSymbol{:}~\AgdaBound{A}\AgdaSymbol{\}}~\AgdaSymbol{→}~\AgdaBound{B}, sometimes making use of the shorthands \AgdaSymbol{∀}~\AgdaBound{x}~\AgdaSymbol{→}~\AgdaBound{B} and \AgdaSymbol{∀}~\AgdaSymbol{\{}\AgdaBound{x}\AgdaSymbol{\}}~\AgdaSymbol{→}~\AgdaBound{B} when types can be inferred.
We write \AgdaDatatype{Σ}~\AgdaBound{A}~\AgdaBound{B} for the dependent sum type whose first projection has type \AgdaBound{A}, and write \AgdaBound{A}~\AgdaDatatype{×}~\AgdaBound{B} when the second projection does not depend on the first, as is usual.
Dependent sums are constructed using the comma constructor: \AgdaBound{x}~\AgdaInductiveConstructor{,}~\AgdaBound{y}.
We sometimes write \AgdaFunction{∃}~\AgdaSymbol{λ}~\AgdaBound{x}~\AgdaSymbol{→}~\AgdaBound{P} for the dependent sum type when the type of the first projection can be inferred.
Propositional equality between two types is written \AgdaBound{A}~\AgdaDatatype{≡}~\AgdaBound{B} and has a single canonical inhabitant, \AgdaInductiveConstructor{refl}.
Lastly, we write \AgdaBound{A}~\AgdaDatatype{⊎}~\AgdaBound{B} for the disjoint union type with constructors \AgdaInductiveConstructor{inj₁} and \AgdaInductiveConstructor{inj₂} and \AgdaFunction{¬}~\AgdaBound{A} for constructive negation.

Agda is a predicative type theory with an infinite universe hierarchy, \AgdaPrimitiveType{Setᵢ}, with \AgdaPrimitiveType{Set}---the type of small types---being identified with \AgdaPrimitiveType{Set₀}, the base universe in Agda's hierarchy.
As a matter of course universe \AgdaPrimitiveType{Setᵢ} is not automatically contained in \AgdaPrimitiveType{Setⱼ} when $i < j$ and requires explicit lifting with \AgdaFunction{Lift}.
Universe polymorphism is used extensively throughout this development, with explicit quantification over universe levels.

%\subsection{Map of Paper}
%\label{subsect.map.of.paper}
%In Section~\ref{sect.basic.definitions} we cover some definitions needed to define Dijkstra's algorithm and its correctness proof.
%In Section~\ref{sect.path.algebras.their.properties.and.models} we discuss `path algebras', a variety of algebraic structure central to our proof of correctness, also providing three models of path algebras to demonstrate that models exist and that path algebras are not categorical.
%In Section~\ref{sect.dijkstras.algorithm.and.its.correctness} we discuss the imperative Dijkstra algorithm, our functional implementation, and main body of the correctness proof leading up to our main theorem: Dijkstra's algorithm computes a right-local solution.
%In Section~\ref{sect.example} we demonstrate the algorithm in action with an example execution inside Agda.
%In Section~\ref{sect.conclusions} we conclude.

\section{Basic definitions}
\label{sect.basic.definitions}

\subsection{Matrices and graph nodes}
\label{subsect.matrices.and.graph.nodes}

We write \AgdaDatatype{Vec}~\AgdaBound{A}~\AgdaBound{n} for the length-indexed list, or vector, containing elements of type \AgdaBound{A} with length \AgdaBound{n}.
We write \AgdaDatatype{Matrix}~\AgdaBound{A}~\AgdaBound{m}~\AgdaBound{n} for the type of $m \times n$-dimensional matrices containing elements of type $A$, implemented as a vector of vectors.
We use finite sets, where \AgdaDatatype{Fin}~\AgdaBound{n} is intuitively the type of natural numbers `of at most $n$', to index into matrices and represent graph nodes in our formalisation.
The type \AgdaDatatype{Fin}~\AgdaBound{n} has a decidable equality for all $n$.
We use the existing standard library definition of \AgdaDatatype{Subset}, which partitions a finite set into elements that lie `inside' and `outside' of the set, to capture the notion of sets of nodes.

Assume an algebraic structure with carrier type \AgdaField{Carrier}, a decidable equality \AgdaField{\_≈\_} and left multiplicative identity \AgdaField{1\#} (structures of this form will be further discussed in Section~\ref{sect.path.algebras.their.properties.and.models}).
We define an $m$-dimensional adjacency matrix over this structure as a record \AgdaRecord{Adj} parameterised by a dimension:

\AgdaHide{
\begin{code}
module itp16-Adj {c ℓ} (alg : PathAlgebra c ℓ) where
  open import Level

  open import Data.Fin using (Fin)
  open import Data.Matrix
  open import Data.Nat.Base using (ℕ)

  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)

  open PathAlgebra alg renaming (Carrier to Weight)
\end{code}
}

% TODO: explain universe levels (ie, where do c and ℓ come from?)
\begin{code}
  record Adj (n : ℕ) : Set (c ⊔ ℓ) where
    field
      matrix  : Matrix Weight n n
      diag    : ∀ i → matrix [ i , i ] ≈ 1#
\end{code}

Here, a field of type \AgdaDatatype{Matrix}~\AgdaField{Carrier}~\AgdaBound{m}~\AgdaBound{m} is bundled with a proof that all diagonal elements of this matrix are equivalent to \AgdaField{1\#}.

\subsection{Sums}
\label{subsect.sums}

By `sum' we refer to the lifting of a binary operator over an indexed set, like $\bigoplus_{x ∈ X} f(x)$~\cite{bertot_canonical_2008}.
The properties of the Path Algebra addition operator, \AgdaFunction{\_+\_}, include associativity, commutative and idempotence.
In combination, these properties allow us to make strong claims about the behaviour of edge weight sums. 

For convenience, we define path weight sums over commutative monoids since they are well supported by the standard library.
A proof of idempotency is required explicitly whenever needed.

Key to understanding this section is knowledge of the family of types, \AgdaFunction{Subset}~\AgdaBound{n}, describing subsets of finite sets of size \AgdaBound{n}, and implemented in the \AgdaModule{Data.Fin.Subset} module of the Agda standard library.
\AgdaFunction{Subset}~\AgdaBound{n} is a fixed-length list of length \AgdaBound{n}.
At each index \AgdaBound{i} of the vector are one of two flags---\AgdaInductiveConstructor{inside} or \AgdaInductiveConstructor{outside}---denotating whether the $i^\mathrm{th}$ element of the finite set in question is inside or outside the described subset, i.e. a partitioning of a finite set into two new sets.

We use the function \AgdaFunction{fold} to define sums over subsets of finite sets using the underlying monoid's identity element \AgdaField{ε} and binary operator \AgdaField{\_∙\_}:

\AgdaHide{
\begin{code}
module itp16-Bigop
    {c ℓ} (cmon : CommutativeMonoid c ℓ)
    where

  open import Data.Fin hiding (fold; fold′)
  open import Data.Fin.Subset
  open import Data.Fin.Subset.Extra using (empty→⊥) renaming (nonempty to nonempty-dec)
  open import Data.Nat hiding (fold)
  open import Data.Product hiding (map; zip)
  open import Data.Vec hiding (_∈_)

  open import Function using (_∘_; id)

  open import Relation.Nullary using (yes; no)

  open CommutativeMonoid cmon
\end{code}
}

\begin{code}
  fold : ∀ {n} → (Fin n → Carrier) → Subset n → Carrier
  fold f []              = ε
  fold f (inside ∷ xs)   = f zero ∙  fold (f ∘ suc) xs
  fold f (outside ∷ xs)  =           fold (f ∘ suc) xs
\end{code}
Intuitively, for a subset of a finite set of size \AgdaBound{n}, the function call \AgdaFunction{fold}~\AgdaBound{f}~\AgdaBound{xs} enumerates all \AgdaBound{n} possible elements of the set, testing each in turn whether it is an element of the subset described by \AgdaBound{xs}, acting on the element if so, ignoring it otherwise.
For convenience we provide a \AgdaKeyword{syntax} declaration for \AgdaFunction{fold}, so that the notation $\AgdaFunction{⨁[}~\AgdaBound{x}~\AgdaFunction{←}~\AgdaBound{v}~\AgdaFunction{]}~\AgdaBound{e}$ denotes the application \AgdaFunction{fold}~(\AgdaSymbol{λ}~\AgdaBound{x}~\AgdaSymbol{→}~\AgdaBound{e})~\AgdaBound{v}.

\AgdaHide{
\begin{code}
  infix 6 ⨁-syntax
\end{code}
\begin{code}
  ⨁-syntax = fold
  syntax ⨁-syntax (λ x → e) v = ⨁[ x ← v ] e
\end{code}}
\AgdaHide{
\begin{code}
  open import Algebra.FunctionProperties _≈_

  open import Data.Empty using (⊥-elim)

  open import Relation.Binary.EqReasoning setoid
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_)
\end{code}}

We now show that sums over commutative monoids have certain properties, of which we present only a selection of the most useful or interesting.
We omit proofs, all of which proceed by straightforward case analysis or induction, unless otherwise stated.
Trivially, we have that folding over an empty set is equivalent to the neutral element of the monoid, and folding over a singleton set containing an element \AgdaBound{i} is equivalent to applying the function \AgdaBound{f} to \AgdaBound{i}.
These facts are expressed as the lemmas \AgdaFunction{fold-⊥} and \AgdaFunction{fold-⁅i⁆}, respectively:
\begin{code}
  fold-⊥ : ∀ {n} f → fold f (⊥ {n}) ≈ ε
  
  fold-⁅i⁆ : ∀ {n} f (i : Fin n) → fold f ⁅ i ⁆ ≈ f i
\end{code}  
\AgdaHide{
\begin{code}
  fold-⊥ {zero}   f = refl
  fold-⊥ {suc n}  f = fold-⊥ (f ∘ suc)
\end{code}}
\AgdaHide{
\begin{code}
  fold-⁅i⁆ f zero =
    begin
      f zero ∙ fold (f ∘ suc) ⊥  ≈⟨ ∙-cong refl (fold-⊥ (f ∘ suc)) ⟩
      f zero ∙ ε                 ≈⟨ proj₂ identity _ ⟩
      f zero
    ∎
  fold-⁅i⁆ f (suc i) = fold-⁅i⁆ (f ∘ suc) i
\end{code}}
Here, \AgdaFunction{⊥} is the empty set, and $\AgdaFunction{⁅}~\AgdaBound{i}~\AgdaFunction{⁆}$ is a singleton set containing only \AgdaBound{i}.
Folding a function \AgdaBound{f} over a union of two subsets, \AgdaBound{xs} and \AgdaBound{ys}, is equivalent to folding over \AgdaBound{xs} and \AgdaBound{ys} separately and combining the two results with the commutative monoid's binary operator, \AgdaField{\_∙\_}, whenever the operator is idempotent, as expressed by the following lemma, \AgdaFunction{fold-∪}:

\begin{code}
  fold-∪ :  ∀ {n} (idp : Idempotent _∙_) f (xs : Subset n) (ys : Subset n) →
            fold f (xs ∪ ys) ≈ fold f xs ∙ fold f ys
\end{code}

The proof proceeds by simultaneous induction on both subsets, combined with equational reasoning.
For each element of the two sets we must consider whether it lies inside or outside of the subsets being described by \AgdaBound{xs} and \AgdaBound{ys}.
We present a single case, \AgdaInductiveConstructor{inside}-\AgdaInductiveConstructor{inside}:

\AgdaHide{
\begin{code}
  fold-∪ idp f []             []             = sym (proj₁ identity _)
\end{code}}
\begin{code}
  fold-∪ idp f (inside ∷ xs)  (inside ∷ ys)  =
    begin
      f zero ∙ fold (f ∘ suc) (xs ∪ ys)
    ≈⟨ ∙-cong (sym (idp _)) (fold-∪ idp (f ∘ suc) xs ys) ⟩
      (f zero ∙ f zero) ∙ (fold (f ∘ suc) xs ∙ fold (f ∘ suc) ys)
    ≈⟨ assoc _ _ _ ⟩
      f zero ∙ (f zero ∙ (fold (f ∘ suc) xs ∙ fold (f ∘ suc) ys))
    ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
      f zero ∙ ((f zero ∙ fold (f ∘ suc) xs) ∙ fold (f ∘ suc) ys)
    ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
      f zero ∙ ((fold (f ∘ suc) xs ∙ f zero) ∙ fold (f ∘ suc) ys)
    ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
      f zero ∙ (fold (f ∘ suc) xs ∙ (f zero ∙ fold (f ∘ suc) ys))
    ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ fold (f ∘ suc) xs) ∙ (f zero ∙ fold (f ∘ suc) ys)
    ∎
\end{code}

\AgdaHide{
\begin{code}
  fold-∪ idp f (inside ∷ xs) (outside ∷ ys) =
    begin
      f zero ∙ fold (f ∘ suc) (xs ∪ ys)
    ≈⟨ ∙-cong refl (fold-∪ idp (f ∘ suc) xs ys) ⟩
      f zero ∙ (fold (f ∘ suc) xs ∙ fold (f ∘ suc) ys)
    ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ fold (f ∘ suc) xs) ∙ fold (f ∘ suc) ys
    ∎
  fold-∪ idp f (outside ∷ xs) (inside  ∷ ys) =
    begin
      f zero ∙ fold (f ∘ suc) (xs ∪ ys)
    ≈⟨ ∙-cong refl (fold-∪ idp (f ∘ suc) xs ys) ⟩
      f zero ∙ (fold (f ∘ suc) xs ∙ fold (f ∘ suc) ys)
    ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ fold (f ∘ suc) xs) ∙ fold (f ∘ suc) ys
    ≈⟨ ∙-cong (comm _ _) refl ⟩
      (fold (f ∘ suc) xs ∙ f zero) ∙ fold (f ∘ suc) ys
    ≈⟨ assoc _ _ _ ⟩
      fold (f ∘ suc) xs ∙ (f zero ∙ fold (f ∘ suc) ys)
    ∎
  fold-∪ idp f (outside ∷ xs) (outside ∷ ys) = fold-∪ idp (f ∘ suc) xs ys
\end{code}}

\AgdaHide{
\begin{code}
  fold-cong-lemma : ∀ {n} (f g : Fin (suc n) → Carrier) x (xs : Subset n) →
                    (∀ i → i ∈ (x ∷ xs) → f i ≈ g i) → (∀ i → i ∈ xs → f (suc i) ≈ g (suc i))
\end{code}
\begin{code}
  fold-cong-lemma f g x [] eq i ()
  fold-cong-lemma f g x (inside ∷ ys) eq i i∈y∷ys = eq (suc i) (there i∈y∷ys)
  fold-cong-lemma f g x (outside ∷ ys) eq zero ()
  fold-cong-lemma f g x (outside ∷ ys) eq (suc i) (there i∈y∷ys) = fold-cong-lemma (f ∘ suc) (g ∘ suc) outside ys (λ i x → eq (suc i) (there x)) i i∈y∷ys
\end{code}}

Here, \AgdaFunction{assoc}, \AgdaFunction{sym}, and \AgdaFunction{∙-cong} are the associativity, symmetry, and congruence with respect to setoid-equivalence properties of the underlying commutative monoid, respectively.
Finally, we demonstrate an extensionality property, namely that folding two different functions across the same set results in equivalent values if the functions agree pointwise on all elements in the set.
This is expressed in the lemma \AgdaFunction{fold-cong}: 

\begin{code}
  fold-cong :  ∀ {n} f g (xs : Subset n) → (∀ i → i ∈ xs → f i ≈ g i) →
               fold f xs ≈ fold g xs
\end{code}

\AgdaHide{
\begin{code}
  fold-cong f g []             eq = refl
  fold-cong f g (inside  ∷ xs) eq = ∙-cong (eq zero here) (fold-cong (f ∘ suc) (g ∘ suc) xs (fold-cong-lemma f g inside xs eq))
  fold-cong f g (outside ∷ xs) eq = fold-cong (f ∘ suc) (g ∘ suc) xs (fold-cong-lemma f g outside xs eq)
\end{code}}

\noindent
The proof proceeds by induction on $\AgdaBound{xs}$ and is omitted.

\AgdaHide{
\begin{code}
  fold-distr : ∀ {n} f x (i : Fin n) → fold (λ i → x ∙ f i) ⁅ i ⁆ ≈ x ∙ fold f ⁅ i ⁆
\end{code}
\begin{code}
  fold-distr {suc n} f x zero =
    begin
      (x ∙ f zero) ∙ fold ((λ i → x ∙ f i) ∘ suc) ⊥  ≈⟨ ∙-cong refl (fold-⊥ {n} _) ⟩
      (x ∙ f zero) ∙ ε                                ≈⟨ assoc _ _ _ ⟩
      x ∙ (f zero ∙ ε)                                ≈⟨ ∙-cong refl (∙-cong refl (sym (fold-⊥ {n} _))) ⟩
      x ∙ (f zero ∙ fold (f ∘ suc) ⊥)
    ∎
  fold-distr f x (suc i) = fold-distr (f ∘ suc) x i
\end{code}}

\AgdaHide{
\begin{code}
  fold-empty : ∀ {n} f (xs : Subset n) → Empty xs → fold f xs ≈ ε
\end{code}
\begin{code}
  fold-empty f [] empty = refl
  fold-empty f (inside  ∷ xs) empty = ⊥-elim (empty nonempty)
    where
      nonempty : Nonempty (inside ∷ xs)
      nonempty = zero , here
  fold-empty f (outside ∷ xs) empty = fold-empty (f ∘ suc) xs (empty′ xs empty)
    where
      empty′ : ∀ {n} (xs : Subset n) → Empty (outside ∷ xs) → Empty xs
      empty′ []             empty (x , ())
      empty′ (inside  ∷ xs) empty nonempty  = ⊥-elim (empty (suc zero , there here))
      empty′ (outside ∷ xs) empty (i , elm) = ⊥-elim (empty (suc i , there  elm))
\end{code}}

\AgdaHide{
\begin{code}
  fold-distr′ : ∀ {n} (idp : Idempotent _∙_) f x (xs : Subset n) → Nonempty xs →
                fold (λ i → x ∙ f i) xs ≈ x ∙ fold f xs
\end{code}
\begin{code}
  fold-distr′ idp f x [] (_ , ())
  fold-distr′ idp f x (inside ∷ xs) (zero , here) with nonempty-dec xs
  ... | yes nonempty-xs =
    begin
      (x ∙ f zero) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ ∙-cong (comm _ _) refl ⟩
      (f zero ∙ x) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
      f zero ∙ (x ∙ fold (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-distr′ idp (f ∘ suc) x xs nonempty-xs)) ⟩
      f zero ∙ (x ∙ (x ∙ fold (f ∘ suc ) xs))       ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
      f zero ∙ ((x ∙ x) ∙ fold (f ∘ suc ) xs)       ≈⟨ ∙-cong refl (∙-cong (idp _) refl) ⟩
      f zero ∙ (x ∙ fold (f ∘ suc ) xs)             ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ x) ∙ fold (f ∘ suc ) xs             ≈⟨ ∙-cong (comm _ _) refl ⟩
      (x ∙ f zero) ∙ fold (f ∘ suc ) xs             ≈⟨ assoc _ _ _ ⟩
      x ∙ (f zero ∙ fold (f ∘ suc) xs)
    ∎
  ... | no ¬nonempty-xs =
    begin
      (x ∙ f zero) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
      x ∙ (f zero ∙ fold (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-empty (λ i → x ∙ f (suc i)) xs ¬nonempty-xs)) ⟩
      x ∙ (f zero ∙ ε)                               ≈⟨ sym (∙-cong refl (∙-cong refl (fold-empty (f ∘ suc) xs ¬nonempty-xs))) ⟩
      x ∙ (f zero ∙ fold (λ i → f (suc i)) xs)
    ∎
  fold-distr′ idp f x (inside ∷ xs) (suc i , there i∈xs) =
    begin
      (x ∙ f zero) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ ∙-cong (comm _ _) refl ⟩
      (f zero ∙ x) ∙ fold (λ i → x ∙ f (suc i)) xs  ≈⟨ assoc _ _ _ ⟩
      f zero ∙ (x ∙ fold (λ i → x ∙ f (suc i)) xs)  ≈⟨ ∙-cong refl (∙-cong refl (fold-distr′ idp (f ∘ suc) x xs (i , i∈xs))) ⟩
      f zero ∙ (x ∙ (x ∙ fold (f ∘ suc ) xs))       ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
      f zero ∙ ((x ∙ x) ∙ fold (f ∘ suc ) xs)       ≈⟨ ∙-cong refl (∙-cong (idp _) refl) ⟩
      f zero ∙ (x ∙ fold (f ∘ suc ) xs)             ≈⟨ sym (assoc _ _ _) ⟩
      (f zero ∙ x) ∙ fold (f ∘ suc ) xs             ≈⟨ ∙-cong (comm _ _) refl ⟩
      (x ∙ f zero) ∙ fold (f ∘ suc ) xs             ≈⟨ assoc _ _ _ ⟩
      x ∙ (f zero ∙ fold (f ∘ suc) xs)
    ∎
  fold-distr′ idp f x (outside ∷ xs) (suc i , there i∈xs) = fold-distr′ idp (f ∘ suc) x xs (i , i∈xs)
\end{code}
}

% Representation of algebraic structures as records
% Setoid, Equivalence

% Subset, Bigop, EstimateOrder

\subsection{Sorted vectors}
\label{subsect.sorted.vectors}

% Need to mention AVL trees in standard library

Dijkstra's algorithm fixes the order that nodes in a graph are visited by maintaining a priority queue of previously unvisited nodes---the node with the lowest priority in this queue is the node that will be considered next by the algorithm.\footnote{How these priorities are assigned to a node in our particular implementation of Dijkstra's algorithm will be further discussed in Section~\ref{sect.dijkstras.algorithm.and.its.correctness}.}
In this Subsection we define an indexed family of types of sorted vectors that we will use in Section~\ref{sect.dijkstras.algorithm.and.its.correctness} to implement this priority queue of unvisited nodes.
Here, for generality we keep the particular type used to implement priorties abstract, and any type with a decidable total order structure defined over them will suffice.

Note that we prefer working with a linear sorted data structure, compared to a balanced binary tree such as Agda's existing implementation of AVL trees in \AgdaModule{Data.AVL}, to simplify proofs.
Using a length-indexed data structure also allows us to straightforwardly statically assert the non-emptiness of our priority queue by mandating that the queue's length must be of the form \AgdaInductiveConstructor{suc}~\AgdaBound{n}, for some $n$.

Throughout this Section we fix and open a decidable total order record, \AgdaRecord{DecTotalOrder}.
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

% dpm: not mentioned anywhere, now?  commented out...
%Appending two vectors, \AgdaFunction{\_++\_}, can be defined easily by repeatedly inserting elements from the first vector into the second.
%Append is given the usual precise type signature:

\AgdaHide{
\begin{code}
  _++_ : ∀ {m n} → SortedVec m → SortedVec n → SortedVec (m + n)
\end{code}
\begin{code}
  []                ++ ys = ys
  (x ∷ xs ⟨ x≼xs ⟩) ++ ys = insert x (xs ++ ys)
\end{code}}

Functions that take the head of a vector, \AgdaFunction{head}, append two vectors together, \AgdaFunction{\_++\_}, and so on, can be given the precise types one usually expects when working with vectors.
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

The proof proceeds by analysing the cases under which \AgdaBound{x}~\AgdaFunction{∈}~\AgdaBound{xs}, and affirms the suitability of \AgdaDatatype{SortedVec} as a priority queue implementation.

\section{Path Algebras, their properties and models}
\label{sect.path.algebras.their.properties.and.models}

\subsection{Path Algebras}
\label{subsect.path.algebras}

\AgdaHide{
\begin{code}
open import Level using (_⊔_)
open import Relation.Binary

module MoreFunctionProperties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

  open import Algebra.FunctionProperties _≈_

  open import Data.Sum
\end{code}}

\begin{figure}[t]
\centering
\begin{tabular}{c||l@{\;\;\;}|l}
\textbf{Operation} & \textbf{Semiring} & \textbf{Path Algebra} \\
\midrule
\AgdaFunction{\_+\_} & Associative & Associative \\
                 & Commutative & Commutative \\
                 & Identity: \AgdaField{0\#} & Identity: \AgdaField{0\#} \\
                 & ---                      & Selective \\
                 & ---                      & Zero: \AgdaField{1\#} \\
\midrule
\AgdaFunction{\_*\_} & Associative & --- \\
                 & Identity: \AgdaField{1\#} & Left identity: \AgdaField{1\#} \\
                 & Zero: \AgdaField{0\#}     & --- \\
\midrule
\AgdaFunction{\_*\_} and \AgdaFunction{\_+\_} & \AgdaFunction{\_*\_} distributes over \AgdaFunction{\_+\_} &
                   \AgdaFunction{\_+\_} absorbs \AgdaFunction{\_*\_} \\
\bottomrule
\end{tabular}
\label{tab.path.algebra}
\vspace{6pt}
\caption{Comparing the algebraic properties of a Semiring and a Path Algebra.}
\label{fig.path.algebra}
\end{figure}

Fix a set $S$ and an equivalence relation $- ≈ -$.
Call a binary operation on $S$, $- \bullet -$, \emph{selective} when for all $x, y \in S$ either $x \bullet y ≈ x$ or $x \bullet y ≈ y$.
With this definition in mind, we call a structure $\langle S, +, *, 0, 1 \rangle$ a `Path Algebra' when:
\begin{itemize}
\item
$\langle S, +, 0 \rangle$ forms a commutative monoid,
\item
$1$ is a left identity for multiplication, and a left- and right zero for addition,
\item
addition is selective, and addition absorbs multiplication,
\item
the usual closure properties for the unit elements and operations apply.
\end{itemize}
A comparison between Path Algebras and the more familiar notion of Semiring is presented in Figure~\ref{fig.path.algebra}.

Following established convention, we capture the notion of a path algebra as an Agda record named \AgdaRecord{PathAlgebra}.
We call the carrier type of a Path Algebra (the set $S$ in the definition above) \AgdaField{Carrier}, obtaining the closure properties mentioned above for `free' as a side-effect of Agda's typing discipline, and assume that there exists a decidable setoid equivalence relation on elements of this type, \AgdaField{\_≈\_}.

\subsection{Properties}
\label{subsect.properties}

\AgdaHide{
\begin{code}
------------------------------------------------------------------------
-- Path correctness proof
--
-- Properties of Path algebras
------------------------------------------------------------------------

module itp16-paper-properties where

open import Data.Empty
open import Data.Product
open import Data.Sum hiding ([_,_])

open import Function

open import Relation.Binary

open import Algebra.FunctionProperties as FunctionProperties using (Op₂)
import Algebra.MoreFunctionProperties as MFP

open import Relation.Nullary

open import Algebra.Path.Structure

open import Function.Equality using (module Π)
open import Function.Equivalence using (_⇔_; equivalence; module Equivalence)

open Π using (_⟨$⟩_)

rightCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
rightCanonicalOrder _≈_ _∙_ a b = ∃ λ c → b ≈ (a ∙ c)

leftCanonicalOrder : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Rel A _
leftCanonicalOrder _≈_ _∙_ a b = ∃ λ c → a ≈ (b ∙ c)
\end{code}}

\AgdaHide{
\begin{code}
module itp16-requires-commutative-monoid
       {c ℓ} (cmon : CommutativeMonoid c ℓ) where

  open CommutativeMonoid cmon
  open FunctionProperties _≈_
  open MFP _≈_
  open import Relation.Binary.EqReasoning setoid

  infix 4 _⊴ᴸ_ _⊴ᴿ_ _⊲ᴸ_ _⊲ᴿ_

  _⊴ᴸ_ _⊴ᴿ_ _⊲ᴸ_ _⊲ᴿ_ : Rel Carrier _

  _⊴ᴸ_ = leftCanonicalOrder _≈_ _∙_
  _⊴ᴿ_ = rightCanonicalOrder _≈_ _∙_

  a ⊲ᴸ b = a ⊴ᴸ b × ¬ a ≈ b
  a ⊲ᴿ b = a ⊴ᴿ b × ¬ a ≈ b
\end{code}}

\begin{code}
  ⊴ᴸ-transitive : Transitive _⊴ᴸ_
  ⊴ᴸ-transitive {a} {b} {c} (x , a≈b∙x) (y , b≈c∙y) = x ∙ y , eq
    where
      eq =
        begin
          a            ≈⟨ a≈b∙x ⟩
          b ∙ x        ≈⟨ ∙-cong b≈c∙y refl ⟩
          (c ∙ y) ∙ x  ≈⟨ assoc _ _ _ ⟩
          c ∙ (y ∙ x)  ≈⟨ ∙-cong refl (comm _ _) ⟩
          c ∙ (x ∙ y)
        ∎
\end{code}

\AgdaHide{
\begin{code}
  ⊴ᴸ‿¬irrefl : ¬ Irreflexive _≈_ _⊴ᴸ_
  ⊴ᴸ‿¬irrefl irrefl = irrefl (proj₁ identity ε) (ε , refl)

  ⊴ᴸ‿¬tri : ¬ Trichotomous _≈_ _⊴ᴸ_
  ⊴ᴸ‿¬tri tri with tri ε ε
  ... | tri< a ¬b ¬c = ¬b refl
  ... | tri≈ ¬a b ¬c = ¬a (ε , (sym (proj₁ identity ε)))
  ... | tri> ¬a ¬b c = ¬b refl
\end{code}}
  
\begin{code}
  isTotalOrderᴸ : Selective _∙_ → IsTotalOrder _≈_ _⊴ᴸ_
\end{code}

\AgdaHide{
\begin{code}
  isTotalOrderᴸ selective =
    record
      { isPartialOrder =
        record
          { isPreorder =
            record
              { isEquivalence = isEquivalence
              ; reflexive = ⊴ᴸ-reflexive
              ; trans = ⊴ᴸ-transitive
              }
          ; antisym = ⊴ᴸ-antisym
          }
      ; total = total
    }
    where
      ⊴ᴸ-reflexive : _≈_ ⇒ _⊴ᴸ_
      ⊴ᴸ-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity b) (sym a≈b))

      ⊴ᴸ-antisym : Antisymmetric _≈_ _⊴ᴸ_
      ⊴ᴸ-antisym {a} {b} (x , a≈b∙x) (y , b≈a∙y) with selective a y | selective b x
      ... | _          | inj₁ b∙x≈b = trans a≈b∙x b∙x≈b
      ... | inj₁ a∙y≈a | _          = sym (trans b≈a∙y a∙y≈a)
      ... | inj₂ a∙y≈y | inj₂ b∙x≈x = a≈b
        where
          a≈x = trans a≈b∙x b∙x≈x
          b≈y = trans b≈a∙y a∙y≈y
          a≈b =
            begin
              a ≈⟨ a≈x ⟩
              x ≈⟨ sym b∙x≈x ⟩
              b ∙ x ≈⟨ ∙-cong b≈y refl ⟩
              y ∙ x ≈⟨ comm _ _ ⟩
              x ∙ y ≈⟨ ∙-cong (sym a≈x) refl ⟩
              a ∙ y ≈⟨ a∙y≈y ⟩
              y ≈⟨ sym b≈y ⟩
              b
            ∎

      total : Total _⊴ᴸ_
      total x y with selective x y
      ... | inj₁ ≈x = inj₁ (x , (sym (trans (comm _ _) ≈x)))
      ... | inj₂ ≈y = inj₂ (y , (sym ≈y))

  isTotalOrderᴿ : Selective _∙_ → IsTotalOrder _≈_ _⊴ᴿ_
  isTotalOrderᴿ selective =
    record
      { isPartialOrder =
        record
          { isPreorder =
            record
              { isEquivalence = isEquivalence
              ; reflexive = ⊴ᴿ-reflexive
              ; trans = ⊴ᴿ-transitive
              }
          ; antisym = ⊴ᴿ-antisym
          }
      ; total = total
    }
    where
      ⊴ᴿ-reflexive : _≈_ ⇒ _⊴ᴿ_
      ⊴ᴿ-reflexive {a} {b} a≈b = ε , sym (trans (proj₂ identity a) a≈b)

      ⊴ᴿ-transitive : Transitive _⊴ᴿ_
      ⊴ᴿ-transitive {a} {b} {c} (x , b≈a∙x) (y , c≈b∙y) =
        x ∙ y , trans c≈b∙y (trans (∙-cong b≈a∙x refl) (assoc _ _ _))

      ⊴ᴿ-antisym : Antisymmetric _≈_ _⊴ᴿ_
      ⊴ᴿ-antisym {a} {b} (x , b≈a∙x) (y , a≈b∙y) with selective a x | selective b y
      ... | _          | inj₁ b∙y≈b = trans a≈b∙y b∙y≈b
      ... | inj₁ a∙x≈a | _          = sym (trans b≈a∙x a∙x≈a)
      ... | inj₂ a∙x≈x | inj₂ b∙y≈y = a≈b
        where
          a≈y = trans a≈b∙y b∙y≈y
          b≈x = trans b≈a∙x a∙x≈x
          a≈b =
            begin
              a      ≈⟨ a≈y ⟩
              y      ≈⟨ sym b∙y≈y ⟩
              b ∙ y  ≈⟨ ∙-cong b≈x refl ⟩
              x ∙ y  ≈⟨ comm _ _ ⟩
              y ∙ x  ≈⟨ ∙-cong (sym a≈y) refl ⟩
              a ∙ x  ≈⟨ sym b≈a∙x ⟩
              b
            ∎

      total : Total _⊴ᴿ_
      total x y with selective x y
      ... | inj₁ ≈x = inj₂ (x , (trans (sym ≈x) (comm _ _)))
      ... | inj₂ ≈y = inj₁ (y , (sym ≈y))

module itp16-requires-path-algebra
       {c ℓ} (dijkstra : PathAlgebra c ℓ) where

  open PathAlgebra dijkstra
  open FunctionProperties _≈_
  open MFP _≈_
  open import Relation.Binary.EqReasoning setoid

  open itp16-requires-commutative-monoid +-commutativeMonoid public
  open IsTotalOrder (isTotalOrderᴸ +-selective) using (antisym)

  _≉_ : _ → _ → Set _
  x ≉ y = ¬ (x ≈ y)

  +-idempotent : Idempotent _+_
  +-idempotent = sel⟶idp _+_ +-selective

  equivalentᴸ : ∀ a b → b + a ≈ a ⇔ a ⊴ᴸ b
  equivalentᴸ a b = equivalence to from
    where
      to : b + a ≈ a → a ⊴ᴸ b
      to a≈b+b = a , sym a≈b+b

      from : a ⊴ᴸ b → b + a ≈ a
      from (x , a≈b+x) with +-selective b x
      ... | inj₁ b+x≈b = b+a≈a
        where
          a≈b = trans a≈b+x b+x≈b
          b+a≈a =
            begin
              b + a ≈⟨ +-cong (sym a≈b) refl ⟩
              a + a ≈⟨ +-idempotent a ⟩
              a
            ∎
      ... | inj₂ b+x≈x = b+a≈a
        where
          a≈x = trans a≈b+x b+x≈x
          b+a≈a =
            begin
              b + a ≈⟨ +-cong refl a≈x ⟩
              b + x ≈⟨ sym a≈b+x ⟩
              a
            ∎

  lem₀ : ∀ {a b c} → a ≈ b + c → a ≈ b ⊎ a ≈ c
  lem₀ {a} {b} {c} a≈b+c with +-selective b c
  ... | inj₁ b+c≈b = inj₁ (trans a≈b+c b+c≈b)
  ... | inj₂ b+c≈c = inj₂ (trans a≈b+c b+c≈c)

  equivalentᴸ-¬ : ∀ a b → (¬ b + a ≈ a) ⇔ (¬ a ⊴ᴸ b)
  equivalentᴸ-¬ a b = equivalence to from
    where
      to : ¬ b + a ≈ a → ¬ a ⊴ᴸ b
      to ¬b+a≈a (x , a≈b+x) with lem₀ a≈b+x
      ... | inj₁ a≈b = ¬b+a≈a (trans (+-cong (sym a≈b) refl) (+-idempotent a))
      ... | inj₂ a≈x = ¬b+a≈a (trans (+-cong refl a≈x) (sym a≈b+x))

      from : ¬ a ⊴ᴸ b → ¬ b + a ≈ a
      from ¬a⊴ᴸb b+a≈a = ¬a⊴ᴸb (b+a≈a⟶a⊴ᴸb ⟨$⟩ b+a≈a)
        where
          open Equivalence (equivalentᴸ a b) renaming (to to b+a≈a⟶a⊴ᴸb)

  lem₁ : ∀ {a b} → a ≈ b → ¬ a ⊲ᴸ b
  lem₁ a≈b (_ , ¬a≈b) = ¬a≈b a≈b

  lem₁′ : ∀ {a b} → a ⊲ᴸ b → a ≉ b
  lem₁′ (a⊴ᴸb , a≉b) = a≉b

  lem₂ : ∀ {a b} → a ≈ b → ¬ b ⊲ᴸ a
  lem₂ a≈b (_ , ¬b≈a) = ¬b≈a (sym a≈b)

  lem₂′ : ∀ {a b} → b ⊲ᴸ a → a ≉ b
  lem₂′ (b⊴ᴸa , b≉a) a≈b = b≉a $ sym a≈b

  lem₃ : ∀ {a b} → a ⊲ᴸ b → ¬ b ⊲ᴸ a
  lem₃ {a} {b} (a⊴ᴸb , ¬a≈b) (b⊴ᴸa , ¬b≈a) = ¬a≈b (antisym a⊴ᴸb b⊴ᴸa)

  ⊲ᴸ‿tri : (_≈?_ : Decidable _≈_) → Trichotomous _≈_ _⊲ᴸ_
  ⊲ᴸ‿tri _≈?_ a b with a ≈? b | +-selective b a
  ... | yes a≈b | _          = tri≈ (lem₁ a≈b) a≈b (lem₂ a≈b)
  ... | no ¬a≈b | inj₁ b+a≈b = tri> (lem₃ b⊲ᴸa) ¬a≈b b⊲ᴸa
    where
      open Equivalence (equivalentᴸ b a)
      b⊲ᴸa = (to ⟨$⟩ trans (+-comm _ _) b+a≈b , (λ b≈a → ¬a≈b (sym b≈a)))
  ... | no ¬a≈b | inj₂ b+a≈a = tri< a⊲ᴸb ¬a≈b (lem₃ a⊲ᴸb)
    where
      open Equivalence (equivalentᴸ a b)
      a⊲ᴸb = (to ⟨$⟩ b+a≈a , ¬a≈b)

  ⊴ᴸ-trans : Transitive _⊴ᴸ_
  ⊴ᴸ-trans {a} {b} {c} a⊴ᴸb b⊴ᴸc = c+a≈a⟶a⊴ᴸc ⟨$⟩ c+a≈a
    where
      open Equivalence (equivalentᴸ a b) renaming (from to a⊴ᴸb⟶b+a≈a)
      open Equivalence (equivalentᴸ b c) renaming (from to b⊴ᴸc⟶c+b≈b)
      open Equivalence (equivalentᴸ a c) renaming (to   to c+a≈a⟶a⊴ᴸc)

      b+a≈a = a⊴ᴸb⟶b+a≈a ⟨$⟩ a⊴ᴸb
      c+b≈b = b⊴ᴸc⟶c+b≈b ⟨$⟩ b⊴ᴸc

      c+a≈a =
        begin
          c + a        ≈⟨ +-cong refl (sym b+a≈a) ⟩
          c + (b + a)  ≈⟨ sym $ +-assoc _ _ _ ⟩
          (c + b) + a  ≈⟨ +-cong c+b≈b refl ⟩
          b + a        ≈⟨ b+a≈a ⟩
          a
        ∎

  ⊲ᴸ-trans : Transitive _⊲ᴸ_
  ⊲ᴸ-trans {a} {b} {c} (a⊴ᴸb , ¬a≈b) (b⊴ᴸc , ¬b≈c) = ⊴ᴸ-trans a⊴ᴸb b⊴ᴸc , (λ a≈c → ¬a≈b (a≈b a≈c))
    where
      open Equivalence (equivalentᴸ a b) renaming (from to a⊴ᴸb⟶b+a≈a)
      open Equivalence (equivalentᴸ b c) renaming (from to b⊴ᴸc⟶c+b≈b)
      open Equivalence (equivalentᴸ a c) renaming (to   to c+a≈a⟶a⊴ᴸc)

      b+a≈a = a⊴ᴸb⟶b+a≈a ⟨$⟩ a⊴ᴸb
      c+b≈b = b⊴ᴸc⟶c+b≈b ⟨$⟩ b⊴ᴸc

      a≈b : a ≈ c → a ≈ b
      a≈b a≈c =
        begin
          a            ≈⟨ sym b+a≈a ⟩
          b + a        ≈⟨ +-cong refl a≈c ⟩
          b + c        ≈⟨ +-cong (sym c+b≈b) refl ⟩
          (c + b) + c  ≈⟨ +-assoc _ _ _ ⟩
          c + (b + c)  ≈⟨ +-cong refl (+-comm _ _) ⟩
          c + (c + b)  ≈⟨ +-cong refl c+b≈b ⟩
          c + b        ≈⟨ c+b≈b ⟩
          b
        ∎

  ⊲ᴸ-resp : _⊲ᴸ_ Respects₂ _≈_
  ⊲ᴸ-resp = resp , flip-resp
    where
      resp : ∀ {a} → (_⊲ᴸ_ a) Respects _≈_
      resp {a} {b} {c} b≈c (a⊴ᴸb , ¬a≈b) =
        c+a≈a⟶a⊴ᴸc ⟨$⟩ c+a≈a ,
        (λ a≈c → ¬a≈b (trans a≈c (sym b≈c)))
        where
          open Equivalence (equivalentᴸ a b) renaming (from to a⊴ᴸb⟶b+a≈a)
          open Equivalence (equivalentᴸ a c) renaming (to   to c+a≈a⟶a⊴ᴸc)

          b+a≈a = a⊴ᴸb⟶b+a≈a ⟨$⟩ a⊴ᴸb

          c+a≈a =
            begin
              c + a  ≈⟨ +-cong (sym b≈c) refl ⟩
              b + a  ≈⟨ b+a≈a ⟩
              a
            ∎

      flip-resp : ∀ {b} → flip _⊲ᴸ_ b Respects _≈_
      flip-resp {a} {b} {c} b≈c (b⊴ᴸa , ¬b≈a) =
        a+c≈c⟶c⊴ᴸa ⟨$⟩ a+c≈c ,
        (λ c≈a → ¬b≈a (trans b≈c c≈a))
        where
          open Equivalence (equivalentᴸ b a) renaming (from to b⊴ᴸa⟶a+b≈b)
          open Equivalence (equivalentᴸ c a) renaming (to   to a+c≈c⟶c⊴ᴸa)

          a+b≈b = b⊴ᴸa⟶a+b≈b ⟨$⟩ b⊴ᴸa

          a+c≈c =
            begin
              a + c  ≈⟨ +-cong refl (sym b≈c) ⟩
              a + b  ≈⟨ a+b≈b ⟩
              b      ≈⟨ b≈c ⟩
              c
            ∎

  ⊲ᴸ-isStrictTotalOrder : (_≈?_ : Decidable _≈_) → IsStrictTotalOrder _≈_ _⊲ᴸ_
  ⊲ᴸ-isStrictTotalOrder _≈?_ =
    record
      { isEquivalence = isEquivalence
      ; trans         = ⊲ᴸ-trans
      ; compare       = ⊲ᴸ‿tri _≈?_
      ; <-resp-≈      = ⊲ᴸ-resp
      }

  equivalentᴿ : ∀ a b → a + b ≈ b ⇔ a ⊴ᴿ b
  equivalentᴿ a b = equivalence to from
    where
      to : a + b ≈ b → a ⊴ᴿ b
      to a+b≈b = b , (sym a+b≈b)

      from : a ⊴ᴿ b → a + b ≈ b
      from (x , b≈a+x) with +-selective a x
      ... | inj₁ a+x≈a = a+b≈b
        where
          b≈a = trans b≈a+x a+x≈a
          a+b≈b =
            begin
              a + b  ≈⟨ +-cong (sym b≈a) refl ⟩
              b + b  ≈⟨ +-idempotent b ⟩
              b
            ∎
      ... | inj₂ a+x≈x = a+b≈b
        where
          b≈x = trans b≈a+x a+x≈x
          a+b≈b =
            begin
              a + b  ≈⟨ +-cong refl b≈x ⟩
              a + x  ≈⟨ sym b≈a+x ⟩
              b
            ∎

  *-rightIncreasingᴸ : (a b : Carrier) → a ⊴ᴸ a * b
  *-rightIncreasingᴸ a b = a , lemma
    where
      lemma : a ≈ a * b + a
      lemma =
        sym $ begin
          a * b + a
            ≈⟨ +-comm (a * b) a ⟩
          a + a * b
            ≈⟨ +-absorbs-* a b ⟩
          a
        ∎

  1#-bottomᴸ : ∀ a → 1# ⊴ᴸ a
  1#-bottomᴸ a = 1# , sym (proj₂ +-zero a)

  0#-topᴸ : ∀ a → a ⊴ᴸ 0#
  0#-topᴸ a = a , sym (proj₁ +-identity a)

  +-upperᴸ : ∀ {a b c} → a ⊴ᴸ b → a ⊴ᴸ c → a ⊴ᴸ b + c
  +-upperᴸ {a} {b} {c} (d , a≡b+d) (e , a≡c+e) = d + e , lemma
    where
      lemma : a ≈ b + c + (d + e)
      lemma =
        sym $ begin
          b + c + (d + e)
            ≈⟨ +-cong (+-comm b c) refl ⟩
          c + b + (d + e)
            ≈⟨ +-assoc c b (d + e) ⟩
          c + (b + (d + e))
            ≈⟨ +-cong refl $ sym $ +-assoc b d e ⟩
          c + ((b + d) + e)
            ≈⟨ +-cong refl $ +-cong (sym a≡b+d) refl ⟩
          c + (a + e)
            ≈⟨ +-cong refl $ +-comm a e ⟩
          c + (e + a)
            ≈⟨ sym $ +-assoc c e a ⟩
          (c + e) + a
            ≈⟨ +-cong (sym a≡c+e) refl ⟩
          a + a
            ≈⟨ +-idempotent a ⟩
          a
        ∎

  isDecTotalOrderᴸ : IsDecTotalOrder _≈_ _⊴ᴸ_
  isDecTotalOrderᴸ =
    record {
      isTotalOrder = isTotalOrderᴸ +-selective
      ; _≟_        = _≟_
      ; _≤?_       = _⊴ᴸ?_
      }
    where
      _⊴ᴸ?_ : Decidable _⊴ᴸ_
      a ⊴ᴸ? b with (b + a) ≟ a
      ... | yes b+a≈a = yes (a , sym b+a≈a)
      ... | no ¬b+a≈a = no (¬b+a≈a⟶¬a⊴ᴸb ⟨$⟩ ¬b+a≈a)
        where
          open Equivalence (equivalentᴸ-¬ a b) renaming (to to ¬b+a≈a⟶¬a⊴ᴸb)

  decTotalOrderᴸ : DecTotalOrder _ _ _
  decTotalOrderᴸ =
    record { Carrier = Carrier ; _≈_ = _≈_ ; _≤_ = _⊴ᴸ_ ; isDecTotalOrder = isDecTotalOrderᴸ }
\end{code}}

\subsection{Models}
\label{subsect.models}

We now discuss three models---or inhabitants---of the \AgdaRecord{PathAlgebra} record to demonstrate that they exist, that Path Algebras are not categorical (i.e. are not inhabitable by only one structure up to isomorphism), and to use later in Section~\ref{sect.example} where we provide an example execution of our algorithm.

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
    ∞  : ℕ∞
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
Take the algebra's addition and multiplication functions to be \AgdaFunction{\_⊓\_} and \AgdaFunction{\_⊔\_} on \AgdaDatatype{ℕ∞}, respectively.
Take the unit for addition to be \AgdaInductiveConstructor{∞} and the unit for multiplication to be \AgdaInductiveConstructor{↑}~\AgdaInductiveConstructor{0}.
\end{enumerate}
In both cases, it is routine to check that the axioms for a \AgdaRecord{PathAlgebra} can be satisfied.
As the names suggest, executing our generalised Dijkstra algorithm with adjacency matrix coefficients taken from a shortest path algebra will compute the shortest path through the graph described by the matrix, whilst taking matrix coefficients from a widest path algebra will compute the widest path, or maximum bottleneck capacity.

\section{Dijkstra's Algorithm and its correctness}
\label{sect.dijkstras.algorithm.and.its.correctness}

In this Section we discuss the generalised imperative Dijkstra's algorithm (Subsection~\ref{subsect.algorithm}), our functional implementation (Subsection~\ref{subsect.functional.implementation}), and the proof of correctness of this implementation (Subsection~\ref{subsect.correctness}).

\subsection{Algorithm}
\label{subsect.algorithm}

\AgdaHide{
\begin{code}
module itp16-Algorithm
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
  open Sorted using () renaming (Vec to SortedVec)

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

\begin{figure}[ht]
\includegraphics{algorithm.pdf}
\caption{Dynerowicz and Griffin's imperative generalised Dijkstra's algorithm}
\label{fig.algorithm}
\end{figure}

Given a weighted graph $G$, Dijkstra's algorithm in its standard form finds the shortest distance from some start node $i \in G$ to each other connected node $j \in G$, provided all edges in $G$ have non-negative weight.
Dynerowicz and Griffin~\cite{dynerowicz_forwarding_2013} found that a generalised variant of Dijkstra's algorithm finds one row of the matrix $R$ solving the fixpoint equation:
\begin{displaymath}
R = I + (R \times A)
\end{displaymath}
Here, $A$ is the adjacency matrix of the graph $G$ and $I$ the identity matrix.
All matrix coefficients are taken from the carrier set of a Path Algebra, with $-+-$ and $-\times-$ the binary addition and multiplication operations of a Path Algebra lifted to matrices (see Section~\ref{sect.path.algebras.their.properties.and.models}).
Pseudocode for the imperative generalised Dijkstra algorithm, as presented by Dynerowicz and Griffin~\cite[pg. 9]{dynerowicz_forwarding_2013}, is provided in Figure~\ref{fig.algorithm}.

\todo{finish this description}

\subsection{A functional implementation}
\label{subsect.functional.implementation}

Our purely functional implementation of this algorithm in Agda consists of nine mutually recursive definitions, the most important of which are \AgdaFunction{order}, \AgdaFunction{estimate}, \AgdaFunction{seen} and \AgdaFunction{queue}.
Throughout this section we maintain the invariant that $i$ is the start node of the graph search, and use the suggestive name \AgdaFunction{Weight} to refer to the carrier set of our Path Algebra.

At each \AgdaBound{step} of the algorithm graph nodes are totally ordered.
This total order is constructed using the \AgdaFunction{order} function, which is parameterised by the \AgdaBound{step} of the algorithm:
\begin{code}
    order : (step : ℕ) → {s≤n : step ≤ n} → DecTotalOrder _ _ _
    order step {s≤n} = estimateOrder $ estimate step {s≤n}
\end{code}
The function \AgdaFunction{estimateOrder} lifts a mapping from nodes to weights into a decidable total order on nodes.
The function \AgdaFunction{estimate} provides an estimate of the distance from the start node $i$ to every other node in the graph.   
We define \AgdaFunction{estimate} as follows:
\begin{code}
    estimate : (step : ℕ) → {s≤n : step ≤ n} → Fin (suc n) → Weight
    estimate zero                 j = A[ i , j ]
    estimate (suc step) {step≤n}  j = r j + r q * A[ q , j ]
      where
        q  = Sorted.head (order step {≤-step′ step≤n}) (queue step {step≤n})
        r  = estimate step {≤-step′ step≤n}
\end{code}
The base case for the \AgdaFunction{estimate} function is a lookup in the adjacency matrix of the graph.
Note that in the imperative algorithm of Figure~\ref{fig.algorithm}, the base case is equivalent to a lookup in the identity matrix instead of the adjacency matrix.
Our base case here therefore corresponds to the \emph{second} iteration of the imperative algorithm.
%dpm: why is that?
Note also that since the addition operation, \AgdaFunction{\_+\_}, of a Path Algebra is selective, the inductive case of \AgdaFunction{estimate} encodes a \emph{choice} between \AgdaFunction{r}~\AgdaBound{j} and \AgdaFunction{r}~\AgdaFunction{q}~\AgdaFunction{*}~\AgdaFunction{A[}~\AgdaFunction{q}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}.
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
The inductive case of \AgdaFunction{seen} unions together all visited nodes from previous steps of the algorithm with the next node to be visited, per our priority queue of nodes.
Once a node has been visited, its distance estimate stays constant and is optimal---this important invariant will be proved and used later in the proof of correctness of the algorithm in Subsection~\ref{subsect.correctness}.

The following is an auxiliary definition needed to define the function \AgdaFunction{queue}, which computes the priortiy queue of nodes that have not yet been visited by the algorithm:
\begin{code}
    queue′ : (step : ℕ) {s≤n : step ≤ n} → Sorted.Vec _ (size $ ∁ $ seen step {s≤n})
    queue′ step {s≤n} = Sorted.fromVec (order step {s≤n}) $ toVec $ ∁ $ seen step
\end{code}
Here the function \AgdaFunction{∁} is setwise complement, with the expression \AgdaFunction{∁}~\AgdaFunction{\$}~\AgdaFunction{seen}~\AgdaBound{step} \AgdaSymbol{\{}\AgdaBound{s≤n}\AgdaSymbol{\}} corresponding to the set of \emph{unseen} graph nodes.
The function \AgdaFunction{queue′} is a direct definition of the priority queue of unvisited nodes at a given step of the algorithm: we take the complement set of the set of nodes that have been visited thus far and order them using our total order, \AgdaFunction{order}, at the given algorithm step.
Whilst straightforward to understand, unfortunately, this definition is awkward to use in practice due to a problem with the type of \AgdaFunction{queue′}: the priority queue's only use is to provide the node with the smallest estimate that has not yet been visited, which is always at the head of the queue. But to extract the head of a queue, its type must guarantee that it contains at least one element.
This fact is expressed by mandating that the length index of the vector whose head is being examined must be of the form \AgdaInductiveConstructor{suc}~\AgdaBound{n} for some \AgdaBound{n}.
Therefore, in order to provide a queue with a more usable length index, we prove the following lemma which we will use to `massage' the type of \AgdaFunction{queue′} into something more amenable:
\begin{code}
    queue-size :  (step : ℕ) → {s≤n : suc step ≤ n} →
                  size (∁ $ seen step {≤-step′ s≤n}) ≡ suc (n ∸ suc step)
\end{code} % $

Using \AgdaFunction{queue′} and \AgdaFunction{queue-size}, we can then give the following more useful definition of the priority queue of previously unvisited nodes, with a \AgdaInductiveConstructor{suc} in head position in the vector's length index, with the function \AgdaFunction{queue}:
\begin{code}
    queue : (step : ℕ) → {s<n : suc step ≤ n} → Sorted.Vec _ (suc (n ∸ (suc step)))
\end{code}
\AgdaHide{
\begin{code}
    queue step {s<n} = P.subst (Sorted.Vec (order step {≤-step′ s<n})) (queue-size step {s<n}) (queue′ step)
\end{code}
}
We omit the obvious definition.
%dpm: following commented out --- where is it used.  Doesn't seem to be mentioned in the rest of the document so probably not needed.
\AgdaHide{
\begin{code}
    queue′⇒queue  :  (step : ℕ) → {s<n : suc step ≤ n} → ∀ {p}
                     (P : ∀ {n} → Sorted.Vec _ n → Set p) →
                     P (queue′ step) → P (queue step {s<n})
\end{code}}

\subsection{Correctness}
\label{subsect.correctness}

We now work towards a full proof of correctness of our implementation.
Here `correctness' entails showing that our algorithm computes a right local solution to the fixpoint equation in Subsection~\ref{subsect.algorithm}.
We proceed by demonstrating that the algorithm preserves several important invariants that, taken together, imply this result. 

We have two basic `sanity checking' results relating the size of of the queue of unseen nodes and set of seen nodes to the \AgdaBound{step} of the algorithm.
At step $step$ the next node to be visited per the priority queue is not in the list of previously seen nodes.
This is expressed by the lemma \AgdaFunction{q∉seen}:
\begin{code}
    q∉seen :  (step : ℕ) → {s<n : suc step ≤ n} →
      Sorted.head _ (queue step {s<n}) ∉ seen step {≤-step′ s<n}
\end{code}
Further, the size of the set of visited nodes at \AgdaBound{step} is \AgdaInductiveConstructor{suc}~\AgdaBound{step}.
This is expressed by the lemma \AgdaFunction{seen-size}:
\begin{code}
    seen-size     :  (step : ℕ) → {s≤n : step ≤ n} → size (seen step {s≤n}) ≡ suc step
\end{code}
Both proofs are straightforward and omitted for brevity.

\AgdaHide{
\begin{code}
    queue′⇒queue step {s≤n} P Pqueue = super-subst P (≡-to-≅ (queue-size step {s≤n})) (H.sym H-lemma) Pqueue
      where
        open import Relation.Binary.HeterogeneousEquality as H
        open Sorted (order step {≤-step′ s≤n})

        super-subst : ∀ {m n p} → {xs : Vec m} → {ys : Vec n} → (P : ∀ {n} → Vec n → Set p) →
                      m H.≅ n → xs H.≅ ys → P xs → P ys
        super-subst P H.refl H.refl Pxs = Pxs

        H-lemma : queue step ≅ queue′ step
        H-lemma = ≡-subst-removable Vec (queue-size step {s≤n}) (queue′ step)

    seen-size zero           = Sub.size⁅i⁆≡1 i
    seen-size (suc step) {s≤n} =
      begin
        size (seen step ∪ ⁅ q ⁆)  ≡⟨ P.cong size (∪-comm (seen step) ⁅ q ⁆) ⟩
        size (⁅ q ⁆ ∪ seen step)  ≡⟨ Sub.size-suc q (seen step) (q∉seen step) ⟩
        suc (size (seen step))    ≡⟨ P.cong suc (seen-size step) ⟩
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

    q∉seen step {s≤n} q∈vs = q∉q∷qs (S.here qs q≼qs)
      where
        module S = Sorted (order step {≤-step′ s≤n})

        q = S.head (queue step {s≤n})
        qs = S.tail (queue step {s≤n})
        q≼qs = S.≼-proof (queue step {s≤n})

        q∉queue′ : ¬ (q S.∈ (queue′ step))
        q∉queue′ = S.fromVec-∉¹ (Sub.toVec-∉¹ (Sub.∁-∈ q∈vs))

        q∉queue : ¬ (q S.∈ (queue step {s≤n}))
        q∉queue = queue′⇒queue step {s≤n} (λ qs → ¬ (q S.∈ qs)) q∉queue′

        q∉q∷qs : ¬ (q S.∈ (q S.∷ qs ⟨ q≼qs ⟩))
        q∉q∷qs = P.subst (λ qs → ¬ (q S.∈ qs)) S.destruct q∉queue
\end{code}
}

\AgdaHide{
\begin{code}
module itp16-Properties
    {c ℓ} (alg : PathAlgebra c ℓ)
    {n} (i : Fin (suc n)) (adj : MAdj.Adj alg (suc n))
    where

  open import Algebra.Path.Properties
  open import Dijkstra.Algorithm alg i adj

  open import Data.Fin.Subset
  import Data.Fin.Subset.Extra as Sub
  open import Data.Matrix
  open import Data.Nat.MoreProperties using (≤-step′)
  open import Data.Nat.Properties using (≤-step)
  open import Data.Product using (_,_; proj₁)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  import Data.Vec as V
  import Data.Vec.Properties as VP
  import Data.Vec.Sorted as Sorted

  open import Function using (_$_; _∘_; flip)
  open import Function.Equivalence using (module Equivalence)
  open import Function.Equality using (module Π)
  open Π using (_⟨$⟩_)

  open import Relation.Nullary
  open import Relation.Unary using (Pred)
  open import Relation.Binary using (module DecTotalOrder)
  import Relation.Binary.EqReasoning as EqR
  import Relation.Binary.PropositionalEquality as P
  open P using (_≡_; _≢_)
  open P.≡-Reasoning
    using ()
    renaming (begin_ to start_; _≡⟨_⟩_ to _≣⟨_⟩_; _∎ to _■)

  -- Bring the algebra's operators, constants and properties into scope
  open PathAlgebra alg renaming (Carrier to Weight)
  open RequiresPathAlgebra alg

  -- This decidable total order is used to sort vertices by their
  -- current estimate
  open DecTotalOrder decTotalOrderᴸ using (_≤_)
  open import Dijkstra.EstimateOrder decTotalOrderᴸ using (estimateOrder)

  -- Setoid reasoning for the PathAlgebra setoid
  open EqR setoid

  private

    -- The head of the queue has the smallest estimated distance of any vertex
    -- that has not been visited so far
\end{code}
}

Another important invariant is the fact that the head of the priority queue of unseen nodes has the smallest estimated distance from the start node of any of the nodes that have not yet been visited.
This is expressed in the lemma \AgdaFunction{q-lemma}:
\begin{code}
    q-lemma :  (step : ℕ) → {s<n : suc step N≤ n} →
               ∀ k → k ∉ seen step {≤-step′ s<n} →
               let r  = estimate step {≤-step′ s<n}
                   q  = Sorted.head _ (queue step {s<n}) in
               r k + r q ≈ r q
\end{code}
The proof of this result is a direct consequence of the fact that the priority queue is a sorted vector.


\AgdaHide{
\begin{code}
    q-lemma step {s<n} k k∉vs = rq⊴ᴸrk⟶rk+rq≈rq ⟨$⟩ S.head-≤ (∈-lemma k∉vs)
      where
        r = estimate step {≤-step′ s<n}

        module S = Sorted (estimateOrder r)
        open DecTotalOrder (estimateOrder r)
          using () renaming (_≤_ to _≤ᵉ_)

        q = S.head (queue step {s<n})

        ∈-lemma : ∀ {k} → k ∉ seen step {≤-step′ s<n} → k S.∈ queue step {s<n}
        ∈-lemma {k} k∉vs = queue⇒queue′ step {s<n} (λ qs → k S.∈ qs) (∈-lemma′ k∉vs)
          where
            ∈-lemma′ : ∀ {k} → k ∉ seen step {≤-step′ s<n} → k S.∈ queue′ step {≤-step′ s<n}
            ∈-lemma′ k∉vs = S.fromVec-∈¹ (Sub.toVec-∈¹ (Sub.∁-∈′ k∉vs))

        open Equivalence (equivalentᴸ (r q) (r k)) renaming (from to rq⊴ᴸrk⟶rk+rq≈rq)

    -- If a vertex has not been visited in step (suc step) then it has not
    -- been visited in step step
\end{code}
}
% $
Further, the set of nodes that has been visited so far is strictly monotonic in the step of the algorithm.
This fact is most usefully stated in the form: `if a node has not been visited at a given step then it has also not been visited in its immediate predecessor step, neither'.
This is expressed in the lemma~\AgdaFunction{not-seen}:
\begin{code}
    not-seen :  (step : ℕ) → {s<n : suc step N≤ n} →
                ∀ k → k ∉ seen (suc step) {s<n} →
                k ∉ seen step {≤-step′ s<n}
\end{code}

The nodes visited in \AgdaInductiveConstructor{suc}~\AgdaBound{step} are the nodes visited in \AgdaBound{step} with the head of the queue at \AgdaBound{step} added, so \AgdaFunction{seen}~\AgdaSymbol{(}\AgdaInductiveConstructor{suc}~\AgdaBound{step}\AgdaSymbol{)} is a superset of \AgdaFunction{seen}~\AgdaBound{step}. The lemma is a direct consequence of this.

\AgdaHide{
\begin{code}
    not-seen step {s<n} k k∉vs′ k∈vs = k∉vs′ (Sub.∪-∈′ k _ _ k∈vs)

  -- Once a node has been visited its estimate is optimal
\end{code}
}

Once a node has been visited its estimate is optimal.

\begin{code}
  pcorrect-lemma :  (step : ℕ) {s<n : suc step N≤ n} → ∀ {j k} →
                    let vs  = seen step {≤-step′ s<n}
                        r   = estimate step {≤-step′ s<n} in
                    j ∈ vs → k ∉ vs → r j + r k ≈ r j
\end{code}
This lemma, together with \cref{thm.prls}, constitutes the core of the correctness proof.

The proof proceeds by induction on \AgdaBound{step}.

\paragraph{Base case.} At step \AgdaInductiveConstructor{zero}, the set of visited nodes, \AgdaFunction{seen}, contains exactly the start node, \AgdaBound{i}, so \AgdaBound{j} is equal to \AgdaBound{i}. The base case of \AgdaFunction{estimate} is a lookup in the adjacency matrix. Consequently, \AgdaFunction{estimate}~\AgdaInductiveConstructor{zero}~\AgdaBound{j} is equal to \AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{i}~\AgdaFunction{]}. By the adjacency matrix diagonal property, this is equivalent to \AgdaFunction{1\#}, the zero element of addition in a path algebra.

The corresponding Agda proof follows (\AgdaFunction{lemma} uses the adjacency matrix diagonal property, and is omitted for brevity):

\begin{code}
  pcorrect-lemma zero {j = j} {k} j∈vs _ =
    begin
      r j  + r k  ≈⟨ +-cong rj≈1 refl ⟩
      1#   + r k  ≈⟨ proj₁ +-zero _ ⟩
      1#          ≈⟨ sym rj≈1 ⟩
      r j
    ∎
\end{code}
\AgdaHide{
\begin{code}
    where
      r = estimate zero {z≤n}
      rj≈1 : A[ i , j ] ≈ 1#
      rj≈1 =
        begin
          A[ i , j ]  ≡⟨ P.cong₂ A[_,_] (P.refl {x = i}) (Sub.i∈⁅i⁆′ i j j∈vs) ⟩
          A[ i , i ]  ≈⟨ MAdj.Adj.diag adj i ⟩
          1#
        ∎
\end{code}
}
In the induction step, we perform a case split: by the definition of \AgdaFunction{seen}, if \AgdaBound{j} is an element of \AgdaFunction{seen}~\AgdaSymbol{(}\AgdaInductiveConstructor{suc}~\AgdaBound{step}\AgdaSymbol{)} then \AgdaBound{j} either belongs to \AgdaFunction{seen}~\AgdaBound{step} (case 1) or was the head of the queue at at \AgdaBound{step} (case 2).

\AgdaHide{
\begin{code}
  pcorrect-lemma (suc step) {s<n} {j} {k} j∈vs′ k∉vs′
    with Sub.∪-∈ {suc n} j (seen step) ⁅ Sorted.head _ (queue step) ⁆ j∈vs′
\end{code}}

\paragraph{Induction step (case \AgdaBound{j}~\AgdaDatatype{∈}~\AgdaFunction{seen}~\AgdaBound{step}).}
\AgdaHide{
\begin{code}
  ... | inj₁ j∈vs =
    begin
      r′ j + r′ k                                          ≡⟨⟩
      (r j + r q * A[ q , j ]) + (r k + r q * A[ q , k ])  ≈⟨ +-cong (+-comm _ _) refl ⟩
      (r q * A[ q , j ] + r j) + (r k + r q * A[ q , k ])  ≈⟨ +-assoc _ _ _ ⟩
      r q * A[ q , j ] + (r j + (r k + r q * A[ q , k ]))  ≈⟨ +-cong refl lemma ⟩
      r q * A[ q , j ] + r j                               ≈⟨ +-comm _ _ ⟩
      r j + r q * A[ q , j ]                               ≡⟨⟩
      r′ j
    ∎
    where
      r  = estimate step {≤-step′ (≤-step′ s<n)}
      r′ = estimate (suc step) {≤-step′ s<n}
      q  = Sorted.head _ (queue step {≤-step′ s<n})

      pcorrect₁ = pcorrect-lemma step {≤-step′ s<n} j∈vs (not-seen step k k∉vs′)
      pcorrect₂ = pcorrect-lemma step {≤-step′ s<n} j∈vs (q∉seen step)

      lemma : r j + (r k + r q * A[ q , k ]) ≈ r j
      lemma =
        begin
          r j + (r k + r q * A[ q , k ])  ≈⟨ sym (+-assoc _ _ _) ⟩
          (r j + r k) + r q * A[ q , k ]  ≈⟨ +-cong pcorrect₁ refl ⟩
          r j + r q * A[ q , k ]          ≈⟨ +-cong (sym pcorrect₂) refl ⟩
          (r j + r q) + r q * A[ q , k ]  ≈⟨ +-assoc _ _ _ ⟩
          r j + (r q + r q * A[ q , k ])  ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
          r j + r q                       ≈⟨ pcorrect₂ ⟩
          r j
        ∎
\end{code}
}
In the following, we use the notation \(r′_j\) to denote \AgdaFunction{estimate}~\AgdaSymbol{(}\AgdaInductiveConstructor{suc}~\AgdaBound{step}\AgdaSymbol{)}~\AgdaBound{j} and \(r_j\) for \AgdaFunction{estimate}~\AgdaBound{step}~\AgdaBound{j}.
The induction step of this theorem requires a lemma that \(r_j + (r_k + r_q * A_{q,k}) ≈ r_j\) which we show first:

\begin{align*}
r_j + (r_k + r_q * A_{q,k})
&≈ (r_j + r_k) + r_q * A_{q,k} && \text{associativity} \\
&≈ r_j + r_q * A_{q,k}         && \text{induction step} \\
&≈ (r_j + r_q) + r_q * A_{q,k} && \text{induction step} \\
&≈ r_j + (r_q + r_q * A_{q,k}) && \text{associativity} \\
&≈ r_j + r_q                   && \text{absorptivity} \\
&≈ r_j                         && \text{induction step}
\end{align*}
Using this lemma and the assumption that \AgdaBound{j}~\AgdaDatatype{∈}~\AgdaFunction{seen}~\AgdaBound{step}, we can proceed to prove the induction step as follows:

\begin{align*}
r′_j + r′_k
&≡ (r_j + r_q * A_{q,j}) + (r_k + r_q * A_{q,k}) && \text{\AgdaFunction{estimate} definition} \\
&≈ (r_q * A_{q,j} + r_j) + (r_k + r_q * A_{q,k}) && \text{commutativity} \\
&≈ r_q * A_{q,j} + (r_j + (r_k + r_q * A_{q,k})) && \text{associativity} \\
&≈ r_q * A_{q,j} + r_j                           && \text{lemma} \\
&≈ r_j + r_q * A_{q,j}                           && \text{commutativity} \\
&≡ r′_j                                          && \text{\AgdaFunction{estimate} definition}
\end{align*}

\paragraph{Induction step (case \AgdaBound{j}~\AgdaDatatype{≡}~\AgdaFunction{head}~\AgdaSymbol{(}\AgdaFunction{queue}~\AgdaBound{step}\AgdaSymbol{)}).}
\AgdaHide{
\begin{code}
  ... | inj₂ j∈⁅q⁆ =
    begin
      r′ j + r′ k                                          ≡⟨⟩
      (r j + r q * A[ q , j ]) + (r k + r q * A[ q , k ])  ≡⟨ j≡q₁ ⟩
      (r q + r q * A[ q , j ]) + (r k + r q * A[ q , k ])  ≈⟨ +-cong (+-absorbs-* _ _) refl ⟩
      r q + (r k + r q * A[ q , k ])                       ≈⟨ sym (+-assoc _ _ _) ⟩
      (r q + r k) + r q * A[ q , k ]                       ≈⟨ +-cong (+-comm _ _) refl ⟩
      (r k + r q) + r q * A[ q , k ]                       ≈⟨ +-assoc _ _ _ ⟩
      r k + (r q + r q * A[ q , k ])                       ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
      r k + r q                                            ≈⟨ lemma ⟩
      r q                                                  ≈⟨ sym (+-absorbs-* _ _) ⟩
      r q + r q * A[ q , j ]                               ≡⟨ j≡q₂ ⟩
      r j + r q * A[ q , j ]                               ≡⟨⟩
      r′ j
    ∎
    where
      r  = estimate step {≤-step′ (≤-step′ s<n)}
      r′ = estimate (suc step) {≤-step′ s<n}
      q  = Sorted.head _ (queue step {≤-step′ s<n})
      j≡q : j ≡ q
      j≡q = Sub.i∈⁅i⁆′ {suc n} q j j∈⁅q⁆

      j≡q₁ = P.cong₂ _+_ (P.cong₂ _+_ (P.cong r j≡q) P.refl) P.refl
      j≡q₂ = P.cong₂ _+_ (P.cong r (P.sym j≡q)) P.refl
      lemma = q-lemma step {≤-step′ s<n} k (not-seen step k k∉vs′)

  -- The distance estimate of a vertex stays the same once it has been visited.
  -- This lemma is used in the correctness proof
\end{code}
}
In the following proof, \(q\) denotes the head of the queue at \AgdaBound{step}.

\begin{align*}
r′_j + r′_k
&≡ (r_j + r_q * A_{q,j}) + (r_k + r_q * A_{q,k}) && \text{\AgdaFunction{estimate} definition} \\
&≡ (r_q + r_q * A_{q,j}) + (r_k + r_q * A_{q,k}) && \text{since \(j = q\)} \\
&≈ r_q + (r_k + r_q * A_{q,k})                  && \text{absorptivity} \\
&≈ (r_q + r_k) + r_q * A_{q,k}                  && \text{associativity} \\
&≈ (r_k + r_q) + r_q * A_{q,k}                  && \text{commutativity} \\
&≈ r_k + (r_q + r_q * A_{q,k})                  && \text{associativity} \\
&≈ r_k + r_q                                   && \text{absorptivity} \\
&≈ r_q                                         && \text{lemma} \\
&≈ r_q + r_q * A_{q,j}                          && \text{absorptivity} \\
&≈ r_j + r_q * A_{q,j}                          && \text{since \(j = q\)} \\
&≡ r′_j                                           && \text{\AgdaFunction{estimate} definition}
\end{align*}

The distance estimate of a node stays the same once it has been visited.

\begin{code}
  estimate-lemma :  (step : ℕ) {s<n : suc step N≤ n} →
                    ∀ k → k ∈ seen step {≤-step′ s<n} →
                    estimate (suc step) {s<n} k ≈ estimate step {≤-step′ s<n} k
\end{code}

This follows immediately from \cref{lemma.optimal}:

\begin{align*}
r′_k
&≡ r_k + r_q * A_{q,k}       && \text{\AgdaFunction{estimate} definition} \\
&≈ (r_k + r_q) + r_q * A_{q,k}  && \text{\Cref{lemma.optimal}} \\
&≈ r_k + (r_q + r_q * A_{q,k})  && \text{absorptivity} \\
&≈ r_k + r_q                   && \text{\Cref{lemma.optimal}} \\
&≡ r_k                           && \text{\AgdaFunction{estimate} definition}
\end{align*}

\AgdaHide{
\begin{code}
  estimate-lemma step {s<n} k k∈vs =
    begin
      r′ k                            ≡⟨⟩
      r k + r q * A[ q , k ]          ≈⟨ +-cong (sym pcorrect) refl ⟩
      (r k + r q) + r q * A[ q , k ]  ≈⟨ +-assoc _ _ _ ⟩
      r k + (r q + r q * A[ q , k ])  ≈⟨ +-cong refl (+-absorbs-* _ _) ⟩
      r k + r q                       ≈⟨ pcorrect ⟩
      r k
    ∎
    where
      r  = estimate step {≤-step′ s<n}
      r′ = estimate (suc step) {s<n}
      q  = Sorted.head _ (queue step {s<n})

      pcorrect = pcorrect-lemma step {s<n} k∈vs (q∉seen step)
\end{code}
}

\AgdaHide{
\begin{code}
module itp16-Correctness
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

The estimate \(r\) is a partial right-local solution for node \(j\) and step \(n\) if
\[r_j ≈ I_{i,j} + \bigoplus_{k ∈ S_n} r_k * A_{k,j}\]
where \(S_n\) is the set of nodes that have been visited at step \(n\).
This is expressed in Agda as follows:

\begin{code}
  pRLS : (step : ℕ) {s≤n : step N≤ n} → Pred (Fin (suc n)) _
  pRLS step {s≤n} j = let r = estimate step {s≤n} in
    r j ≈ I[ i , j ] + (⨁[ k ← seen step {s≤n} ] r k * A[ k , j ])
\end{code}

The estimate \(r\) is a right-local solution for node \(j\) and step \(n\) if
\[r_j ≈ I_{i,j} + \bigoplus_{k ∈ V} r_k * A_{k,j}\]
where \(V\) is the set of all nodes \emph{(}\AgdaFunction{⊤} in Agda\emph{)}.
In Agda, we express this as follows:

\begin{code}
  RLS : (step : ℕ) {s≤n : step N≤ n} → Pred (Fin (suc n)) _
  RLS step {s≤n} j = let r = estimate step {s≤n} in
    r j ≈ I[ i , j ] + (⨁[ k ← ⊤ ] r k * A[ k , j ])
\end{code}
Our aim is to prove that \AgdaFunction{RLS}~\AgdaBound{n}~\AgdaBound{j} holds for all \AgdaBound{j}. At step \AgdaBound{n}, every node has been visited: \AgdaFunction{seen}~\AgdaBound{n}~\AgdaDatatype{≡}~\AgdaFunction{⊤}. This means that \AgdaFunction{RLS}~\AgdaBound{n}~\AgdaBound{j} is a direct consequence of \AgdaFunction{pRLS}~\AgdaBound{n}~\AgdaBound{j}. We prove that our implementation of Dijkstra's algorithm computes a partial right-local solution at every step (\cref{thm.prls}), and then show that this implies that the end result is a right-local solution (\cref{cor.rls}).

Dijkstra's algorithm computes a partial right-local solution at every step.

The proof proceeds by induction on \AgdaBound{step}.
In the base case (\AgdaBound{step}~\AgdaSymbol{=}~\AgdaInductiveConstructor{zero}), we perform a case split on whether \AgdaBound{j} is equal to the start node \AgdaBound{i}.

\paragraph{Base case (\(i = j\)).} \AgdaFunction{estimate}~\AgdaInductiveConstructor{zero}~\AgdaBound{j} is defined as \AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}, which equals \AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{i}~\AgdaFunction{]} by assumption. This is equivalent to \AgdaFunction{1\#} by the adjacency matrix diagonal property. The theorem follows by the identity matrix' diagonal property and the fact that \AgdaFunction{1\#} is a zero element for \AgdaFunction{+}:

\begin{code}
  pcorrect : (step : ℕ) {s≤n : step N≤ n} → ∀ j → pRLS step {s≤n} j
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

\paragraph{Base case (\(i ≠ j\)).} We expand the definition of \AgdaFunction{estimate} and use the identity property of \AgdaFunction{+} to show that \AgdaFunction{estimate}~\AgdaInductiveConstructor{zero}~\AgdaBound{j} is equivalent to \AgdaFunction{0\#}~\AgdaFunction{+}~\AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}.

The left-hand side (\AgdaFunction{0\#}) is equal to \AgdaFunction{I[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]} by the definition of the identity matrix and the assumption \(i ≠ j\); the right-hand side (\AgdaFunction{A[}~\AgdaBound{i}~\AgdaFunction{,}~\AgdaBound{j}~\AgdaFunction{]}) is transformed into \(\bigoplus_{k ∈ \{i\}} r_k * A_{k,j}\) using the left-identity property of \AgdaFunction{*} and the adjacency matrix diagonal property as follows:

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
\end{code}
}

\paragraph{Induction step.}
\begin{align*}
r′_j
&≡ r_j + r_q * A_{q,j} && \text{\AgdaFunction{estimate} definition} \\
&≈ \left(I_{i,j} + \left(\bigoplus_{k ∈ S_n} r_k * A_{k,j}\right)\right) + r_q * A_{q,j} && \text{\Cref{thm.prls}} \\
&≈ I_{i,j} + \left(\left(\bigoplus_{k ∈ S_n} r_k * A_{k,j}\right) + r_q * A_{q,j}\right) && \text{associativity} \\
&≈ I_{i,j} + \left(\left(\bigoplus_{k ∈ S_n} r′_k * A_{k,j}\right) + r′_q * A_{q,j}\right) && \text{\Cref{cor.estimate}, absorptivity} \\
&≈ I_{i,j} + \left(\left(\bigoplus_{k ∈ S_n} r′_k * A_{k,j}\right) + \left(\bigoplus_{k ∈ \{ q \}} r′_k * A_{k,j}\right)\right) && \text{\Cref{lem.fold.singleton}} \\
&≈ I_{i,j} + \bigoplus_{k ∈ S_n ∪ \{ q \}} r′_k * A_{k,j} && \text{\Cref{lem.fold.union}} \\
&≡ I_{i,j} + \bigoplus_{k ∈ S_{n+1}} r′_k * A_{k,j} && \text{\AgdaFunction{seen} definition}
\end{align*}
We omit the corresponding Agda proof for brevity.

\AgdaHide{
\begin{code}
  pcorrect (suc step) {s≤n} j =
    begin
      r′ j
    ≡⟨⟩
      r j + r q * A[ q , j ]
    ≈⟨ +-cong (pcorrect step {≤-step′ s≤n} j) refl ⟩
      (I[ i , j ] + (⨁[ k ← vs ] r k * A[ k , j ])) + r q * A[ q , j ]
    ≈⟨ +-assoc _ _ _ ⟩
      I[ i , j ] + ((⨁[ k ← vs ] r k * A[ k , j ]) + r q * A[ q , j ])
    ≈⟨ +-cong refl (+-cong fold (*-cong (sym (+-absorbs-* _ _)) refl)) ⟩
      I[ i , j ] + ((⨁[ k ← vs ] r′ k * A[ k , j ]) + r′ q * A[ q , j ])
    ≈⟨ +-cong refl (+-cong refl (sym (fold-⁅i⁆ f′ q))) ⟩
      I[ i , j ] + ((⨁[ k ← vs ] r′ k * A[ k , j ]) + (⨁[ k ← ⁅ q ⁆ ] r′ k * A[ k , j ]))
    ≈⟨ +-cong refl (sym (fold-∪ +-idempotent f′ (seen step) ⁅ q ⁆)) ⟩
      I[ i , j ] + (⨁[ k ← vs ∪ ⁅ q ⁆ ] r′ k * A[ k , j ])
    ≡⟨⟩
      I[ i , j ] + (⨁[ k ← seen (suc step) {s≤n} ] r′ k * A[ k , j ])
    ∎
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
\end{code}
}

Dijkstra's algorithm computes a right-local solution.

By \cref{thm.prls}, Dijkstra's algorithm computes a partial right-local solution at step \AgdaBound{n} for every node \AgdaBound{j}. By \cref{lem.seen.size}, the number of nodes that have been visited at step \AgdaBound{n} is the total number of nodes in the graph, \AgdaBound{n}. Thus at step \AgdaBound{n}, every node has been visited, so \AgdaFunction{seen}~\AgdaBound{n}~\AgdaDatatype{≡}~\AgdaFunction{⊤}. It follows that \AgdaFunction{RLS}~\AgdaBound{n}~\AgdaBound{j} for all nodes \AgdaBound{j}:

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

\section{Example}
\label{sect.example}

\section{Conclusions}
\label{sect.conclusions}

\paragraph{Related Work}

\paragraph{Future Work}

\paragraph{Resources}

The Dijkstra formalisation and all supporting files are available anonymously from a public \texttt{git} repository~\cite{markert_formalised_2015}.
Documentation for type checking the formalisation is available in the repository.
The formalisation consists of approximately 2,400 lines of Agda and was developed using Agda~2.4.2.1 and~2.4.2.2 and Standard Library version~0.9.

\bibliography{path-algebra}

\end{document}
