# Coq Library for First-Order Logic

This library is a (preliminary) merge of several Coq projects concerning first-order logic. It provides a unified framework for the first-order [syntax](Syntax), [semantics](Semantics), and [deduction systems](Deduction), tools like a [proof mode](Proofmode) and a [reification tactic](Reification), and results regarding [completeness](Completeness2), [undecidability](Undecidability), and [incompleteness](Incompleteness).

Disclaimer: the library is currently still in development and (parts of it) will be extracted into a separate repository in the near future. So if you plan to use it or contribute to it, best get in touch with the maintainers [Dominik Kirst](mailto:kirst@cs.uni-saarland.de) and [Johannes Hostert](mailto:s8johost@stud.uni-saarland.de) first.

## Installation

Follow the [manual installation instructions](https://github.com/dominik-kirst/coq-library-undecidability/tree/fol-library#manual-installation) of this fork of the Coq library of undecidability proofs. To build only the core files relevant for first-order logic, run `make FragmentSyntax.vo FullSyntax.vo.` from the `theories` folder.

## Contributors

- Andrej Dudenhefner
- Yannick Forster
- Marc Hermes
- Johannes Hostert
- Dominik Kirst
- Mark Koch
- Dominique Larchey-Wendling
- Niklas Mück
- Benjamin Peters
- Gert Smolka
- Dominik Wehr

## Publications

- On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem. Yannick Forster, Dominik Kirst, and Gert Smolka. CPP'19.
- Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory. Yannick Forster, Dominik Kirst, Dominik Wehr. LFCS'20
- Trakhtenbrot's Theorem in Coq - A Constructive Approach to Finite Model Theory. Dominik Kirst and Dominique Larchey-Wendling. IJCAR'20.
- Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory (Extended Version). Yannick Forster, Dominik Kirst, Dominik Wehr. JLC'21.
- Synthetic Undecidability and Incompleteness of First-Order Axiom Systems in Coq. Dominik Kirst, Marc Hermes. ITP'21.
- Trakhtenbrot's Theorem in Coq: Finite Model Theory through the Constructive Lens. Dominik Kirst, Dominique Larchey-Wendling. LMCS'22.
- Synthetic Undecidability and Incompleteness of First-Order Axiom Systems in Coq. Dominik Kirst, Marc Hermes. JAR'22.
- Undecidability of Dyadic First-Order Logic in Coq. Johannes Hostert, Andrej Dudenhefner, Dominik Kirst. ITP'22.
- An Analysis of Tennenbaum's Theorem in Constructive Type Theory. Marc Hermes, Dominik Kirst. FSCD'22.
