# A library of formalised undecidable problems in Coq

[![Build Status](https://travis-ci.org/uds-psl/coq-library-undecidability.svg?branch=master)](https://travis-ci.org/uds-psl/coq-library-undecidability)

This library contains undecidable problems and formalised reductions between them.
Feel free to contribute or start using the problems!

## Existing undecidable problems

- Post correspondence problem (`PCP` in [`Problems/PCP.v`](theories/Problems/PCP.v)), **`good seed`**
- Halting problems for single-tape and multi-tape Turing machines (`Halt` in [`Problems/TM.v`](theories/Problems/TM.v))
- Halting problem for Minsky machines (`MM_HALTING` in [`Problems/MM.v`](theories/Problems/MM.v))
- Halting problem for two counters Minsky machines (`MM2_HALTING` in [`Problems/MM2.v`](theories/Problems/MM2.v)) with 
  self-contained explanations, **`good seed`**
- Halting problem for Binary Stack Machines (`BSM_HALTING` in [`Problems/BSM.v`](theories/Problems/BSM.v))
- Halting problem for the call-by-value lambda-calculus (`eva` in [`Problems/L.v`](theories/Problems/L.v))
- String rewriting (`SR` in [`Problems/SR.v`](theories/Problems/SR.v))
- Entailment in Elementary Intuitionistic Linear Logic (`EILL_PROVABILITY` in [`Problems/ILL.v`](theories/Problems/ILL.v))
- Entailment in Intuitionistic Linear Logic (`ILL_PROVABILITY` in [`Problems/ILL.v`](theories/Problems/ILL.v))
- Provability in Minimal (Intuitionistic, Classical) First-Order Logic (`prv` in [`Problems/FOL.v`](theories/Problems/FOL.v))
- Validity in Minimal (Intuitionistic, Classical) First-Order Logic (`valid` in [`Problems/FOL.v`](theories/Problems/FOL.v), `kvalid` in [`Problems/FOL.v`](theories/Problems/FOL.v))
- Satisfiability in Intuitionistic (Classical) First-Order Logic (`satis` in [`Problems/FOL.v`](theories/Problems/FOL.v), `ksatis` in [`Problems/FOL.v`](theories/Problems/FOL.v))
- Halting problem for FRACTRAN programs (`FRACTRAN_REG_HALTING` in [`Problems/FRACTRAN.v`](theories/Problems/FRACTRAN.v)), **`good seed`**
- Satisfiability for elementary diophantine constraints (`DIO_ELEM_SAT` 
  in [`Problems/DIOPHANTINE.v`](theories/Problems/DIOPHANTINE.v))
- [Hilbert's 10th problem](https://uds-psl.github.io/H10), i.e. solvability of a single diophantine equation (`H10` in 
  in [`Problems/DIOPHANTINE.v`](theories/Problems/DIOPHANTINE.v))
- Satisfiability of elementary Diophantine constraints of the form `x=1`, `x=y+z` or `x=y.z` without parameters (`H10C_SAT` in [`Problems/H10C.v`](theories/Problems/H10C.v)), **`good seed`**

## How to build

If you can use `opam 2` on your system, you can follow the instructions here.
If you cannot use `opam 2`, you can use the `noopam` branch of this repository, which has no dependencies, but less available problems.

### Install from opam

We recommend creating a fresh opam switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
```

Then the following commands install the library:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add opam repo add psl-opam-repository https://github.com/uds-psl/psl-opam-repository.git
opam install coq-library-undecidability.1.0~alpha+8.10
```

### Manual installation

You need `Coq 8.10.2` built on OCAML `> 4.02.3`, the [Smpl](https://github.com/uds-psl/smpl) package, the [PSL Base](https://github.com/uds-psl/base-library) library, the [Equations](https://mattam82.github.io/Coq-Equations/) package, and the [MetaCoq](https://metacoq.github.io/metacoq/) package for Coq. If you are using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add opam repo add psl-opam-repository https://github.com/uds-psl/psl-opam-repository.git
opam install . --deps-only
```

### Building the undecidability library

- `make all` builds the library
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory
- `make realclean` also removes all build files in the `external` directory. You have to run `make deps` again after this.

## Published work and technical reports

- Undecidability of Higher-Order Unification Formalised in Coq. Simon Spies and Yannick Forster. Technical report. Subdirectory `HOU`. https://www.ps.uni-saarland.de/Publications/details/SpiesForster:2019:UndecidabilityHOU.html
- Verified Programming of Turing Machines in Coq. Yannick Forster, Fabian Kunze, Maximilian Wuttke. Technical report. Subdirectory `TM`. https://github.com/uds-psl/tm-verification-framework/
- Hilbert's Tenth Problem in Coq. Dominique Larchey-Wendling and Yannick Forster. FSCD '19. Subdirectory `H10`. https://uds-psl.github.io/H10
- A certifying extraction with time bounds from Coq to call-by-value lambda-calculus. ITP '19. Subdirectory `L`. https://github.com/uds-psl/certifying-extraction-with-time-bounds
- Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. Subdirectory `ILL`. http://uds-psl.github.io/ill-undecidability/
- On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem. Yannick Forster, Dominik Kirst, and Gert Smolka. CPP '19. Subdirectory `FOL`. https://www.ps.uni-saarland.de/extras/fol-undec
-  Formal Small-step Verification of a Call-by-value Lambda Calculus Machine. Fabian Kunze, Gert Smolka, and Yannick Forster. APLAS 2018. Subdirectory `LAM`. https://www.ps.uni-saarland.de/extras/cbvlcm2/
- Towards a library of formalised undecidable problems in Coq: The undecidability of intuitionistic linear logic. Yannick Forster and Dominique Larchey-Wendling. LOLA 2018. Subdirectory `ILL`. https://www.ps.uni-saarland.de/~forster/downloads/LOLA-2018-coq-library-undecidability.pdf 
- Verification of PCP-Related Computational Reductions in Coq. Yannick Forster, Edith Heiter, and Gert Smolka. ITP 2018. Subdirectory `PCP`. https://ps.uni-saarland.de/extras/PCP 
- Call-by-Value Lambda Calculus as a Model of Computation in Coq. Yannick Forster and Gert Smolka. Journal of Automated Reasoning (2018) Subdirectory `L`. https://www.ps.uni-saarland.de/extras/L-computability/

## How to contribute

- Fork the project on GitHub.
- Create a new subdirectory for your project and add your files.
- Add a license for your project.
- Edit the "Existing undecidable problems" and the "Contributors" section in this file
- File a pull request.

## Contributors

- Yannick Forster
- Edith Heiter
- Dominik Kirst 
- Fabian Kunze
- Dominique Larchey-Wendling
- Gert Smolka
- Simon Spies
- Maximilian Wuttke

