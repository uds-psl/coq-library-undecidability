# A Coq Library of Undecidability Proofs

[![Build Status](https://travis-ci.com/uds-psl/coq-library-undecidability.svg?branch=coq-8.12)](https://travis-ci.com/uds-psl/coq-library-undecidability)

This library contains undecidable problems and formalised reductions between them.
Feel free to contribute or start using the problems!

## Existing undecidable problems

- Post correspondence problem (`PCP` in [`PCP/PCP.v`](theories/PCP/PCP.v)), **`good seed`**
- Halting problems for single-tape and multi-tape Turing machines (`HaltTM` in [`TM/TM.v`](theories/TM/TM.v))
- Halting problem for Minsky machines (`MM_HALTING` in [`Problems/MM.v`](theories/Problems/MM.v))
- Halting problem for two counters Minsky machines (`MM2_HALTING` in [`Problems/MM2.v`](theories/Problems/MM2.v)) with 
  self-contained explanations, **`good seed`**
- Halting problem for Binary Stack Machines (`BSM_HALTING` in [`Problems/BSM.v`](theories/Problems/BSM.v))
- Halting problem for the call-by-value lambda-calculus (`HaltL` in [`L/L.v`](theories/L/L.v))
- String rewriting (`SR` in [`StringRewriting/SR.v`](theories/StringRewriting/SR.v))
- Entailment in Elementary Intuitionistic Linear Logic (`EILL_PROVABILITY` in [`Problems/ILL.v`](theories/Problems/ILL.v))
- Entailment in Intuitionistic Linear Logic (`ILL_PROVABILITY` in [`Problems/ILL.v`](theories/Problems/ILL.v))
- Provability in Minimal (Intuitionistic, Classical) First-Order Logic (`prv` in [`Problems/FOL.v`](theories/Problems/FOL.v))
- Validity in Minimal (Intuitionistic, Classical) First-Order Logic (`valid` in [`Problems/FOL.v`](theories/Problems/FOL.v), `kvalid` in [`Problems/FOL.v`](theories/Problems/FOL.v))
- Satisfiability in Intuitionistic (Classical) First-Order Logic (`satis` in [`Problems/FOL.v`](theories/Problems/FOL.v), `ksatis` in [`Problems/FOL.v`](theories/Problems/FOL.v))
- Halting problem for FRACTRAN programs (`FRACTRAN_REG_HALTING` in [`Problems/FRACTRAN.v`](theories/Problems/FRACTRAN.v)), **`good seed`**
- [Hilbert's 10th problem](https://uds-psl.github.io/H10), i.e. solvability of a single diophantine equation (`H10` in 
  in [`Problems/DIOPHANTINE.v`](theories/Problems/DIOPHANTINE.v))
- Satisfiability of elementary Diophantine constraints of the form `x = 1`, `x = y + z` or `x = y · z` (`H10C_SAT` in [`DiophantineConstraints/H10C.v`](theories/DiophantineConstraints/H10C.v)), **`good seed`**
- Satisfiability of uniform Diophantine constraints of the form `x = 1 + y + z · z` (`H10UC_SAT` in [`DiophantineConstraints/H10C.v`](theories/DiophantineConstraints/H10C.v)), **`good seed`**
- One counter machine halting problem (`CM1c4_HALT` in [`CounterMachines/CM1.v`](theories/CounterMachines/CM1.v)), **`good seed`**
- Provability in Hilbert-style calculi (`HSC_PRV` in [`HilbertCalculi/HSC.v`](theories/HilbertCalculi/HSC.v))
- Recognizing axiomatizations of Hilbert-style calculi (`HSC_AX` in [`HilbertCalculi/HSC.v`](theories/HilbertCalculi/HSC.v))
- Solvability of linear polynomial (over N) constraints of the form `x = 1`, `x = y + z`, `x = X · y` (`LPolyNC_SAT` in [`PolynomialConstraints/LPolyNC.v`](theories/PolynomialConstraints/LPolyNC.v))
- Finite multiset constraint solvability (`FMsetC_SAT` in [`SetConstraints/FMsetC.v`](theories/SetConstraints/FMsetC.v)), **`good seed`**
- Uniform boundedness of deterministic, length-preserving stack machines (`SMNdl_UB` in [`StackMachines/SMN.v`](theories/StackMachines/SMN.v))
- Semi-unification (`SemiU` in [`SemiUnification/SemiU.v`](theories/SemiUnification/SemiU.v))
- System F Inhabitation (`SysF_INH` in [`SystemF/SysF.v`](theories/SystemF/SysF.v)), System F Typability (`SysF_TYP` in [`SystemF/SysF.v`](theories/SystemF/SysF.v)), System F Type Checking (`SysF_TC` in [`SystemF/SysF.v`](theories/SystemF/SysF.v))

## How to build

If you can use `opam 2` on your system, you can follow the instructions here.
If you cannot use `opam 2`, you can use the `noopam` branch of this repository, which has no dependencies, but less available problems.

### Install from opam

We recommend creating a fresh opam switch:

```
opam switch create coq-library-undecidability 4.09.1+flambda
eval $(opam env)
```

Then the following commands install the library:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add psl-opam-repository https://github.com/uds-psl/psl-opam-repository.git
opam install coq-library-undecidability.dev+8.12
```

### Manual installation

You need `Coq 8.12` built on OCAML `>= 4.07.1`, the [Smpl](https://github.com/uds-psl/smpl) package, the [PSL Base](https://github.com/uds-psl/base-library) library, the [Equations](https://mattam82.github.io/Coq-Equations/) package, and the [MetaCoq](https://metacoq.github.io/metacoq/) package for Coq. If you are using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add psl-opam-repository https://github.com/uds-psl/psl-opam-repository.git
opam install . --deps-only
```

### Building the undecidability library

- `make all` builds the library
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory

### Troubleshooting

#### Windows

If you use Visual Studio Code on Windows 10 with Windows Subsystem for Linux (WSL), then local opam switches may cause issues.
To avoid this, you can use a non-local opam switch, i.e. `opam switch create 4.07.1+flambda`.

#### Coq version

Be careful that this branch only compiles under Coq 8.12. If you want to use a different Coq version you have to change to a different branch.
Due to compatibility issues, not every branch contains exactly the same problems. 
We recommend to use the newest branch if possible.


## Published work and technical reports

### Papers and abstracts on the library

A Coq Library of Undecidable Problems. Yannick Forster, Dominique Larchey-Wendling, Andrej Dudenhefner, Edith Heiter, Dominik Kirst, Fabian Kunze, Gert Smolka, Simon Spies, Dominik Wehr, Maximilian Wuttke. CoqPL '20. https://popl20.sigplan.org/details/CoqPL-2020-papers/5/A-Coq-Library-of-Undecidable-Problems

### Papers and abstracts on problems and proofs included in the library

- Trakhtenbrot's Theorem in Coq - A Constructive Approach to Finite Model Theory. Dominik Kirst and Dominique Larchey-Wendkling. IJCAR 2020. Subdirectory `TRAKTHENBROT`. https://www.ps.uni-saarland.de/extras/fol-trakh/
- Undecidability of Semi-Unification on a Napkin. Andrej Dudenhefner. FSCD 2020. Subdirectory `SUP`. https://www.ps.uni-saarland.de/Publications/documents/Dudenhefner_2020_Semi-unification.pdf
- Undecidability of Higher-Order Unification Formalised in Coq. Simon Spies and Yannick Forster. Technical report. Subdirectory `HOU`. https://www.ps.uni-saarland.de/Publications/details/SpiesForster:2019:UndecidabilityHOU.html
- Verified Programming of Turing Machines in Coq. Yannick Forster, Fabian Kunze, Maximilian Wuttke. Technical report. Subdirectory `TM`. https://github.com/uds-psl/tm-verification-framework/
- Hilbert's Tenth Problem in Coq. Dominique Larchey-Wendling and Yannick Forster. FSCD '19. Subdirectory `H10`. https://uds-psl.github.io/H10
- A certifying extraction with time bounds from Coq to call-by-value lambda-calculus. ITP '19. Subdirectory `L`. https://github.com/uds-psl/certifying-extraction-with-time-bounds
- Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. Subdirectory `ILL`. http://uds-psl.github.io/ill-undecidability/
- On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem. Yannick Forster, Dominik Kirst, and Gert Smolka. CPP '19. Subdirectory `FOL`. https://www.ps.uni-saarland.de/extras/fol-undec
- Formal Small-step Verification of a Call-by-value Lambda Calculus Machine. Fabian Kunze, Gert Smolka, and Yannick Forster. APLAS 2018. Subdirectory `L/AbstractMachines`. https://www.ps.uni-saarland.de/extras/cbvlcm2/
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
- Andrej Dudenhefner

