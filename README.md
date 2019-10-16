# A library of formalised undecidable problems in Coq

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

### Required packages

You need `Coq 8.8.1`, `8.8.2` or `8.9.1` built on OCAML `> 4.02.3` and the [Equations](https://mattam82.github.io/Coq-Equations/) package for Coq. If you're using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam install . --deps-only
```

### Build external libraries

The Undecidability libraries depends on several external libraries. Initialise and build them once as follows:

``` sh
git submodule init
git submodule update
make deps
```

### Building the undecidability library

- `make all` builds the library
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory
- `make realclean` also removes all build files in the `external` directory. You have to run `make deps` again after this.

## Published work and technical reports

- Hilbert's Tenth Problem in Coq. Dominique Larchey-Wendling and Yannick Forster. Technical report. Subdirectory `H10`. https://uds-psl.github.io/H10
- A certifying extraction with time bounds from Coq to call-by-value lambda-calculus. Technical report. Subdirectory `L`. https://github.com/uds-psl/certifying-extraction-with-time-bounds
- Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. Subdirectory `ILL`. http://uds-psl.github.io/ill-undecidability/
- On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem. Yannick Forster, Dominik Kirst, and Gert Smolka. CPP '19. Subdirectory `FOL`. https://www.ps.uni-saarland.de/extras/fol-undec
-  Formal Small-step Verification of a Call-by-value Lambda Calculus Machine. Fabian Kunze, Gert Smolka, and Yannick Forster. APLAS 2018. Subdirectory `LAM`. https://www.ps.uni-saarland.de/extras/cbvlcm2/
- Towards a library of formalised undecidable problems in Coq: The undecidability of intuitionistic linear logic. Yannick Forster and Dominique Larchey-Wendling. LOLA 2018. Subdirectory `ILL`. https://www.ps.uni-saarland.de/~forster/downloads/LOLA-2018-coq-library-undecidability.pdf 
- Verification of PCP-Related Computational Reductions in Coq. Yannick Forster, Edith Heiter, and Gert Smolka. ITP 2018. Subdirectory `PCP`. https://ps.uni-saarland.de/extras/PCP 
- Call-by-Value Lambda Calculus as a Model of Computation in Coq. Yannick Forster and Gert Smolka. Journal of Automated Reasoning (2018) Subdirectory `L`. https://www.ps.uni-saarland.de/extras/L-computability/

## How to contribute

- Fork the project.
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
- Maximilian Wuttke

