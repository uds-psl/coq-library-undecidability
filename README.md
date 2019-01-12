# A library of formalised undecidable problems in Coq

This library contains undecidable problems and formalised reductions between them.
Feel free to contribute or start using the problems!

## Existing undecidable problems

- Post correspondence problem (`PCP` in `Problems/PCP.v`)
- Halting problem for Turing machines (`Halt` in `Problems/TM.v`)
- Halting problem for Minsky machines (`MM_HALTING` in `Problems/MM.v`)
- Halting problem for binary stack machines (`BSM_HALTING` in `Problems/BSM.v`)
- Halting problem for the call-by-value lambda-calculus (`eva` in `Problems/L.v`)
- String rewriting (`SR` in `Problems/SR.v`)
- Entailment in elementary intuitionistic linear logic (`EILL_PROVABILITY` in `Problems/ILL.v`)
- Entailment in intuitionistic linear logic (`ILL_PROVABILITY` in `Problems/ILL.v`)
- Provability in minimal (intuitionistic, classical) first-order logic (`prv` in `Problems/FOL.v`)
- Validity in minimal (intuitionistic, classical) first-order logic (`valid` in `Problems/FOL.v`, `kvalid` in `Problems/FOL.v`)
- Satisfiability in intuitionistic (classical) first-order logic (`satis` in `Problems/FOL.v`, `ksatis` in `Problems/FOL.v`)

## How to build

- the subprojects are currently in subdirectories, roughly corresponding to papers or theses covering them
- `make all` builds all subprojects by calling `make all` of the corresponding subproject's makefile
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files and `.html` files
- the `gh-pages` branch contains a snapshot of the `html` files and this `README` file and is accessible under `uds-psl.github.io/coq-library-undecidability`

## Published work

- Verification of PCP-Related Computational Reductions in Coq. Yannick Forster, Edith Heiter, and Gert Smolka. ITP 2018. Subdirectory `PCP`. https://ps.uni-saarland.de/extras/PCP 
- Towards a library of formalised undecidable problems in Coq: The undecidability of intuitionistic linear logic. Yannick Forster and Dominique Larchey-Wendling. LOLA 2018. Subdirectory `ILL`. https://www.ps.uni-saarland.de/~forster/downloads/LOLA-2018-coq-library-undecidability.pdf 
-  Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines. Yannick Forster and Dominique Larchey-Wendling. CPP '19. Subdirectory `ILL`. http://uds-psl.github.io/ill-undecidability/
-  On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem. Yannick Forster, Dominik Kirst, and Gert Smolka. CPP '19. Subdirectory `FOL`. https://www.ps.uni-saarland.de/extras/fol-undec
- Call-by-Value Lambda Calculus as a Model of Computation in Coq. Yannick Forster and Gert Smolka. Journal of Automated Reasoning (2018). https://www.ps.uni-saarland.de/extras/L-computability/

## How to contribute

- Fork the repository using the `Fork` button.
- Create a new subdirectory for your project and add your files.
- Add a license for your project.
- Edit the "Existing undecidable problems" and the "Contributors" section in this file
- File a pull request.

## Contributors

- Yannick Forster (@yforster)
- Edith Heiter
- Dominik Kirst (@dominik-kirst)
- Dominique Larchey-Wendling (@DmxLarchey)
- Gert Smolka
