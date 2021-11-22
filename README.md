# Specific Instructions regarding the "Trakhtenbrot's Theorem in Coq" Paper

The code accompanying this paper is part of the Coq Library of Undecidability Proofs and depends on some library files. Therefore it is necessary to clone and checkout this branch and install the whole library following the [__Manual installation__](#manual-installation) instructions below. However, to _save some time_, the final build with `make all` can be replaced by `make TRAKHTENBROT/summary.vo` from inside the `theories` folder to only compile the files relevant for the paper. This command should take less than 5min instead of >30min for the full build.

# Coq Library of Undecidability Proofs

[![CI](https://github.com/uds-psl/coq-library-undecidability/workflows/CI/badge.svg?branch=coq-8.13)](https://github.com/uds-psl/coq-library-undecidability/actions)

The Coq Library of Undecidability Proofs contains mechanised reductions to establish undecidability results in Coq.
The undecidability proofs are based on a synthetic approach to undecidability, where a problem `P` is considered [undecidable](theories/Synthetic/Undecidability.v#L4) if its [decidability](theories/Synthetic/Definitions.v#L6) in Coq would imply the decidability of the [halting problem of single-tape Turing machines](theories/TM/TM.v#L148) in Coq.
As in the traditional literature, undecidability of a problem `P` in the library is often established by constructing a [many-one reduction](theories/Synthetic/Definitions.v#L27) from an undecidable problem to `P`.

For more information on the structure of the library, the synthetic approach, and included problems see [Publications](#publications) below, our [Wiki](https://github.com/uds-psl/coq-library-undecidability/wiki), look at the [slides](https://www.ps.uni-saarland.de/~forster/downloads/slides_coqpl20.pdf) or the [recording](https://www.youtube.com/watch?v=mo_C6664n3E) of the talk on the Coq Library of Undecidability proofs at [CoqPL '20](https://popl20.sigplan.org/details/CoqPL-2020-papers/5/A-Coq-Library-of-Undecidable-Problems).

The library is a collaborative effort, growing constantly and we invite everybody to contribute undecidability proofs!

## Problems in the Library

The problems in the library can mostly be categorized into seed
problems, advanced problems, and target problems.

Seed problems are simple to state and thus make for good starting points of undecidability proofs, often leading to easier reductions to other problems.

Advanced problems do not work well as seeds, but they highlight the potential of our library as a framework for mechanically checking pen&paper proofs of potentially hard undecidability results.

Target problems are very expressive and thus work well as targets for reduction, with the aim of closing loops in the reduction graph to establish the inter-reducibility of problems.

### Seed Problems

- Post correspondence problem (`PCP` in [`PCP/PCP.v`](theories/PCP/PCP.v))
- Halting problem for two counters Minsky machines (`MM2_HALTING` in [`MinskyMachines/MM2.v`](theories/MinskyMachines/MM2.v)) 
- Halting problem for FRACTRAN programs (`FRACTRAN_REG_HALTING` in [`FRACTRAN/FRACTRAN.v`](theories/FRACTRAN/FRACTRAN.v))
- Satisfiability of elementary Diophantine constraints of the form `x = 1`, `x = y + z` or `x = y · z` (`H10C_SAT` in [`DiophantineConstraints/H10C.v`](theories/DiophantineConstraints/H10C.v))
- Satisfiability of uniform Diophantine constraints of the form `x = 1 + y + z · z` (`H10UC_SAT` in [`DiophantineConstraints/H10C.v`](theories/DiophantineConstraints/H10C.v))
- Halting problem for one counter machines (`CM1_HALT` in [`CounterMachines/CM1.v`](theories/CounterMachines/CM1.v))
- Solvability of finite multiset constraint  (`FMsetC_SAT` in [`SetConstraints/FMsetC.v`](theories/SetConstraints/FMsetC.v))
- Simple semi-Thue system 01 rewriting (`SSTS01` in [`StringRewriting/SSTS.v`](theories/StringRewriting/SSTS.v))

### Advanced Problems 

#### Halting Problems for Traditional Models of Computation

- Halting problem for the call-by-value lambda-calculus (`HaltL` in [`L/L.v`](theories/L/L.v))
- Halting problem for multi-tape Turing machines (`HaltMTM` in [`TM/TM.v`](theories/TM/TM.v))
- Halting problem for single-tape Turing machines (`HaltTM 1` in [`TM/TM.v`](theories/TM/TM.v))
- Halting problem for simple binary single-tape Turing machines (`HaltSBTM`) in [`TM/SBTM.v`](theories/TM/SBTM.v)
- Halting problem for Binary Stack Machines (`BSM_HALTING` in [`StackMachines/BSM.v`](theories/StackMachines/BSM.v))
- Halting problem for Minsky machines (`MM_HALTING` in [`MinskyMachines/MM.v`](theories/MinskyMachines/MM.v))
- Halting problem for partial recursive functions (`MUREC_HALTING` in [`MuRec/recalg.v`](theories/MuRec/recalg.v))

#### Problems from Logic

- Provability in Minimal, Intuitionistic, and Classical First-Order Logic (`FOL*_prv_intu`, `FOL_prv_intu`, `FOL_prv_class` in [`FOL/FOL.v`](theories/FOL/FOL.v)), including a formulation for the minimal binary signature ([`FOL/binFOL.v`](theories/FOL/binFOL.v))
- Validity in Minimal and Intuitionistic First-Order Logic (`FOL*_valid`, `FOL_valid_intu` in [`FOL/FOL.v`](theories/FOL/FOL.v))
- Satisfiability in Minimal and Intuitionistic First-Order Logic (`FOL*_satis`, `FOL_satis_intu` in [`FOL/FOL.v`](theories/FOL/FOL.v))
- Finite satisfiability in First-Order Logic, known as "Trakhtenbrot's theorem" (`FSAT` in [`FOL/FSAT.v`](theories/FOL/FSAT.v) based on [`TRAKHTENBROT/red_utils.v`](theories/TRAKHTENBROT/red_utils.v))
- Semantic and deductive entailment in first-order ZF set-theory with ([`FOL/ZF.v`](theories/FOL/ZF.v)) and without ([`FOL/minZF.v`](theories/FOL/minZF.v) and [`FOL/binZF.v`](theories/FOL/binZF.v)) function symbols for set operations
- Semantic and deductive entailment in Peano arithmetic ([`FOL/PA.v`](theories/FOL/PA.v))
- Entailment in Elementary Intuitionistic Linear Logic (`EILL_PROVABILITY` in [`ILL/EILL.v`](theories/ILL/EILL.v))
- Entailment in Intuitionistic Linear Logic (`ILL_PROVABILITY` in [`ILL/ILL.v`](theories/ILL/ILL.v))
- Entailment in Classical Linear Logic (`CLL_cf_PROVABILITY` in [`ILL/CLL.v`](theories/ILL/CLL.v))
- Entailment in Intuitionistic Multiplicative Sub-Exponential Linear Logic (`IMSELL_cf_PROVABILITY3` in [`ILL/IMSELL.v`](theories/ILL/IMSELL.v))
- Provability in Hilbert-style calculi (`HSC_PRV` in [`HilbertCalculi/HSC.v`](theories/HilbertCalculi/HSC.v))
- Recognizing axiomatizations of Hilbert-style calculi (`HSC_AX` in [`HilbertCalculi/HSC.v`](theories/HilbertCalculi/HSC.v))
- Satisfiability in Separation Logic (`SLSAT` in [SeparationLogic/SL.v](theories/SeparationLogic/SL.v) and `MSLSAT` in [SeparationLogic/MSL.v](theories/SeparationLogic/MSL.v))

#### Other Problems

- Acceptance problem for two counters non-deterministic Minsky machines (`ndMM2_ACCEPT` in [`MinskyMachines/ndMM2.v`](theories/MinskyMachines/ndMM2.v))
- String rewriting in Semi-Thue and Thue-systems (`SR` and `TSR` in [`StringRewriting/SR.v`](theories/StringRewriting/SR.v))
- String rewriting in Post canonical systems in normal form (`PCSnf` in [`StringRewriting/PCSnf.v`](theories/StringRewriting/PCSnf.v))
- Hilbert's 10th problem, i.e. solvability of a single diophantine equation (`H10` in [`H10/H10.v`](theories/H10/H10.v))
- Solvability of linear polynomial (over N) constraints of the form `x = 1`, `x = y + z`, `x = X · y` (`LPolyNC_SAT` in [`PolynomialConstraints/LPolyNC.v`](theories/PolynomialConstraints/LPolyNC.v))
- One counter machine halting problem (`CM1_HALT` in [`CounterMachines/CM1.v`](theories/CounterMachines/CM1.v)), 
- Finite multiset constraint solvability (`FMsetC_SAT` in [`SetConstraints/FMsetC.v`](theories/SetConstraints/FMsetC.v))
- Uniform boundedness of deterministic, length-preserving stack machines (`SMNdl_UB` in [`StackMachines/SMN.v`](theories/StackMachines/SMN.v))
- Semi-unification (`SemiU` in [`SemiUnification/SemiU.v`](theories/SemiUnification/SemiU.v))
- System F Inhabitation (`SysF_INH` in [`SystemF/SysF.v`](theories/SystemF/SysF.v)), System F Typability (`SysF_TYP` in [`SystemF/SysF.v`](theories/SystemF/SysF.v)), System F Type Checking (`SysF_TC` in [`SystemF/SysF.v`](theories/SystemF/SysF.v))

### Target Problems

- Halting problem for the call-by-value lambda-calculus (`HaltL` in [`L/L.v`](theories/L/L.v))
- Validity, provability, and satisfiability in First-Order Logic (all problems in [`FOL/FOL.v`](theories/FOL/FOL.v))

## Installation Instructions

You need [`opam 2`](https://opam.ocaml.org) on your system to be able to follow the instructions here.
You can follow the [instructions to install and compile](https://github.com/uds-psl/coq-library-undecidability/) the whole 
Coq library of Undecidability Proofs but we recommend the shorter manual installation instructions below, especially
since this tailored version compiles the [__summary file__](theories/TRAKHTENBROT/summary.v) while the standard 
installation avoids compiling it. Also the standard build takes much longer to compile.

### Manual installation

First, download the source code of the release as either [`TRAK-LMCS-v1.1.zip`](https://github.com/uds-psl/coq-library-undecidability/archive/refs/tags/TRAK-LMCS-v1.1.zip) or [`TRAK-LMCS-v1.1.tar.gz`](https://github.com/uds-psl/coq-library-undecidability/archive/refs/tags/TRAK-LMCS-v1.1.tar.gz). Unpack the
archive file and then `cd` to the unpacked new directory.

```
wget -c https://github.com/uds-psl/coq-library-undecidability/archive/refs/tags/TRAK-LMCS-v1.1.zip
unzip TRAK-LMCS-v1.1.zip
cd coq-library-undecidability-TRAK-LMCS-v1.1
```

You need `Coq 8.13` built on OCAML `>= 4.07.1`, the [Smpl](https://github.com/uds-psl/smpl) package, the [Equations](https://mattam82.github.io/Coq-Equations/) package, and the [MetaCoq](https://metacoq.github.io/metacoq/) package for Coq. With `opam 2`, you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
```

### Building the undecidability library

#### Relevant `make` commands

- `make TRAKHTENBROT/summary.vo` builds the review file `theories/TRAKHTENBROT/summary.v` for the Trakhtenbrot development (expect 2-4 minutes)
- `make all` builds the whole library (expect 30 minutes)
- `make TM/TM.vo` compiles only the file `theories/TM/TM.v` and its dependencies
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory

#### Compiled interfaces

The library is compatible with Coq's compiled interfaces ([`vos`](https://coq.inria.fr/refman/practical-tools/coq-commands.html#compiled-interfaces-produced-using-vos)) for quick infrastructural access.

- `make vos` builds compiled interfaces for the library
- `make vok` checks correctness of the library 

### Reviewing the Coq code

We recommend starting the code review by opening the file `theories/TRAKHTENBROT/summary.v`
using your favorite IDE, e.g. CoqIDE:

```
opam install coqide.8.13.1     ## if needed
cd theories
coqide TRAKHTENBROT/summary.v
```

Notice that it is __essential to compile__ this file __before reviewing__, using `make TRAKHTENBROT/summary.vo` as explained above, 
because this will compile all the library files on which the review `summary.v` file depends.

The file `summary.v` contains commented out `Print Assumptions` commands that
can be uncommented to check for that no axioms where used. 
Printing assumptions takes a big toll on the compilation time, 
which is why these commands are systematically commented out in the 
main Coq Undecidability library: it already takes 30 minutes to fully compile.

Notice that you can also just check for axiom-freeness on the
main results at the end of this file. This entails that intermediate
result are also free of axioms, i.e. the results `FULL_MONADIC`,
`FULL_MONADIC_discernable` and `FULL_TRAKHTENBROT`. For convenience,
these three are currently uncommented in the file of this tailored version.

### Troubleshooting

#### Windows

If you use Visual Studio Code on Windows 10 with Windows Subsystem for Linux (WSL), then local opam switches may cause issues.
To avoid this, you can use a non-local opam switch, i.e. `opam switch create 4.07.1+flambda`.

#### Coq version

Be careful that this branch only compiles under `Coq 8.13`. If you want to use a different Coq version you have to change to a different branch.
Due to compatibility issues, not every branch contains exactly the same problems. 
We recommend to use the newest branch if possible.

## Publications

### Papers and abstracts on the library

A Coq Library of Undecidable Problems. Yannick Forster, Dominique Larchey-Wendling, Andrej Dudenhefner, Edith Heiter, Dominik Kirst, Fabian Kunze, Gert Smolka, Simon Spies, Dominik Wehr, Maximilian Wuttke. CoqPL '20. https://popl20.sigplan.org/details/CoqPL-2020-papers/5/A-Coq-Library-of-Undecidable-Problems

### Papers and abstracts on problems and proofs included in the library

- Trakhtenbrot's Theorem in Coq - A Constructive Approach to Finite Model Theory. Dominik Kirst and Dominique Larchey-Wendling. IJCAR 2020. Subdirectory `TRAKHTENBROT`. https://www.ps.uni-saarland.de/extras/fol-trakh/
- Undecidability of Semi-Unification on a Napkin. Andrej Dudenhefner. FSCD 2020. Subdirectory `SemiUnification`. https://www.ps.uni-saarland.de/Publications/documents/Dudenhefner_2020_Semi-unification.pdf
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

Fork the project on GitHub, add a new subdirectory for your project and your files, then file a pull request.
We have [guidelines for the directory structure of projects](https://github.com/uds-psl/coq-library-undecidability/wiki/Structure-Guidelines).

## Contributors

- Yannick Forster
- Dominique Larchey-Wendling
- Andrej Dudenhefner
- Edith Heiter
- Marc Hermes
- Dominik Kirst 
- Fabian Kunze
- Gert Smolka
- Simon Spies
- Dominik Wehr
- Maximilian Wuttke

Parts of the Coq Library of Undecidability Proofs reuse generic code initially developed as a library for the lecture ["Introduction to Computational Logics"](https://courses.ps.uni-saarland.de/icl_16/) at [Saarland University](https://www.uni-saarland.de/nc/en/home.html), which was written by a subset of the above contributors, Sigurd Schneider, and Jan Christian Menz.
