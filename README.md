# Specific Instructions regarding the "Hilbert Tenth problem in Coq" Paper

The code accompanying this paper is part of the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability)
in the branch [`coq-8.13`](https://github.com/uds-psl/coq-library-undecidability/tree/coq-8.13), library which depends on some external packages
([Equations](https://mattam82.github.io/Coq-Equations/) and [MetaCoq](https://metacoq.github.io/metacoq/)). Therefore it is necessary to 
clone and checkout this release and install the whole library following the [__Manual installation__](#manual-installation) instructions 
below. 

However, to _save some time_, the final build with `make all` can be replaced by the command

- `cd theories` 

followed by either:

- `make H10/summary.vo` to only compile the files relevant for the paper. The `summary.v` file gives
   a high-level view of all the many-one reductions described in the paper together with pointers
   to the relevant definitions;
- `make H10/standalone.vo` which imports `summary.vo` but moreover contains a _standalone statement_ 
   (preceded with all the relevant definitions) for the many-one reduction from `BPCP` to `H10nat`:
   * `BPCP`: the _Post correspondence problem_ for Boolean strings;
   * `H10nat`: solvability of single polynomial equation over natural numbers.

Both of these commands should take considerably less time than the >30min necessary for the full build of the library.

Notice that the files [`H10/summary.v`](theories/H10/summary.v) and [`H10/standalone.v`](theories/H10/standalone.v)
are specific to this release and are not included in the `coq-8.13` branch of the Coq Library of Undecidability Proofs.

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
opam install coq-library-undecidability.1.0.0+8.13
```

### Manual installation

You need `Coq 8.13` built on OCAML `>= 4.07.1`, the [Smpl](https://github.com/uds-psl/smpl) package, the [Equations](https://mattam82.github.io/Coq-Equations/) package, and the [MetaCoq](https://metacoq.github.io/metacoq/) package for Coq. If you are using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
```

### Building the undecidability library

- `make all` builds the library
- `make TM/TM.vo` compiles only the file `theories/TM/TM.v` and its dependencies
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory

#### Compiled interfaces

The library is compatible with Coq's compiled interfaces ([`vos`](https://coq.inria.fr/refman/practical-tools/coq-commands.html#compiled-interfaces-produced-using-vos)) for quick infrastructural access.

- `make vos` builds compiled interfaces for the library
- `make vok` checks correctness of the library 

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

- Trakhtenbrot's Theorem in Coq - A Constructive Approach to Finite Model Theory. Dominik Kirst and Dominique Larchey-Wendling. IJCAR 2020. Subdirectory `TRAKTHENBROT`. https://www.ps.uni-saarland.de/extras/fol-trakh/
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
