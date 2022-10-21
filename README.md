# Coq Library of Undecidability Proofs

[![CI](https://github.com/uds-psl/coq-library-undecidability/workflows/CI/badge.svg?branch=coq-8.16)](https://github.com/uds-psl/coq-library-undecidability/actions)

The Coq Library of Undecidability Proofs contains mechanised reductions to establish undecidability results in Coq.
The undecidability proofs are based on a synthetic approach to undecidability. 
A problem `P` is considered [undecidable](theories/Synthetic/Undecidability.v#L25) if its [decidability](theories/Synthetic/Definitions.v#L15) in Coq implies the [enumerability](theories/Synthetic/Definitions.v#L24) of the complement of halting problem for Turing machines (`SBTM_HALT` in [`TM/SBTM.v`](theories/TM/SBTM.v)).
Since the Turing machine halting is enumerable (`SBTM_HALT_enum` in [`TM/SBTM_enum.v`](theories/TM/SBTM_enum.v)), enumerability of its complement would classically imply its decidability.

As in the traditional literature, undecidability of a problem `P` in the library is often established by constructing a [many-one reduction](theories/Synthetic/Definitions.v#L40) from an undecidable problem to `P`.

For more information on the structure of the library, the synthetic approach, and included problems see [Publications](#publications) below, our [Wiki](https://github.com/uds-psl/coq-library-undecidability/wiki), look at the [slides](https://www.ps.uni-saarland.de/~forster/downloads/slides_coqpl20.pdf) or the [recording](https://www.youtube.com/watch?v=mo_C6664n3E) of the talk on the Coq Library of Undecidability proofs at [CoqPL '20](https://popl20.sigplan.org/details/CoqPL-2020-papers/5/A-Coq-Library-of-Undecidable-Problems).

The library is a collaborative effort, growing constantly and we invite everybody to contribute undecidability proofs!

## Problems in the Library

The problems in the library can mostly be categorized into seed problems, advanced problems, and target problems.

Seed problems are simple to state and thus make for good starting points of undecidability proofs, often leading to easier reductions to other problems.

Advanced problems do not work well as seeds, but they highlight the potential of our library as a framework for mechanically checking pen&paper proofs of potentially hard undecidability results.
Some advanced problems are proven decidable to contrast negative results.

Target problems are very expressive and thus work well as targets for reduction, with the aim of closing loops in the reduction graph to establish the inter-reducibility of problems.

### Seed Problems

- Halting problem for single-tape two-symbol Turing machines (`SBTM_HALT` in [`TM/SBTM.v`](theories/TM/SBTM.v))
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

- Halting problem for the weak call-by-value lambda-calculus (`HaltL` in [`L/L.v`](theories/L/L.v))
- Halting problem for multi-tape Turing machines (`HaltMTM` in [`TM/TM.v`](theories/TM/TM.v))
- Halting problem for single-tape Turing machines (`HaltTM 1` in [`TM/TM.v`](theories/TM/TM.v))
- Halting problem for simple binary single-tape Turing machines (`HaltSBTM` in [`TM/SBTM.v`](theories/TM/SBTM.v))
- Halting problem for program counter based binary single-tape Turing machines (`PCTM_HALT` in [`TM/PCTM.v`](theories/TM/PCTM.v))
- Halting problem for Binary Stack Machines (`BSM_HALTING` in [`StackMachines/BSM.v`](theories/StackMachines/BSM.v))
- Halting problems for Minsky machines (`MM_HALTING` and `MMA_HALTING n` in [`MinskyMachines/MM.v`](theories/MinskyMachines/MM.v))
- Halting problem for partial recursive functions (`MUREC_HALTING` in [`MuRec/recalg.v`](theories/MuRec/recalg.v))
- Halting problem for the weak call-by-name lambda-calculus (`wCBN` in [`LambdaCalculus/wCBN.v`](theories/LambdaCalculus/wCBN.v))

An equivalence proof that most of the mentioned models of computation compute the same `n`-ary functional relations over natural numbers is available in [`Models_Equivalent.v`](theories/Synthetic/Models_Equivalent.v).

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
- Validity and satisfiability in Second-Order Peano Arithmetic ([`SOL/PA2.v`](theories/SOL/PA2.v))
- Validity and satisfiability in Second-Order Logic in the empty signature ([`SOL/SOL.v`](theories/SOL/SOL.v))

#### Other Problems

- Acceptance problem for two counters non-deterministic Minsky machines (`ndMM2_ACCEPT` in [`MinskyMachines/ndMM2.v`](theories/MinskyMachines/ndMM2.v))
- String rewriting in Semi-Thue and Thue-systems (`SR` and `TSR` in [`StringRewriting/SR.v`](theories/StringRewriting/SR.v))
- String rewriting in Post canonical systems in normal form (`PCSnf` in [`StringRewriting/PCSnf.v`](theories/StringRewriting/PCSnf.v))
- Hilbert's 10th problem, i.e. solvability of a single diophantine equation (`H10` in [`H10/H10.v`](theories/H10/H10.v))
- Solvability of linear polynomial (over N) constraints of the form `x = 1`, `x = y + z`, `x = X · y` (`LPolyNC_SAT` in [`PolynomialConstraints/LPolyNC.v`](theories/PolynomialConstraints/LPolyNC.v))
- One counter machine halting problem (`CM1_HALT` in [`CounterMachines/CM1.v`](theories/CounterMachines/CM1.v))
- Finite multiset constraint solvability (`FMsetC_SAT` in [`SetConstraints/FMsetC.v`](theories/SetConstraints/FMsetC.v))
- Uniform boundedness of deterministic, length-preserving stack machines (`SMNdl_UB` in [`StackMachines/SMN.v`](theories/StackMachines/SMN.v))
- Semi-unification (`SemiU` in [`SemiUnification/SemiU.v`](theories/SemiUnification/SemiU.v))
- System F Inhabitation (`SysF_INH` in [`SystemF/SysF.v`](theories/SystemF/SysF.v)), System F Typability (`SysF_TYP` in [`SystemF/SysF.v`](theories/SystemF/SysF.v)), System F Type Checking (`SysF_TC` in [`SystemF/SysF.v`](theories/SystemF/SysF.v))
- Halting problem for Krivine machines (`KrivineM_HALT` in [`LambdaCalculus/Krivine.v`](theories/LambdaCalculus/Krivine.v))

#### Decidable Problems

- Two-counter Minsky Program Machine Halting (`MPM2_HALT` in [`MinskyMachines/Deciders/MPM2_HALT_dec.v`](theories/MinskyMachines/Deciders/MPM2_HALT_dec.v))<br/>
  The definition follows exactly Minsky[^1] (Chapter 11, Table 11.1-1), and is different from `MM2_HALTING` in [`MinskyMachines/MM2.v`](theories/MinskyMachines/MM2.v).
- Reversible Two-counter Machine Halting (`MM2_REV_HALT` in [`MinskyMachines/MM2.v`](theories/MinskyMachines/MM2.v))
- Two-counter Machine Uniform Mortality (`MM2_UMORTAL` in [`MinskyMachines/MM2.v`](theories/MinskyMachines/MM2.v))
- Two-counter Machine Uniform Boundedness (`MM2_UBOUNDED` in [`MinskyMachines/MM2.v`](theories/MinskyMachines/MM2.v))

### Target Problems

- Halting problem for the call-by-value lambda-calculus (`HaltL` in [`L/L.v`](theories/L/L.v))
- Validity, provability, and satisfiability in First-Order Logic (all problems in [`FOL/FOL.v`](theories/FOL/FOL.v))

## Installation Instructions

If you can use `opam 2` on your system, you can follow the instructions here.

### Install from released package via opam

*This installation method only works if the `opam` package is already released. Make sure you have done `opam update` and check the output of `opam info coq-library-undecidability` to see whether a package is available. If no package is available, use one of the two methods below.*

We recommend creating a fresh opam switch:

```
opam switch create coq-library-undecidability 4.09.1+flambda
eval $(opam env)
```

Then the following commands install the library:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-library-undecidability.1.0.1+8.16
```

### Install from git via opam

You can use `opam` to install the current state of this branch as follows.

We recommend creating a fresh opam switch:

```
opam switch create coq-library-undecidability --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
```

Then the following commands install the library:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam pin add coq-library-undecidability.dev+8.16 "https://github.com/uds-psl/coq-library-undecidability.git#coq-8.16"
```

### Manual installation (TENTATIVE)

You need `Coq 8.16` built on OCAML `>= 4.09.1`, and the Template-Coq (part of [MetaCoq](https://metacoq.github.io/)) package for Coq. If you are using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
opam install coq.8.16.dev
opam pin add -k git coq-equations.1.3+8.16 "https://github.com/mattam82/Coq-Equations.git#8.16"
```

#### Building the undecidability library

- `make all` builds the library
- `make TM/TM.vo` compiles only the file `theories/TM/TM.v` and its dependencies
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory

#### Compiled interfaces

The library is compatible with Coq's compiled interfaces ([`vos`](https://coq.inria.fr/refman/practical-tools/coq-commands.html#compiled-interfaces-produced-using-vos)) for quick infrastructural access.

- `make vos` builds compiled interfaces for the library
- `make vok` checks correctness of the library 

### Troubleshooting

#### Coq version

Be careful that this branch only compiles under `Coq 8.16`. If you want to use a different Coq version you have to change to a different branch.
Due to compatibility issues, not every branch contains exactly the same problems. 
We recommend to use the newest branch if possible.

## Publications

### Papers and abstracts on the library

A Coq Library of Undecidable Problems. Yannick Forster, Dominique Larchey-Wendling, Andrej Dudenhefner, Edith Heiter, Dominik Kirst, Fabian Kunze, Gert Smolka, Simon Spies, Dominik Wehr, Maximilian Wuttke. CoqPL '20. https://popl20.sigplan.org/details/CoqPL-2020-papers/5/A-Coq-Library-of-Undecidable-Problems

Computability in Constructive Type Theory. Yannick Forster. PhD thesis. https://dx.doi.org/10.22028/D291-35758

### Papers and abstracts on problems and proofs included in the library

- Certified Decision Procedures for Two-Counter Machines. Andrej Dudenhefner. FSCD 2022. Subdirectory `MinskyMachines/Deciders`. https://drops.dagstuhl.de/opus/volltexte/2022/16297/
- Constructive Many-One Reduction from the Halting Problem to Semi-Unification. Andrej Dudenhefner. CSL 2022. Subdirectory `SemiUnification`. https://drops.dagstuhl.de/opus/volltexte/2022/15738/
- Undecidability, Incompleteness, and Completeness of Second-Order Logic in Coq. Mark Koch and Dominik Kirst. CPP 2022. Subdirectory `SOL`. https://www.ps.uni-saarland.de/extras/cpp22-sol/
- A Mechanised Proof of the Time Invariance Thesis for the Weak Call-By-Value λ-Calculus. Yannick Foster, Fabian Kunze, Gert Smolka, Maximilian Wuttke. ITP 2021. Subdirectory `TM/L`. https://drops.dagstuhl.de/opus/volltexte/2021/13914/
- Synthetic Undecidability of MSELL via FRACTRAN. Dominique Larchey-Wendling. FSCD 2021. File [`ILL/IMSELL.v`](theories/ILL/IMSELL.v). Also documents 
 the undecidability proof for 2-counters Minsky machines [`MinskyMachines/MM2.v`](theories/MinskyMachines/MM2.v) via FRACTRAN. https://github.com/uds-psl/coq-library-undecidability/releases/tag/FSCD-2021/ 
- The Undecidability of System F Typability and Type Checking for Reductionists. Andrej Dudenhefner. LICS 2021. Subdirectory `SystemF`. https://ieeexplore.ieee.org/document/9470520
- Trakhtenbrot's Theorem in Coq - A Constructive Approach to Finite Model Theory. Dominik Kirst and Dominique Larchey-Wendling. IJCAR 2020. Subdirectory `TRAKTHENBROT`. https://www.ps.uni-saarland.de/extras/fol-trakh/
- Undecidability of Semi-Unification on a Napkin. Andrej Dudenhefner. FSCD 2020. Subdirectory `SemiUnification`. https://www.ps.uni-saarland.de/Publications/documents/Dudenhefner_2020_Semi-unification.pdf
- Mechanized Undecidability Results for Propositional Calculi. TYPES 2020. Subdirectory `HilbertCalculi`. https://types2020.di.unito.it/abstracts/BookOfAbstractsTYPES2020.pdf#page=94
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
- Johannes Hostert
- Dominik Kirst 
- Mark Koch
- Fabian Kunze
- Gert Smolka
- Simon Spies
- Dominik Wehr
- Maximilian Wuttke

Parts of the Coq Library of Undecidability Proofs reuse generic code initially developed as a library for the lecture ["Introduction to Computational Logics"](https://courses.ps.uni-saarland.de/icl_16/) at [Saarland University](https://www.uni-saarland.de/nc/en/home.html), which was written by a subset of the above contributors, Sigurd Schneider, and Jan Christian Menz.

[^1]: Minsky, Marvin Lee. Computation. Englewood Cliffs: Prentice-Hall, 1967.
