# Proof Mode

This folder contains the first-order logic proof mode of our submission to the [2021 Coq Workshop](https://coq-workshop.gitlab.io/2021/), as well as the associated demo files.

## Building

For build instructions, see [the README for the whole libary](https://github.com/dominik-kirst/coq-library-undecidability/tree/coqws#manual-installation). Note that you must **not** follow the instructions for installing from OPAM, since the version published on OPAM does not include our additions. You have to build this library yourself.

In short, to build the proof mode, run the following in this repo's root folder:
```
opam switch create coq-library-undecidability-workshop21 4.07.1+flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
make FOL/Proofmode/ProofMode.vo
```

Note that lines 1-4 only have to be run once.

## Usage

The proof mode is invoked by calling the tactic `fstart`.
Details on the available tactics can be found in the [documentation](Manual.pdf).
It also explains the neccessary setup steps as well as implementation details.

## Overwiev

### `ProofMode.v`
This file contains all of the main implementation of the proof mode as well as all custom tactics. 

### `Hoas.v`
This file the higher order abstract syntax input language.

### `StringToIdent.v`
This file contains a MetaCoq plugin for converting strings into Coq identifiers.

### `Theories.v`
This file proves some facts that the proof mode requires to work with theories.
Note that theory support is still work in progress.

## Demos
All files starting with `Demo` are demo files, which demonstrate the proof mode.

### `DemoPA.v`
This file first showcases some general features of the proof mode on the signature of Peano Arithmetic.
The second part is a syntactic proof of an Euclidean division theorem using our HOAS input language.

### `DemoZF.v`

This file contains some basic proofs on the signature of Zermelo–Fraenkel set theory using the proof mode.

### `DemoMinZF.v`

This file benchmarks the proof mode against an [existing development](../Reductions/PCPb_to_minZF.v#527), verifying the translation to the minimal signature of ZF.
This hightlights that the proof mode allows for shorter and more readable proof scirpts.
