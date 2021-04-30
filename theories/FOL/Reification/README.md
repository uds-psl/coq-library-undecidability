# Reification

This folder contains the Reification tactics for our submission to the [2021 Coq Workshop](https://coq-workshop.gitlab.io/2021/), as well as the associated demo files.

## Building

For build instructions, see [the README for the whole libary](https://github.com/dominik-kirst/coq-library-undecidability/tree/coqws#manual-installation). Note that you must **not** follow the instructions for installing from OPAM, since the version published on OPAM does not include our additions. You have to build this library yourself.


## Usage

The main tactic you will want to use is `represent`. It can be invoked on goals like `representableP n P`.

Before you can use the tactic, you must define an instance of `tarski_reflector`, which can easily be done using buildDefaultTarski.

A more detailed documentation can be found [here](https://example.org). This document explains the internal operations of the reification engine, all tactics, and the extension point mechanism. It also contains hints and common mistakes one should avoid.

## Demos
All files starting with `Demo` are demo files, which demonstrate the reification tactic.
### `DemoPA.v`
This file proves some facts about Peano Arithmetic, including the commutativiy of `+` and `*`. Specifically, we prove that these hold in all models of PA. For this, we use our reification tactic to make induction easier.

### `DemoPAExtensional.v`
This file proves the same facts as `DemoPA.v`. However, here we assume a model where equality is extensional. This makes the actual proofs shorter, since we can use rewriting, however, we have to use the extension point mechanism to teach the reification engine how to handle equality.
