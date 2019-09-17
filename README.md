# Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory

Yannick Forster <forster@ps.uni-saarland>, Dominik Kirst <kirst@ps.uni-saarland.de>, Dominik Wehr <s8dowehr@stud.uni-saarland.de>

This is the Coq formalisation of the paper ["Completeness Theorems for First-Order Logic Analysed in Constructive Type Theory"](https://www.ps.uni-saarland.de/extras/fol-undec/).

## How to compile the code

You can simply type `make`.

The files are tested to compile with

``` shell
The Coq Proof Assistant, version 8.8.2 (March 2019)
compiled on Mar 19 2019 10:40:28 with OCaml 4.07.0
```
and the [Equations package](https://github.com/mattam82/Coq-Equations) version

``` shell
coq-equations 1.2~beta2+8.8

```

To install this dependencies, it is easiest to use `opam`:

``` shell
opam switch create coq.8.8.2 4.07.0
opam pin add coq 8.8.2
opam pin add coq-equations 1.2~beta2+8.8
```
