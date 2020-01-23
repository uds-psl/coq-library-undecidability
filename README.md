# Trakhtenbrot's Theorem in Coq

Dominik Kirst <kirst@ps.uni-saarland.de>, Dominique Larchey-Wendling <dominique.larchey-wendling@loria.fr>,

This repository contains the Coq formalisation of the paper 
["Trakhtenbrot's Theorem in Coq"](http://www.loria.fr/~larchey/papers/trakhtenbrot.pdf), submitted at the
International Joint Conference on Automated Reasoning (IJCAR 2020).

## How to compile the code

In the directory containing this `README.md` file, type `make all`. Compilation time should be arround 1 minute.
The files are tested to compile with `The Coq Proof Assistant, version 8.9.1 (October 2019)`. Compilation
has also been tested and should work with version `8.8.2`, `8.10.1`.

The compiled HTML version of the files can be found [here](http://www.ps.uni-saarland.de/extras/fol-trakh/website/toc.html) 
or in the [`website`](website) subdirectory of this repository.

For actually running the code after a full compilation, we advice consulting first the [`summary`](theories/TRAKHTENBROT/summary.v)
file that list all the main results presented in the paper.

# A Coq library of undecidable problems

This repo is static and stripped version of a development branch of the 
[library of undecidable problems](https://github.com/uds-psl/coq-library-undecidability) 
together with the html version of the code.

