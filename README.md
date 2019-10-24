# A library of formalised undecidable problems in Coq

[![Build Status](https://travis-ci.org/uds-psl/coq-library-undecidability.svg?branch=noopam)](https://travis-ci.org/uds-psl/coq-library-undecidability)

This library contains undecidable problems and formalised reductions between them.
Feel free to contribute or start using the problems!

This is the `noopam` branch of the library which you should *only* use if you absolutely can't use `opam 2` on your system.
Some undecidable problems might not be available on this branch, because they rely on opam packages.

See the `master` branch for an overview of problems in the library, a contribution guide and other information.

## How to build the `noopam` branch

You need to have Coq `8.8.1`, `8.8.2` or `8.9.1`. You don't need any external libraries or tools.

- `make all` builds the library
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files and `.html` files
