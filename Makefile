all:
	+git submodule update --init --recursive
	+make -C coq-library-undecidability deps
	+make -C coq-library-undecidability all -j 5
	+make -C theories html
