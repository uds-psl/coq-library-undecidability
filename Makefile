all:
	+make -C coq-library-undecidability deps
	+make -C coq-library-undecidability all
	+make -C theories html
