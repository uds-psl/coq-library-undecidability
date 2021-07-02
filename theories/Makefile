all: Makefile.coq
	export TIMED
	@+$(MAKE) -f Makefile.coq all

html: Makefile.coq
	@+$(MAKE) -f Makefile.coq html
	mv html/*.html ../website
	rm -rf html

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject 
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: force
	yes | cp _CoqProject.in _CoqProject
	git ls-files "*.v" >> _CoqProject

force _CoqProject.in Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all html clean force
