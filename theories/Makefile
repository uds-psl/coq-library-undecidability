all: Makefile.coq
	export TIMED
	$(MAKE) -f Makefile.coq all

html: Makefile.coq
	$(MAKE) -f Makefile.coq html
	mv html/*.html ../website
	rm -rf html

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

vok: Makefile.coq
	$(MAKE) -f Makefile.coq vok
	
vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos
	
uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq


.PHONY: all html clean

dummy:

%.vo: Makefile.coq dummy
	$(MAKE) -f Makefile.coq $@
