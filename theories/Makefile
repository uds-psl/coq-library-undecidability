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

gitclean: 
	git clean -Xfd

findclean: 
	find \( -name "*.aux" -o -name "*.vo*" -o -name "*.glob" \) -exec rm -f {} \;

mrproper: clean gitclean findclean

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all html clean force
