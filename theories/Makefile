all: Makefile.rocq
	export TIMED
	@+$(MAKE) -f Makefile.rocq all

html: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq html
	mv html/*.html ../website
	rm -rf html

clean: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq clean
	rm -f Makefile.rocq Makefile.rocq.conf

gitclean: 
	git clean -Xfd

findclean: 
	find \( -name "*.aux" -o -name "*.vo*" -o -name "*.glob" \) -exec rm -f {} \;

mrproper: clean gitclean findclean

Makefile.rocq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.rocq

force _CoqProject Makefile: ;

%: Makefile.rocq force
	@+$(MAKE) -f Makefile.rocq $@

.PHONY: all html clean force
