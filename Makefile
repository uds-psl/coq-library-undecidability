all:
	export TIMED
	@+$(MAKE) -C theories all

force Makefile: ;

%: force
	@+$(MAKE) -C theories $@

deploy:
	rsync -r website/ forster@alfred.ps.uni-saarland.de:~/public_html/thesis/library-coq/

.PHONY: all force
