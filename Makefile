all:
	export TIMED
	@+$(MAKE) -C theories all

force Makefile: ;

%: force
	@+$(MAKE) -C theories $@

.PHONY: all force