all:
	export TIMED
	$(MAKE) -C theories all

install:
	$(MAKE) -C theories install

clean:
	$(MAKE) -C theories clean

html:
	$(MAKE) -C theories html

.PHONY: all install html clean 

dummy:

%.vo: dummy
	cd theories && $(MAKE) $@
