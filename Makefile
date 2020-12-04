all:
	export TIMED
	$(MAKE) -C theories all

install:
	$(MAKE) -C theories install

clean:
	$(MAKE) -C theories clean

html:
	$(MAKE) -C theories html

vok:
	$(MAKE) -C theories vok
	
vos:
	$(MAKE) -C theories vos
	
.PHONY: all install html clean 

dummy:

%.vo: dummy
	cd theories && $(MAKE) $@
