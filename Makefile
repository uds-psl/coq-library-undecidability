all:
	+make -C theories all

install:
	+make -C theories install

clean:
	+make -C theories clean

html:
	+make -C theories html

.PHONY: all install html clean 
