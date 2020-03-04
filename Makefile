
all:
	+make -C theories all

deps:
	+make -C external all

clean:
	+make -C theories clean

realclean:
	+make -C external clean
	+make -C theories clean

html:
	+make -C theories html

.PHONY: all html clean realclean
