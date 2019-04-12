all:
	+make -C external all
	+make -C theories all

clean:
	+make -C theories clean

realclean:
	+make -C external clean
	+make -C theories clean

html:
	+make -C theories website

.PHONY: all html clean realclean
