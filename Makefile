all:
	+make -C theories all

clean:
	+make -C theories clean

html:
	+make -C theories website

.PHONY: all html clean 
