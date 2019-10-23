all:
	+make -C theories all

clean:
	+make -C theories clean
	rm -rf ./website/*.html

html:
	+make -C theories website

.PHONY: all html clean 
