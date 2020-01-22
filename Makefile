.PHONY : all coq html website clean

all: coq html website

html:
	$(MAKE) -C theories html

coq:
	$(MAKE) -C theories

website:
	$(MAKE) -C theories html
	mv theories/html/*html website
	rm -rf theories/html

clean:
	$(MAKE) -C theories clean
	rm -f website/*html
