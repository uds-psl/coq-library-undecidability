TOPTARGETS := all clean

SUBDIRSW := $(wildcard */.)
SUBDIRS := $(filter-out website/. , $(SUBDIRSW))

all: $(SUBDIRS)

clean: $(SUBDIRS)
	rm -f website/*.html

html: $(SUBDIRS)
	mv */html/*.html website
	rm -rf */html

$(SUBDIRS):
	$(MAKE) -C $@ $(MAKECMDGOALS)

.PHONY: all clean html $(SUBDIRS)
